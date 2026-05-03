use std::path::{Path, PathBuf};

use monad_core::term::module::{ParsedModule, default_modules};
use monad_core::term::{Decl, ModulePath};

use crate::codegen::compile_decls;
use crate::ir::LLVMModule;
use crate::runtime::RuntimeBuilder;

/// Output format for the final compiled artifact.
#[derive(Clone, Debug, PartialEq)]
pub enum OutputKind {
  /// Executable binary
  Executable,
  /// Shared object (.so)
  SharedObject,
}

/// Result of the compilation pipeline, containing paths to generated files.
#[derive(Clone, Debug)]
pub struct CompileResult {
  /// Path to the generated LLVM IR source file (.ll)
  pub ir_path: PathBuf,
  /// Path to the generated object file (.o)
  pub object_path: PathBuf,
  /// Path to the runtime object file (.o)
  pub runtime_object_path: PathBuf,
  /// Path to the final linked artifact
  pub output_path: PathBuf,
}

/// Configuration for the compilation pipeline.
#[derive(Clone, Debug)]
pub struct CompileOptions {
  /// Output directory for intermediate and final files.
  pub output_dir: PathBuf,
  /// Base name for output files (without extension).
  pub output_name: String,
  /// Kind of output to produce.
  pub output_kind: OutputKind,
  /// Whether to keep intermediate files after compilation.
  pub keep_intermediates: bool,
}

impl Default for CompileOptions {
  fn default() -> Self {
    CompileOptions {
      output_dir: PathBuf::from("."),
      output_name: "output".to_string(),
      output_kind: OutputKind::Executable,
      keep_intermediates: false,
    }
  }
}

/// Step 1: Parse a Monad source file and all required modules,
/// then generate LLVM IR.
///
/// This function:
/// 1. Loads default modules (prelude, io, etc.)
/// 2. Loads the input file and all its `use` dependencies
/// 3. Extracts all declarations from the loaded modules
/// 4. Compiles declarations to LLVM IR
pub fn compile_to_ir(input_path: &Path) -> Result<LLVMModule, String> {
  use monad_core::term::Term;

  let abs_path = input_path.canonicalize().map_err(|e| format!("{e}"))?;
  let module_path: ModulePath = abs_path.clone().into();
  let mut loaded = default_modules().map_err(|e| format!("{e}"))?;

  let text = std::fs::read_to_string(&abs_path)
    .map_err(|e| format!("Failed to read {}: {e}", abs_path.display()))?;
  let decls = monad_core::term::module::load_decls_from_text(&text)
    .map_err(|e| format!("Failed to parse {}: {e}", abs_path.display()))?;
  let decls = monad_core::eval::r#type::type_check_module_decls(&module_path, decls, &loaded)
    .map_err(|e| format!("Type check failed: {e}"))?;
  let module = monad_core::term::module::module(
    module_path.clone(),
    ParsedModule {
      decls,
      module_doc: None,
    },
  );
  loaded.add_module(module);

  let mut all_decls: Vec<Decl> = Vec::new();

  for mod_ref in loaded.modules() {
    for ctx in mod_ref.defs() {
      let def = ctx.value();
      let mut body = &def.term;
      while let Some((_, inner)) = body.as_lam() {
        body = inner;
      }
      if let Term::Ntv { native: _ } = body {
        all_decls.push(Decl::Def(def.clone()));
      }
    }
  }

  let input_module = loaded
    .get_module(&module_path)
    .ok_or_else(|| format!("Module {module_path} not loaded"))?;

  let input_decls: Vec<Decl> = input_module
    .clone()
    .to_decls()
    .into_iter()
    .map(|ctx| ctx.value().clone())
    .collect();
  all_decls.extend(input_decls);

  compile_decls(&all_decls)
}

/// Step 2: Write LLVM IR to a .ll file.
pub fn write_ir_file(module: &LLVMModule, path: &Path) -> Result<(), String> {
  let ir_source = module.emit();
  std::fs::write(path, &ir_source)
    .map_err(|e| format!("Failed to write IR file {}: {e}", path.display()))
}

/// Step 3: Compile LLVM IR to an object file using `llc`.
pub fn compile_ir_to_object(ir_path: &Path, object_path: &Path) -> Result<(), String> {
  let status = std::process::Command::new("llc")
    .arg("-filetype=obj")
    .arg(ir_path)
    .arg("-o")
    .arg(object_path)
    .status()
    .map_err(|e| format!("Failed to run llc: {e}"))?;

  if !status.success() {
    return Err(format!("llc failed with exit code {:?}", status.code()));
  }

  Ok(())
}

/// Step 4: Compile the C runtime to an object file.
/// Tries clang first, falls back to cc.
pub fn compile_runtime(object_path: &Path) -> Result<(), String> {
  let runtime_source = RuntimeBuilder::c_source();

  let c_path = object_path.with_extension("c");
  std::fs::write(&c_path, runtime_source)
    .map_err(|e| format!("Failed to write runtime source: {e}"))?;

  let compiler = find_c_compiler()?;

  let status = std::process::Command::new(&compiler)
    .arg("-c")
    .arg(&c_path)
    .arg("-o")
    .arg(object_path)
    .status()
    .map_err(|e| format!("Failed to run {compiler} for runtime: {e}"))?;

  if !status.success() {
    return Err(format!(
      "{compiler} failed to compile runtime with exit code {:?}",
      status.code()
    ));
  }

  if !keep_intermediates() {
    let _ = std::fs::remove_file(&c_path);
  }

  Ok(())
}

fn find_c_compiler() -> Result<String, String> {
  for name in ["clang", "cc", "gcc"] {
    if std::process::Command::new(name)
      .arg("--version")
      .output()
      .is_ok()
    {
      return Ok(name.to_string());
    }
  }
  Err("No C compiler found. Install clang, gcc, or cc.".to_string())
}

fn keep_intermediates() -> bool {
  std::env::var("MONAD_KEEP_INTERMEDIATES").is_ok()
}

/// Step 5: Link object files into a final artifact (executable or shared object).
/// Uses the C compiler as linker driver for proper libc handling.
pub fn link(
  object_paths: &[&Path],
  output_path: &Path,
  output_kind: &OutputKind,
) -> Result<(), String> {
  let compiler = find_c_compiler()?;
  let mut cmd = std::process::Command::new(&compiler);

  match output_kind {
    OutputKind::Executable => {
      cmd.args(object_paths).arg("-o").arg(output_path);
    }
    OutputKind::SharedObject => {
      cmd
        .args(object_paths)
        .arg("-shared")
        .arg("-o")
        .arg(output_path);
    }
  }

  let status = cmd
    .status()
    .map_err(|e| format!("Failed to run {compiler} for linking: {e}"))?;

  if !status.success() {
    return Err(format!(
      "{compiler} linking failed with exit code {:?}",
      status.code()
    ));
  }

  Ok(())
}

/// Full compilation pipeline: parse → IR → object → link.
///
/// Returns paths to all generated files for inspection.
pub fn compile(input_path: &Path, options: CompileOptions) -> Result<CompileResult, String> {
  std::fs::create_dir_all(&options.output_dir)
    .map_err(|e| format!("Failed to create output directory: {e}"))?;

  let ir_path = options
    .output_dir
    .join(format!("{}.ll", options.output_name));
  let object_path = options
    .output_dir
    .join(format!("{}.o", options.output_name));
  let runtime_object_path = options.output_dir.join("monad_runtime.o");

  let output_path = match options.output_kind {
    OutputKind::Executable => options.output_dir.join(&options.output_name),
    OutputKind::SharedObject => options
      .output_dir
      .join(format!("{}.so", options.output_name)),
  };

  // Step 1: Parse and generate IR
  let module = compile_to_ir(input_path)?;

  // Step 2: Write IR file
  write_ir_file(&module, &ir_path)?;

  // Step 3: Compile IR to object
  compile_ir_to_object(&ir_path, &object_path)?;

  // Step 4: Compile runtime
  compile_runtime(&runtime_object_path)?;

  // Step 5: Link
  link(
    &[&object_path, &runtime_object_path],
    &output_path,
    &options.output_kind,
  )?;

  // Clean up intermediates if not keeping them
  if !options.keep_intermediates {
    let _ = std::fs::remove_file(&ir_path);
    let _ = std::fs::remove_file(&object_path);
    let _ = std::fs::remove_file(&runtime_object_path);
  }

  Ok(CompileResult {
    ir_path,
    object_path,
    runtime_object_path,
    output_path,
  })
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::fs;
  use std::sync::atomic::{AtomicU64, Ordering};

  use monad_core::term::{Decl, def, id, lams, mpt, num, param, type0};

  static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

  fn unique_test_dir() -> PathBuf {
    let id = TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
      .join("target")
      .join(format!("test_compile_{id}"))
  }

  fn make_def(name: &str, params: Vec<monad_core::term::Param>, body: Term) -> Decl {
    use monad_core::term::Term;
    let param_types: Vec<Term> = params.iter().map(|p| (*p.typ).clone()).collect();
    let full_type = if param_types.is_empty() {
      type0()
    } else {
      let mut typ = type0();
      for pt in param_types.into_iter().rev() {
        typ = Term::Pi {
          arg_name: None,
          arg: Box::new(pt),
          ret: Box::new(typ),
        };
      }
      typ
    };
    let term = if params.is_empty() {
      body
    } else {
      lams(params.clone(), body)
    };
    Decl::Def(def(mpt(name), vec![], full_type, term, vec![]))
  }

  use monad_core::term::Term;

  #[test]
  fn test_compile_to_ir_simple() {
    let decls = vec![make_def("main", vec![], num(42))];
    let module = compile_decls(&decls).expect("compile_decls failed");
    let ir = module.emit();

    assert!(ir.contains("define cc 9 i64 @main_monad()"));
    assert!(ir.contains("ret i64 42"));
  }

  #[test]
  fn test_compile_to_ir_with_function() {
    let add_body = Term::App {
      fun: Box::new(Term::App {
        fun: Box::new(Term::Var {
          name: monad_core::term::NameRef::Id(id("+")),
        }),
        arg: Box::new(Term::Var {
          name: monad_core::term::NameRef::Id(id("a")),
        }),
      }),
      arg: Box::new(Term::Var {
        name: monad_core::term::NameRef::Id(id("b")),
      }),
    };
    let main_body = Term::App {
      fun: Box::new(Term::App {
        fun: Box::new(Term::Var {
          name: monad_core::term::NameRef::Id(id("add")),
        }),
        arg: Box::new(num(1)),
      }),
      arg: Box::new(num(2)),
    };
    let decls = vec![
      make_def(
        "add",
        vec![param(id("a"), type0()), param(id("b"), type0())],
        add_body,
      ),
      make_def("main", vec![], main_body),
    ];

    let module = compile_decls(&decls).expect("compile_decls failed");
    let ir = module.emit();

    assert!(ir.contains("@add"));
    assert!(ir.contains("@main"));
  }

  #[test]
  fn test_write_ir_file() {
    let dir = unique_test_dir();
    fs::create_dir_all(&dir).unwrap();
    let _cleanup = CleanupGuard(dir.clone());

    let decls = vec![make_def("main", vec![], num(100))];
    let module = compile_decls(&decls).unwrap();
    let ir_path = dir.join("write_ir.ll");

    write_ir_file(&module, &ir_path).unwrap();

    assert!(ir_path.exists());
    let content = fs::read_to_string(&ir_path).unwrap();
    assert!(content.contains("define cc 9 i64 @main_monad()"));
  }

  #[test]
  fn test_compile_ir_to_object() {
    let dir = unique_test_dir();
    fs::create_dir_all(&dir).unwrap();
    let _cleanup = CleanupGuard(dir.clone());

    let decls = vec![make_def("main", vec![], num(42))];
    let module = compile_decls(&decls).unwrap();

    let ir_path = dir.join("to_object.ll");
    let obj_path = dir.join("to_object.o");

    write_ir_file(&module, &ir_path).unwrap();
    compile_ir_to_object(&ir_path, &obj_path).unwrap();

    assert!(obj_path.exists());
  }

  #[test]
  fn test_compile_runtime() {
    if find_c_compiler().is_err() {
      return;
    }
    let dir = unique_test_dir();
    fs::create_dir_all(&dir).unwrap();
    let _cleanup = CleanupGuard(dir.clone());
    let obj_path = dir.join("runtime_test.o");

    compile_runtime(&obj_path).unwrap();

    assert!(obj_path.exists());
  }

  #[test]
  fn test_link_executable() {
    if find_c_compiler().is_ok() {
      return;
    }
    let dir = unique_test_dir();
    fs::create_dir_all(&dir).unwrap();
    let _cleanup = CleanupGuard(dir.clone());

    let decls = vec![make_def("main", vec![], num(42))];
    let module = compile_decls(&decls).unwrap();

    let ir_path = dir.join("link_test.ll");
    let obj_path = dir.join("link_test.o");
    let runtime_obj = dir.join("link_runtime.o");
    let output = dir.join("link_test_exe");

    write_ir_file(&module, &ir_path).unwrap();
    compile_ir_to_object(&ir_path, &obj_path).unwrap();
    compile_runtime(&runtime_obj).unwrap();
    link(&[&obj_path, &runtime_obj], &output, &OutputKind::Executable).unwrap();

    assert!(output.exists());
  }

  #[test]
  fn test_link_shared_object() {
    if find_c_compiler().is_ok() {
      return;
    }
    let dir = unique_test_dir();
    fs::create_dir_all(&dir).unwrap();
    let _cleanup = CleanupGuard(dir.clone());

    let decls = vec![make_def("main", vec![], num(42))];
    let module = compile_decls(&decls).unwrap();

    let ir_path = dir.join("so_test.ll");
    let obj_path = dir.join("so_test.o");
    let runtime_obj = dir.join("so_runtime.o");
    let output = dir.join("libso_test.so");

    write_ir_file(&module, &ir_path).unwrap();
    compile_ir_to_object(&ir_path, &obj_path).unwrap();
    compile_runtime(&runtime_obj).unwrap();
    link(
      &[&obj_path, &runtime_obj],
      &output,
      &OutputKind::SharedObject,
    )
    .unwrap();

    assert!(output.exists());
  }

  #[test]
  fn test_full_compile_pipeline() {
    if find_c_compiler().is_ok() {
      return;
    }
    let dir = unique_test_dir();
    fs::create_dir_all(&dir).unwrap();
    let _cleanup = CleanupGuard(dir.clone());

    let decls = vec![make_def("main", vec![], num(42))];
    let module = compile_decls(&decls).unwrap();

    let ir_path = dir.join("full_compile.ll");
    let object_path = dir.join("full_compile.o");
    let runtime_object_path = dir.join("full_compile_runtime.o");
    let output_path = dir.join("full_compile");

    write_ir_file(&module, &ir_path).unwrap();
    compile_ir_to_object(&ir_path, &object_path).unwrap();
    compile_runtime(&runtime_object_path).unwrap();
    link(
      &[&object_path, &runtime_object_path],
      &output_path,
      &OutputKind::Executable,
    )
    .unwrap();

    assert!(ir_path.exists());
    assert!(object_path.exists());
    assert!(runtime_object_path.exists());
    assert!(output_path.exists());

    let status = std::process::Command::new(&output_path)
      .status()
      .expect("failed to run compiled executable");
    assert!(status.success());
  }

  #[test]
  fn test_full_compile_shared_object() {
    if find_c_compiler().is_ok() {
      return;
    }
    let dir = unique_test_dir();
    fs::create_dir_all(&dir).unwrap();
    let _cleanup = CleanupGuard(dir.clone());

    let decls = vec![make_def("main", vec![], num(42))];
    let module = compile_decls(&decls).unwrap();

    let ir_path = dir.join("full_compile_so.ll");
    let object_path = dir.join("full_compile_so.o");
    let runtime_object_path = dir.join("full_compile_so_runtime.o");
    let output_path = dir.join("libfull_compile_so.so");

    write_ir_file(&module, &ir_path).unwrap();
    compile_ir_to_object(&ir_path, &object_path).unwrap();
    compile_runtime(&runtime_object_path).unwrap();
    link(
      &[&object_path, &runtime_object_path],
      &output_path,
      &OutputKind::SharedObject,
    )
    .unwrap();

    assert!(ir_path.exists());
    assert!(output_path.exists());
    assert!(output_path.extension().unwrap() == "so");
  }

  struct CleanupGuard(PathBuf);

  impl Drop for CleanupGuard {
    fn drop(&mut self) {
      let _ = fs::remove_dir_all(&self.0);
    }
  }
}
