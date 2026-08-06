use std::collections::{BTreeMap, HashSet};
use std::fmt::Display;
use std::fs;
use std::hash::{BuildHasherDefault, DefaultHasher, Hash};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use crate::diag::render_diagnostics;
use crate::eval::r#type::render_type_error_with_source;
use crate::eval::r#type::type_check;
use crate::eval::{EvalOptions, eval, eval_test};
#[cfg(feature = "kernel")]
use crate::eval_term::EvalTerm;
#[cfg(feature = "kernel")]
use crate::lower::LowerContext;
#[cfg(feature = "repl")]
use crate::parser::{ReplInput, repl_parser};
use crate::term::Decl;
use crate::term::Term::{self, Con, Hole};
#[cfg(feature = "repl")]
use crate::term::module::ParsedModule;
#[cfg(feature = "repl")]
use crate::term::module::module;
use crate::term::module::{
  LoadedModules, default_modules, load_module_files, load_module_from_text, module_warnings,
};
use crate::term::{
  Constructor, InductiveVariant, ModulePath, Named, SearchPaths, SourceContext, SourceRange, mpt,
  strings_to_list_term,
};
use crate::term::{app, id};

pub mod core_check;
pub mod core_check_module;
pub mod core_term;
pub mod core_unify;
pub mod diag;
pub mod eval;
pub mod eval_term;
pub mod lower;
pub mod lower_core;
pub mod parser;
pub mod raise_core;
pub mod runtime;
pub mod term;

#[cfg(all(not(target_arch = "wasm32"), feature = "repl"))]
use rustyline::{DefaultEditor, error::ReadlineError};

pub type Set<T> = HashSet<T, BuildHasherDefault<DefaultHasher>>;
pub fn empty_set<T: Eq + Hash>() -> Set<T> {
  HashSet::with_hasher(BuildHasherDefault::new())
}

pub fn set_of<T: Eq + Hash>(vals: impl Iterator<Item = T>) -> Set<T> {
  let mut set = empty_set();
  for value in vals {
    set.insert(value);
  }
  set
}

pub type Map<K, V> = BTreeMap<K, V>;

#[cfg(all(not(target_arch = "wasm32"), feature = "repl"))]
pub fn repl(options: EvalOptions) -> Result<(), String> {
  let mut rl = DefaultEditor::new().map_err(|e| format!("{e}"))?;

  if rl.load_history("history.txt").is_err() {
    println!("No previous history.");
  }
  let mut loaded_modules = default_modules().map_err(|e| format!("{e}"))?;
  loaded_modules.config.benchmark = options.benchmark;
  loaded_modules.set_search_paths(build_default_search_paths(&PathBuf::from("."), &[]));
  let module_path = ModulePath::top("'repl");
  let module = module(
    module_path.clone(),
    ParsedModule {
      decls: vec![],
      module_doc: None,
    },
  );
  loaded_modules.add_module(module);
  let mut loaded_scopes = loaded_modules.scopes();
  let mut global = loaded_scopes.global(&module_path).unwrap();
  loop {
    let readline = rl.readline(">> ");
    match readline {
      Ok(line) => {
        let repl_res = repl_parser(&line).map_err(|e| format!("{e}"));
        match repl_res {
          Err(e) => eprintln!("error: {e}"),
          Ok(repl_input) => {
            if options.debug {
              println!("Parsed: {repl_input}");
            }
            rl.add_history_entry(line.as_str())
              .map_err(|e| format!("{e}"))?;

            match repl_input {
              ReplInput::Term(term) => {
                let scope = global.scope();
                let t = type_check(term, Hole, &scope);
                match t {
                  Ok(tt) => {
                    let (term, typ) = tt.to_tuple();
                    println!("Eval type {typ}");

                    let term = eval(term, &scope, &options);
                    match term {
                      Ok(t) => println!("{t}"),
                      Err(e) => eprintln!("error: {e}"),
                    }
                  }
                  Err(e) => eprintln!("Type error: {e}"),
                }
              }
              ReplInput::Decls(Decl::Use(u)) => {
                if loaded_modules.get_module(&u.module_path).is_some() {
                  // Module already loaded, just update scope
                  loaded_scopes = loaded_modules.scopes();
                  global = loaded_scopes.global(&module_path).unwrap();
                } else {
                  let loaded = loaded_modules.clone();
                  let res = load_module_files(&u.module_path, loaded);
                  match res {
                    Ok(loaded) => {
                      if options.debug {
                        for module in loaded.modules() {
                          println!("Adding module {} to scope", module.path());
                        }
                      }
                      loaded_modules = loaded;
                      loaded_scopes = loaded_modules.scopes();
                      global = loaded_scopes.global(&module_path).unwrap();
                    }
                    Err(e) => eprintln!("loading error {e}"),
                  }
                }
              }
              ReplInput::Decls(decl) => {
                loaded_modules
                  .get_module_mut(&module_path)
                  .unwrap()
                  .add_decl(decl.clone());
                loaded_scopes = loaded_modules.scopes();
                global = loaded_scopes.global(&module_path).unwrap();
              }
            }
          }
        }
      }
      Err(ReadlineError::Interrupted) => {
        println!("CTRL-C");
        break;
      }
      Err(ReadlineError::Eof) => {
        println!("CTRL-D");
        break;
      }
      Err(err) => {
        println!("Error: {:?}", err);
        break;
      }
    }
  }
  rl.save_history("history.txt").map_err(|e| format!("{e}"))?;
  Ok(())
}

pub fn load_module(
  file: &PathBuf,
  path: &ModulePath,
  mut loaded: LoadedModules,
) -> Result<LoadedModules, String> {
  let text = fs::read_to_string(file).map_err(|e| format!("{e}"))?;
  load_module_from_text(&text, path, &mut loaded).map_err(|e| format!("{e}"))?;
  Ok(loaded)
}

#[cfg(feature = "kernel")]
/// Evaluate a type-checked Term through the EvalTerm kernel pipeline.
/// Returns the resulting EvalTerm (no conversion back to Term yet).
pub fn eval_kernel(term: Term, scope: &crate::term::module::Scope) -> Result<EvalTerm, String> {
  let mut ctx = LowerContext::new(scope);
  let lowered = ctx.lower(&term).map_err(|e| format!("lower: {e}"))?;
  let env = ctx.finish(scope).map_err(|e| format!("env: {e}"))?;
  crate::eval_term::eval_entry(&lowered, &env).map_err(|e| format!("eval: {e}"))
}

pub fn run(
  input: PathBuf,
  args: Vec<String>,
  options: EvalOptions,
  extra_mote_paths: Vec<PathBuf>,
) -> Result<(), String> {
  let path: ModulePath = input.clone().into();
  let source = fs::read_to_string(&input).map_err(|e| format!("{e}"))?;
  let mut loaded = default_modules().map_err(|e| format!("{e}"))?;
  loaded.config.benchmark = options.benchmark;
  let search_paths = build_default_search_paths(&input, &extra_mote_paths);
  loaded.set_search_paths(search_paths);
  load_module_from_text(&source, &path, &mut loaded).map_err(|e| format!("{e}"))?;
  let module = loaded
    .get_module(&path)
    .ok_or_else(|| format!("Module {path} not loaded"))?;
  let warnings = module_warnings(module, Some(&input));
  if !warnings.is_empty() {
    eprintln!(
      "{}",
      render_diagnostics(&warnings, Some(&source), options.use_colors)
    );
  }
  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(&path).expect("Module not loaded");
  if options.debug {
    println!("{global}");
  }
  let arg: Term = strings_to_list_term(args);

  let def = module
    .get_def(&mpt("main"))
    .ok_or("main not found")?
    .value();
  let input_term = if def.term.is_lam() {
    app(def.term.clone(), arg)
  } else {
    def.term.clone()
  };

  let (term, typ) = type_check(input_term, Hole, &global.scope())
    .map_err(|e| render_type_error_with_source(&source, &e, options.use_colors, Some(&input)))?
    .to_tuple();
  println!("Eval type {typ}");
  #[cfg(feature = "kernel")]
  {
    let kernel_result = eval_kernel(term.clone(), &global.scope())
      .map_err(|e| format!("kernel: {e}"))
      .inspect_err(|e| eprintln!("{e}"))?;
    println!("Kernel result {kernel_result}");
    if options.debug {
      eprintln!("Note: kernel evaluator used (feature \"kernel\" enabled)");
    }
  }
  #[cfg(not(feature = "kernel"))]
  {
    let term = eval(term, &global.scope(), &options)
      .map_err(|e| format!("{e}"))
      .inspect_err(|e| eprintln!("{e}"))?;

    if options.debug {
      println!("Eval result {term}");
    }
  }
  Ok(())
}

pub fn vec_fmt<T: Display>(v: &[T]) -> String {
  v.iter()
    .map(|t| format!("{t}"))
    .collect::<Vec<String>>()
    .join(", ")
}

fn build_default_search_paths(input: &PathBuf, extra_paths: &[PathBuf]) -> SearchPaths {
  let mut paths = SearchPaths::empty();

  if let Some(parent) = input.parent() {
    paths.push(parent.to_path_buf());
  }

  paths.push(PathBuf::from("."));

  for p in extra_paths {
    paths.push(p.clone());
  }

  if let Ok(cwd) = std::env::current_dir() {
    let motes_dir = cwd.join("motes");
    if motes_dir.is_dir() {
      paths.push(motes_dir.clone());
      if let Ok(entries) = std::fs::read_dir(&motes_dir) {
        for entry in entries.flatten() {
          let src_dir = entry.path().join("src");
          if src_dir.is_dir() {
            paths.push(src_dir);
          }
        }
      }
    }
  }

  if let Ok(monad_path) = std::env::var("MONAD_PATH") {
    for dir in std::env::split_paths(&monad_path) {
      paths.push(dir);
    }
  }

  paths
}

const GREEN: &str = "\x1b[32m";
const RED: &str = "\x1b[31m";
const YELLOW: &str = "\x1b[33m";
const RESET: &str = "\x1b[0m";

enum TestResult {
  Pass,
  Fail,
  FailWithMessage(String),
}

fn detect_test_result(term: &Term) -> TestResult {
  match term {
    Term::Ctx { term, .. } => detect_test_result(term),
    Con(Constructor {
      name,
      typ_name,
      args,
      ..
    }) => {
      if typ_name == &mpt("Bool") {
        return if name == &id("true") {
          TestResult::Pass
        } else if name == &id("false") {
          TestResult::Fail
        } else {
          TestResult::FailWithMessage(format!("unexpected result: {term}"))
        };
      }
      if typ_name == &mpt("IO")
        && let Some(Some(inner)) = args.first()
      {
        return detect_test_result(inner);
      }
      if typ_name == &mpt("Result") {
        if name == &id("ok") {
          return TestResult::Pass;
        } else if name == &id("err") {
          if let Some(Some(msg_term)) = args.first() {
            let msg = extract_string_literal(msg_term);
            return TestResult::FailWithMessage(msg.unwrap_or_else(|| msg_term.to_string()));
          }
          return TestResult::Fail;
        }
      }
      TestResult::FailWithMessage(format!("unexpected result: {term}"))
    }
    _ => TestResult::FailWithMessage(format!("unexpected result: {term}")),
  }
}

fn extract_string_literal(term: &Term) -> Option<String> {
  match term {
    Term::Ctx { term, .. } => extract_string_literal(term),
    Term::Lit {
      value: crate::term::Literal::Str { value },
    } => Some(value.clone()),
    _ => None,
  }
}

/// Recursively find all .mo files in a directory.
fn collect_mo_files(dir: &Path) -> Vec<PathBuf> {
  let mut files = Vec::new();
  if dir.is_dir() {
    for entry in std::fs::read_dir(dir).unwrap_or_else(|_| panic!("cannot read dir {dir:?}")) {
      let entry = entry.unwrap();
      let path = entry.path();
      if path.is_dir() {
        files.extend(collect_mo_files(&path));
      } else if path.extension().is_some_and(|e| e == "mo") {
        files.push(path);
      }
    }
  }
  files
}

#[derive(Debug)]
struct FileOutput {
  passed: usize,
  failed: usize,
  output_lines: Vec<String>,
  error_message: Option<String>,
  failures: Vec<(String, String)>,
}

/// Process a single test file. Returns updated `LoadedModules` and the file result.
fn test_one_file(
  file: &Path,
  path: &ModulePath,
  mut loaded: LoadedModules,
  options: &EvalOptions,
  test_timeout: Option<std::time::Duration>,
  file_index: usize,
  total_files: usize,
) -> (LoadedModules, FileOutput) {
  let file_path = file.to_path_buf();

  let header = format!(
    "{YELLOW}[{}/{}] Testing {}...{RESET}",
    file_index + 1,
    total_files,
    file_path.display()
  );
  println!("{header}");

  let backup = loaded.clone();
  loaded = match load_module(&file_path, path, loaded) {
    Ok(l) => l,
    Err(e) => {
      return (
        backup,
        FileOutput {
          passed: 0,
          failed: 1,
          output_lines: vec![format!("{RED}FAIL{RESET} {}", file_path.display())],
          error_message: Some(format!("failed to compile {}: {e}", file_path.display())),
          failures: Vec::new(),
        },
      );
    }
  };

  let module = match loaded.get_module(path) {
    Some(m) => m,
    None => {
      return (
        loaded,
        FileOutput {
          passed: 0,
          failed: 0,
          output_lines: Vec::new(),
          error_message: None,
          failures: Vec::new(),
        },
      );
    }
  };

  let loaded_scopes = loaded.scopes();
  let global = loaded_scopes.global(path).expect("Module not loaded");

  let mut output_lines: Vec<String> = Vec::new();
  if options.debug {
    output_lines.push(format!("{global}"));
  }

  let warnings = module_warnings(module, Some(&file_path));
  if !warnings.is_empty() {
    output_lines.push(render_diagnostics(&warnings, None, options.use_colors));
  }

  let test_defs: Vec<_> = module
    .defs()
    .into_iter()
    .filter(|ctx| ctx.value().has_test_attr())
    .collect();

  if test_defs.is_empty() {
    return (
      loaded,
      FileOutput {
        passed: 0,
        failed: 0,
        output_lines: Vec::new(),
        error_message: None,
        failures: Vec::new(),
      },
    );
  }

  let mut passed = 0;
  let mut failed = 0;
  let mut failures: Vec<(String, String)> = Vec::new();

  for ctx in &test_defs {
    let def = ctx.value();
    let name = def.name.to_string();
    // `def` was already fully type-checked and elaborated by `load_module` above
    // (module.defs() returns the post-type-check decls, with e.g. `==` already
    // resolved to a concrete `instance-BEq-*.beq` call). Re-running `type_check`
    // on that already-elaborated term can spuriously fail: elaboration commits
    // generic calls to a specific concrete instance, which is no longer flexible
    // enough for the checker to re-derive the same polymorphic instantiation from
    // scratch. There's no need to check it again — just use it directly.
    let term = def.term.clone();
    let typ = def.typ().clone();

    if options.debug {
      output_lines.push(format!("test {name} : {typ}"));
    }

    let start = Instant::now();
    let eval_result = run_test_eval(term.clone(), &global.scope(), &options, test_timeout);
    let duration = start.elapsed();
    let duration_str = format_duration(duration);

    let result = match eval_result {
      Ok(t) => t,
      Err(e) => {
        failed += 1;
        failures.push((name.clone(), format!("eval error: {e}")));
        continue;
      }
    };

    if options.debug {
      output_lines.push(format!("  eval: {result}"));
    }

    match detect_test_result(&result) {
      TestResult::Pass => {
        passed += 1;
        output_lines.push(format!("{GREEN}PASS{RESET} {name} ({duration_str})"));
      }
      TestResult::Fail => {
        failed += 1;
        output_lines.push(format!("{RED}FAIL{RESET} {name} ({duration_str})"));
      }
      TestResult::FailWithMessage(msg) => {
        failed += 1;
        output_lines.push(format!("{RED}FAIL{RESET} {name} ({duration_str}): {msg}"));
        failures.push((name.clone(), msg));
      }
    }
  }

  let total = passed + failed;
  if failed > 0 {
    output_lines.push(format!(
      "{passed}/{total} tests passed in {}: {RED}FAILED{RESET}",
      file_path.display()
    ));
  } else if passed > 0 {
    output_lines.push(format!(
      "{passed}/{total} tests passed in {}",
      file_path.display()
    ));
  }

  (
    loaded,
    FileOutput {
      passed,
      failed,
      output_lines,
      error_message: None,
      failures,
    },
  )
}

fn print_file_output(result: &FileOutput) {
  for line in &result.output_lines {
    println!("{line}");
  }
  for (name, msg) in &result.failures {
    eprintln!("{RED}FAIL{RESET} {name}: {msg}");
  }
}

fn print_final_summary(
  total_passed: usize,
  total_failed: usize,
  overall_errors: &[String],
) -> Result<(), String> {
  let total_tests = total_passed + total_failed;
  if total_tests == 0 {
    return Err("No tests found".to_string());
  }

  if total_failed > 0 {
    println!("{RED}{total_passed}/{total_tests} total tests passed{RESET}");
    Err(format!(
      "{} test(s) failed\n{}",
      total_failed,
      overall_errors.join("\n")
    ))
  } else {
    println!("{GREEN}{total_passed}/{total_tests} total tests passed{RESET}");
    Ok(())
  }
}

fn run_tests_sequential(
  files: &[PathBuf],
  master_loaded: &LoadedModules,
  options: &EvalOptions,
  test_timeout: Option<std::time::Duration>,
) -> Result<(), String> {
  let mut total_passed = 0;
  let mut total_failed = 0;
  let mut overall_errors: Vec<String> = Vec::new();
  let mut loaded = master_loaded.clone();
  let total = files.len();

  for (i, file) in files.iter().enumerate() {
    let path: ModulePath = file.clone().into();
    let (new_loaded, result) = test_one_file(file, &path, loaded, options, test_timeout, i, total);
    loaded = new_loaded;

    print_file_output(&result);

    total_passed += result.passed;
    total_failed += result.failed;

    if let Some(ref err) = result.error_message {
      eprintln!("  {err}");
      overall_errors.push(err.clone());
    }
  }

  print_final_summary(total_passed, total_failed, &overall_errors)
}

fn run_tests_parallel(
  files: &[PathBuf],
  master_loaded: &LoadedModules,
  options: &EvalOptions,
  num_threads: usize,
  test_timeout: Option<std::time::Duration>,
) -> Result<(), String> {
  let n_threads = std::cmp::min(num_threads, files.len());
  let chunk_size = files.len().div_ceil(n_threads);

  let total_passed = Arc::new(AtomicUsize::new(0));
  let total_failed = Arc::new(AtomicUsize::new(0));
  let overall_errors: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));

  let mut handles = Vec::with_capacity(n_threads);
  for (chunk_idx, chunk) in files.chunks(chunk_size).enumerate() {
    let mut loaded = master_loaded.clone();
    let opts = options.clone();
    let chunk_files: Vec<PathBuf> = chunk.to_vec();
    let passed = Arc::clone(&total_passed);
    let failed = Arc::clone(&total_failed);
    let errors = Arc::clone(&overall_errors);
    let total = files.len();
    let base_idx = chunk_idx * chunk_size;

    let handle = std::thread::Builder::new()
      .stack_size(8 * 1024 * 1024)
      .spawn(move || {
        for (i, file) in chunk_files.iter().enumerate() {
          let path: ModulePath = file.clone().into();
          let (new_loaded, output) = test_one_file(
            file,
            &path,
            loaded,
            &opts,
            test_timeout,
            base_idx + i,
            total,
          );
          loaded = new_loaded;

          print_file_output(&output);

          passed.fetch_add(output.passed, Ordering::Relaxed);
          failed.fetch_add(output.failed, Ordering::Relaxed);
          if let Some(ref err) = output.error_message {
            eprintln!("  {err}");
            errors.lock().unwrap().push(err.clone());
          }
        }
      })
      .expect("failed to spawn test thread");
    handles.push(handle);
  }

  for handle in handles {
    handle.join().expect("test thread panicked");
  }

  let total_passed = total_passed.load(Ordering::Relaxed);
  let total_failed = total_failed.load(Ordering::Relaxed);
  let overall_errors = Arc::try_unwrap(overall_errors)
    .unwrap()
    .into_inner()
    .unwrap();

  print_final_summary(total_passed, total_failed, &overall_errors)
}

fn format_duration(d: std::time::Duration) -> String {
  let nanos = d.as_nanos();
  if nanos < 1_000 {
    format!("{nanos}ns")
  } else if nanos < 1_000_000 {
    format!("{:.0}µs", d.as_micros())
  } else if nanos < 1_000_000_000 {
    format!("{:.2}ms", d.as_secs_f64() * 1000.0)
  } else {
    format!("{:.2}s", d.as_secs_f64())
  }
}

fn run_test_eval(
  term: Term,
  scope: &crate::term::module::Scope,
  options: &EvalOptions,
  test_timeout: Option<std::time::Duration>,
) -> Result<Term, String> {
  match test_timeout {
    Some(timeout) => eval_test(term, scope, options, timeout).map_err(|e| format!("{e}")),
    None => eval(term, scope, options).map_err(|e| format!("{e}")),
  }
}

pub fn run_tests(
  inputs: Vec<PathBuf>,
  options: EvalOptions,
  num_threads: usize,
  test_timeout: Option<std::time::Duration>,
  extra_mote_paths: Vec<PathBuf>,
) -> Result<(), String> {
  let mut files: Vec<PathBuf> = Vec::new();
  for input in &inputs {
    if input.is_dir() {
      files.extend(collect_mo_files(input));
    } else {
      files.push(input.clone());
    }
  }
  files.sort();
  files.dedup();

  let mut master_loaded = default_modules().map_err(|e| format!("{e}"))?;
  master_loaded.set_test_mode(true);
  master_loaded.config.benchmark = options.benchmark;

  let search_paths = if let Some(first_input) = inputs.first() {
    build_default_search_paths(first_input, &extra_mote_paths)
  } else {
    build_default_search_paths(&PathBuf::from("."), &extra_mote_paths)
  };
  master_loaded.set_search_paths(search_paths);

  // Ensure std/test is loaded (for Test.assert)
  let test_path: ModulePath = ModulePath::new(vec![id("std"), id("test")]);
  if master_loaded.get_module(&test_path).is_none() {
    master_loaded = load_module_files(&test_path, master_loaded)
      .map_err(|e| format!("Failed to load std/test: {e}"))?;
  }

  // Filter out files that are already part of the default modules
  let files: Vec<PathBuf> = files
    .into_iter()
    .filter(|file| {
      let path: ModulePath = file.clone().into();
      let is_default = master_loaded.get_module(&path).is_some() || {
        let last = path.last();
        master_loaded
          .get_module(&ModulePath::single(last.clone()))
          .is_some()
      };
      !is_default
    })
    .collect();

  // Single file or single-threaded: run sequentially
  if num_threads <= 1 || files.len() <= 1 {
    run_tests_sequential(&files, &master_loaded, &options, test_timeout)
  } else {
    run_tests_parallel(&files, &master_loaded, &options, num_threads, test_timeout)
  }
}

/// One target file's `organize-imports` result: the rewritten source if
/// anything changed (`None` means the file already has no bare
/// `use`/`open`/`@[...]` to convert), or the error that kept it from being
/// checked at all (parse/type error — same as `check_files`, a broken file
/// is reported rather than silently skipped or guessed at).
#[derive(Debug, Clone)]
pub struct OrganizeImportsResult {
  pub path: PathBuf,
  pub new_source: Option<String>,
  pub error: Option<String>,
}

/// Compute `organize-imports` edits for every `.mo` file under `inputs`
/// (directories expanded recursively, same as `check_files`), reusing one
/// incrementally-growing `LoadedModules` across the batch so cross-file
/// `use`/`open` targets resolve — mirrors `check_files`'s structure
/// exactly (same file-collection, same `master_loaded` threading, same
/// "skip files already satisfied by the embedded defaults" filter) so the
/// two commands can't drift on what counts as "the file set" or "loaded
/// successfully". Pure computation — callers decide whether to print a
/// diff or write `new_source` back to disk.
pub fn organize_imports_for_files(
  inputs: Vec<PathBuf>,
  extra_mote_paths: Vec<PathBuf>,
) -> Result<Vec<OrganizeImportsResult>, String> {
  let inputs = if inputs.is_empty() {
    vec![PathBuf::from(".")]
  } else {
    inputs
  };

  let mut files: Vec<PathBuf> = Vec::new();
  for input in &inputs {
    if input.is_dir() {
      files.extend(collect_mo_files(input));
    } else {
      files.push(input.clone());
    }
  }
  files.sort();
  files.dedup();

  let mut master_loaded = default_modules().map_err(|e| format!("{e}"))?;
  let search_paths = build_default_search_paths(&inputs[0], &extra_mote_paths);
  master_loaded.set_search_paths(search_paths);

  let files: Vec<PathBuf> = files
    .into_iter()
    .filter(|file| {
      let path: ModulePath = file.clone().into();
      let is_default = master_loaded.get_module(&path).is_some() || {
        let last = path.last();
        master_loaded
          .get_module(&ModulePath::single(last.clone()))
          .is_some()
      };
      !is_default
    })
    .collect();

  let mut results = Vec::with_capacity(files.len());
  for file in &files {
    let path: ModulePath = file.clone().into();
    let text = match fs::read_to_string(file) {
      Err(e) => {
        results.push(OrganizeImportsResult {
          path: file.clone(),
          new_source: None,
          error: Some(format!("{e}")),
        });
        continue;
      }
      Ok(text) => text,
    };
    match crate::term::module::load_module_from_text_typed(&text, &path, &mut master_loaded) {
      Ok(()) => {
        let module = master_loaded
          .get_module(&path)
          .expect("just-loaded module must be present");
        let edits =
          crate::term::organize_imports::compute_organize_import_edits(module, &master_loaded);
        let new_source = if edits.is_empty() {
          None
        } else {
          Some(crate::term::organize_imports::apply_text_edits(
            &text, edits,
          ))
        };
        results.push(OrganizeImportsResult {
          path: file.clone(),
          new_source,
          error: None,
        });
      }
      Err(e) => {
        results.push(OrganizeImportsResult {
          path: file.clone(),
          new_source: None,
          error: Some(format!("{e}")),
        });
      }
    }
  }

  Ok(results)
}

/// One target file's check result — every parse/type error found in it,
/// with real positions. Kept free of any JSON/LSP-shape opinions (field
/// names, 0- vs 1-indexing, `uri` vs `path`) on purpose: that's a wire-
/// format concern for whichever CLI/LSP layer serializes this, not
/// something `core` should know about.
#[derive(Debug, Clone)]
pub struct FileCheckResult {
  pub path: PathBuf,
  pub diagnostics: Vec<crate::diag::Diagnostic>,
}

/// Parse and type-check every `.mo` file under `inputs` (directories are
/// expanded recursively via `collect_mo_files`, same as `run_tests`), but
/// — unlike `run_tests` — never evaluates `@[test]` defs or anything else;
/// this only ever runs the checker, so it's usable as a fast, side-
/// effect-free "does this compile" pass. Reuses `load_module_files` (the
/// same real loader `Run`/`Test` go through) file by file rather than
/// reimplementing loading/checking, so `check`'s notion of "does this
/// file type-check" can never drift from what actually running it means.
///
/// A file that fails to load contributes its `TypeError` (or, for a
/// generic loader failure — e.g. a missing `use`d module — a single
/// synthetic `Diagnostic` with no location) as that file's diagnostics;
/// `master_loaded` only advances past files that loaded successfully, so
/// one broken file can't prevent the rest from being checked.
pub fn check_files(
  inputs: Vec<PathBuf>,
  extra_mote_paths: Vec<PathBuf>,
) -> Result<Vec<FileCheckResult>, String> {
  let inputs = if inputs.is_empty() {
    vec![PathBuf::from(".")]
  } else {
    inputs
  };

  let mut files: Vec<PathBuf> = Vec::new();
  for input in &inputs {
    if input.is_dir() {
      files.extend(collect_mo_files(input));
    } else {
      files.push(input.clone());
    }
  }
  files.sort();
  files.dedup();

  let mut master_loaded = default_modules().map_err(|e| format!("{e}"))?;
  let search_paths = build_default_search_paths(&inputs[0], &extra_mote_paths);
  master_loaded.set_search_paths(search_paths);

  // Skip files already satisfied by the embedded default modules — same
  // filter `run_tests` applies, for the same reason: a bare re-check of
  // e.g. `prelude` would just report "already loaded", not a real result.
  let files: Vec<PathBuf> = files
    .into_iter()
    .filter(|file| {
      let path: ModulePath = file.clone().into();
      let is_default = master_loaded.get_module(&path).is_some() || {
        let last = path.last();
        master_loaded
          .get_module(&ModulePath::single(last.clone()))
          .is_some()
      };
      !is_default
    })
    .collect();

  let mut results = Vec::with_capacity(files.len());
  for file in &files {
    let path: ModulePath = file.clone().into();
    let diagnostics = match fs::read_to_string(file) {
      Err(e) => vec![crate::diag::Diagnostic {
        message: format!("{e}"),
        path: Some(file.clone()),
        ..Default::default()
      }],
      Ok(text) => {
        let (diagnostics, updated) = check_one_source(file, &text, &path, master_loaded.clone());
        master_loaded = updated;
        diagnostics
      }
    };
    results.push(FileCheckResult {
      path: file.clone(),
      diagnostics,
    });
  }

  Ok(results)
}

/// Type-check one file's given `source` text against `loaded`, returning
/// its diagnostics and (whether or not it loaded successfully — a failed
/// load still returns `loaded` unchanged, not consumed) the resulting
/// `LoadedModules`. The shared per-file primitive both `check_files`
/// (disk-reading, multi-file, batch CLI) and `check_source` (single
/// in-memory buffer, the LSP server's `didOpen`/`didChange` path) build
/// on, so the two can never drift on what "does this file check" means.
fn check_one_source(
  path: &PathBuf,
  source: &str,
  module_path: &ModulePath,
  mut loaded: LoadedModules,
) -> (Vec<crate::diag::Diagnostic>, LoadedModules) {
  match crate::term::module::load_module_from_text_typed(source, module_path, &mut loaded) {
    Ok(()) => {
      let warnings = loaded
        .get_module(module_path)
        .map(|module| module_warnings(module, Some(path)))
        .unwrap_or_default();
      (warnings, loaded)
    }
    Err(crate::term::module::LoadingError::Type(type_error)) => (
      crate::eval::r#type::type_error_as_diagnostics(&type_error, Some(path)),
      loaded,
    ),
    Err(crate::term::module::LoadingError::Generic(message)) => (
      vec![crate::diag::Diagnostic {
        message,
        path: Some(path.clone()),
        ..Default::default()
      }],
      loaded,
    ),
  }
}

/// Type-check a single file's CURRENT in-memory content — unlike
/// `check_files` (which always reads from disk), this is what the LSP
/// server calls on `textDocument/didOpen`/`didChange`, where the editor's
/// buffer may have unsaved changes that differ from what's on disk.
pub fn check_source(
  path: &Path,
  source: &str,
  extra_mote_paths: Vec<PathBuf>,
) -> Result<Vec<crate::diag::Diagnostic>, String> {
  let path = path.to_path_buf();
  let module_path: ModulePath = path.clone().into();
  let mut loaded = default_modules().map_err(|e| format!("{e}"))?;
  loaded.set_search_paths(build_default_search_paths(&path, &extra_mote_paths));
  let (diagnostics, _) = check_one_source(&path, source, &module_path, loaded);
  Ok(diagnostics)
}

/// `organize-imports` edits for a single file's CURRENT in-memory
/// content — the LSP server's `textDocument/codeAction` and
/// `workspace/executeCommand("monad.organizeImports")` handlers build on
/// this, same "single in-memory buffer" shape as `check_source`. Returns
/// an empty edit list (not an error) if the file doesn't parse/type-check
/// — there's nothing sound to compute a minimal import list from, and the
/// real problem already surfaces via `check_source`'s diagnostics.
pub fn organize_imports_for_source(
  path: &Path,
  source: &str,
  extra_mote_paths: Vec<PathBuf>,
) -> Result<Vec<crate::term::organize_imports::TextEdit>, String> {
  let path = path.to_path_buf();
  let module_path: ModulePath = path.clone().into();
  let mut loaded = default_modules().map_err(|e| format!("{e}"))?;
  loaded.set_search_paths(build_default_search_paths(&path, &extra_mote_paths));
  match crate::term::module::load_module_from_text_typed(source, &module_path, &mut loaded) {
    Ok(()) => {
      let module = loaded
        .get_module(&module_path)
        .expect("just-loaded module must be present");
      Ok(crate::term::organize_imports::compute_organize_import_edits(module, &loaded))
    }
    Err(_) => Ok(Vec::new()),
  }
}

/// Coarse-grained symbol classification — enough to distinguish the
/// handful of top-level decl kinds a workspace symbol index cares about,
/// not a full mirror of `InductiveVariant`/`Decl`'s own variant set (e.g.
/// `Use`/`Open`/`Infix` decls aren't symbols at all, so they're simply
/// skipped rather than given a `SymbolKind` of their own).
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SymbolKind {
  Function,
  Struct,
  Class,
  Enum,
  Instance,
}

#[derive(Debug, Clone)]
pub struct SymbolInfo {
  pub name: String,
  pub kind: SymbolKind,
  pub location: Option<SourceRange>,
  /// A short human-readable summary — a `def`'s full type signature
  /// (rendered via `Term`'s `Display`), `None` for kinds that don't have
  /// an obvious one-line summary yet (`Struct`/`Class`/`Enum`/`Instance`).
  /// This is what `hover --json` shows for a symbol; `symbols --json`
  /// exposes it too (LSP's `SymbolInformation.detail` has the same role).
  pub detail: Option<String>,
}

#[derive(Debug, Clone)]
pub struct FileSymbols {
  pub path: PathBuf,
  pub symbols: Vec<SymbolInfo>,
}

/// Top-level `Def`/`Type`/`Ins` decls (with their real, decl-level
/// `SourceContext` span) for every named symbol `check_module_source`'s
/// `Vec<SourceContext<Decl>>` output. Only ever needs decl-level spans
/// (already correct — see Phase 0's notes), not the sub-expression-level
/// `CoreTerm` span work Phase 0b covers, since a symbol's *location* is
/// just "where the whole declaration is", not "which sub-expression".
fn symbols_from_decls(decls: &[SourceContext<Decl>]) -> Vec<SymbolInfo> {
  let mut symbols = Vec::new();
  for ctx in decls {
    let location = Some(ctx.loc.clone());
    match ctx.value() {
      Decl::Def(def) => symbols.push(SymbolInfo {
        name: def.name.to_string(),
        kind: SymbolKind::Function,
        location,
        detail: Some(def.typ.to_string()),
      }),
      Decl::Type(ind) => {
        let kind = match ind.variant() {
          InductiveVariant::Struct => SymbolKind::Struct,
          InductiveVariant::Class => SymbolKind::Class,
          InductiveVariant::Generic => SymbolKind::Enum,
        };
        symbols.push(SymbolInfo {
          name: ind.name().to_string(),
          kind,
          location,
          detail: None,
        });
      }
      Decl::Ins(instance) => symbols.push(SymbolInfo {
        name: instance.name().to_string(),
        kind: SymbolKind::Instance,
        location,
        detail: None,
      }),
      _ => {}
    }
  }
  symbols
}

/// Workspace symbol index: every named `def`/`type`/`instance` in each
/// target file, with its declaration-level location. Shares `check_files`'
/// file-collection and per-file loading (`load_module_from_text_typed`) —
/// a file that fails to load simply contributes no symbols, since a
/// symbol table over broken code isn't this function's job (that's
/// `check_files`'s).
pub fn symbols_for_files(
  inputs: Vec<PathBuf>,
  extra_mote_paths: Vec<PathBuf>,
) -> Result<Vec<FileSymbols>, String> {
  let inputs = if inputs.is_empty() {
    vec![PathBuf::from(".")]
  } else {
    inputs
  };

  let mut files: Vec<PathBuf> = Vec::new();
  for input in &inputs {
    if input.is_dir() {
      files.extend(collect_mo_files(input));
    } else {
      files.push(input.clone());
    }
  }
  files.sort();
  files.dedup();

  let mut master_loaded = default_modules().map_err(|e| format!("{e}"))?;
  let search_paths = build_default_search_paths(&inputs[0], &extra_mote_paths);
  master_loaded.set_search_paths(search_paths);

  let files: Vec<PathBuf> = files
    .into_iter()
    .filter(|file| {
      let path: ModulePath = file.clone().into();
      let is_default = master_loaded.get_module(&path).is_some() || {
        let last = path.last();
        master_loaded
          .get_module(&ModulePath::single(last.clone()))
          .is_some()
      };
      !is_default
    })
    .collect();

  let mut results = Vec::with_capacity(files.len());
  for file in &files {
    let path: ModulePath = file.clone().into();
    let symbols = match fs::read_to_string(file) {
      Err(_) => Vec::new(),
      Ok(text) => {
        let (symbols, updated) = symbols_one_source(&text, &path, master_loaded.clone());
        master_loaded = updated;
        symbols
      }
    };
    results.push(FileSymbols {
      path: file.clone(),
      symbols,
    });
  }

  Ok(results)
}

/// The shared per-file primitive `symbols_for_files` (disk-reading,
/// multi-file) and `symbols_from_source` (single in-memory buffer, the
/// LSP server's path) both build on — mirrors `check_one_source`.
fn symbols_one_source(
  source: &str,
  module_path: &ModulePath,
  mut loaded: LoadedModules,
) -> (Vec<SymbolInfo>, LoadedModules) {
  match crate::term::module::load_module_from_text_typed(source, module_path, &mut loaded) {
    Ok(()) => {
      let symbols = loaded
        .get_module(module_path)
        .map(|m| symbols_from_decls(m.clone().to_decls().as_slice()))
        .unwrap_or_default();
      (symbols, loaded)
    }
    Err(_) => (Vec::new(), loaded),
  }
}

/// Symbol index for a single file's CURRENT in-memory content — unlike
/// `symbols_for_files` (which always reads from disk), this is what the
/// LSP server's `hover`/`definition` handlers call, so a lookup reflects
/// the editor's buffer even before it's been saved.
pub fn symbols_from_source(
  path: &Path,
  source: &str,
  extra_mote_paths: Vec<PathBuf>,
) -> Result<Vec<SymbolInfo>, String> {
  let path = path.to_path_buf();
  let module_path: ModulePath = path.clone().into();
  let mut loaded = default_modules().map_err(|e| format!("{e}"))?;
  loaded.set_search_paths(build_default_search_paths(&path, &extra_mote_paths));
  let (symbols, _) = symbols_one_source(source, &module_path, loaded);
  Ok(symbols)
}

#[cfg(test)]
mod test {
  use super::*;

  /// Regression test for `test_one_file`: it used to redundantly re-run
  /// `type_check` on a def's already-elaborated term (with `Hole` as the
  /// expected type), discarding the def's own checked type. For a generic
  /// function called via an unannotated lambda, elaboration had already
  /// committed the call to one concrete instance, which the redundant
  /// second check could no longer re-derive the same polymorphic
  /// instantiation for — spuriously failing tests that `load_module`
  /// already type-checked successfully. `test_one_file` now reuses the
  /// def's own term/type directly instead of re-checking.
  #[test]
  fn test_direct_generic_call_via_lambda_does_not_regress() {
    let dir = PathBuf::from("/tmp").join(format!(
      "monad-test-generic-lambda-{:x}",
      std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("generic_lambda_test.mo");
    fs::write(
      &file,
      r#"
def my_any {A : Type} (pred : A -> Bool) (xs : List A) : Bool :=
    match xs {
        empty => false,
        cons a tail =>
            if pred a
            then true
            else my_any pred tail,
        _ => false
    }

@[test]
def test_direct_generic_call : Bool :=
    my_any (fn a => a == "c") ["a", "b", "c"]
"#,
    )
    .unwrap();

    // `run_tests` unconditionally loads `std/test.mo` (for `Test.assert`);
    // resolve it via the workspace root rather than relying on cwd, since
    // `cargo test` runs with cwd set to this crate's directory, not the
    // workspace root where `std/` actually lives.
    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
      .parent()
      .unwrap()
      .to_path_buf();
    let result = run_tests(
      vec![file],
      EvalOptions::default(),
      1,
      None,
      vec![workspace_root],
    );

    fs::remove_dir_all(&dir).unwrap();

    assert!(
      result.is_ok(),
      "Direct (non-piped) generic call via an unannotated lambda should pass: {:?}",
      result
    );
  }
}
