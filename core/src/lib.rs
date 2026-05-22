use std::collections::{BTreeMap, HashSet};
use std::fmt::Display;
use std::fs;
use std::hash::{BuildHasherDefault, DefaultHasher, Hash};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use crate::eval::r#type::render_type_error_with_source;
use crate::eval::r#type::type_check;
use crate::eval::{EvalOptions, eval, eval_test};
#[cfg(feature = "kernel")]
use crate::eval_term::EvalTerm;
#[cfg(feature = "kernel")]
use crate::lower::LowerContext;
#[cfg(feature = "repl")]
use crate::parser::{ReplInput, repl_parser};
#[cfg(feature = "repl")]
use crate::term::Decl;
use crate::term::Term::{self, Con, Hole};
#[cfg(feature = "repl")]
use crate::term::module::ParsedModule;
#[cfg(feature = "repl")]
use crate::term::module::module;
use crate::term::module::{
  LoadedModules, default_modules, load_module_files, load_module_from_text,
};
use crate::term::{Constructor, ModulePath, mpt, strings_to_list_term};
use crate::term::{app, id};

pub mod diag;
pub mod eval;
pub mod eval_term;
pub mod lower;
pub mod parser;
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
  load_module_from_text(&text, path.clone(), &mut loaded).map_err(|e| format!("{e}"))?;
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

pub fn run(input: PathBuf, args: Vec<String>, options: EvalOptions) -> Result<(), String> {
  let path: ModulePath = input.clone().into();
  let source = fs::read_to_string(&input).map_err(|e| format!("{e}"))?;
  let mut loaded = default_modules().map_err(|e| format!("{e}"))?;
  loaded.config.benchmark = options.benchmark;
  load_module_from_text(&source, path.clone(), &mut loaded).map_err(|e| format!("{e}"))?;
  let module = loaded
    .get_module(&path)
    .ok_or_else(|| format!("Module {path} not loaded"))?;
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
    let term = def.term.clone();

    let (term, typ) = match type_check(term, Hole, &global.scope()) {
      Ok(tt) => tt.to_tuple(),
      Err(e) => {
        failed += 1;
        failures.push((name.clone(), format!("type error: {e}")));
        continue;
      }
    };

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
