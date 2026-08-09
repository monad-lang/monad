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
#[cfg(feature = "repl")]
use crate::eval::r#type::type_check;
use crate::eval::{EvalOptions, eval, eval_test};
#[cfg(feature = "repl")]
use crate::parser::{ReplInput, repl_parser};
use crate::term::Decl;
#[cfg(feature = "repl")]
use crate::term::Term::Hole;
use crate::term::Term::{self, Con};
use crate::term::id;
#[cfg(feature = "repl")]
use crate::term::module::ParsedModule;
#[cfg(feature = "repl")]
use crate::term::module::module;
use crate::term::module::{
  LoadedModules, default_module_source_files, default_modules, load_module_files,
  load_module_from_text, module_warnings,
};
use crate::term::{
  Constructor, InductiveVariant, ModulePath, Named, SearchPaths, SourceContext, SourceRange, mpt,
};

pub mod core_check;
pub mod core_check_module;
pub mod core_eval;
pub mod core_ir;
pub mod core_native;
pub mod core_parity;
pub mod core_program;
pub mod core_term;
pub mod core_unify;
pub mod core_value;
pub mod diag;
pub mod eval;
pub mod lower_core;
pub mod lower_core_ir;
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

/// A `build_core_program` failure — kept as two variants rather than a
/// single `String` so callers that want nice, source-annotated
/// diagnostics for the common case (a real error in the user's own
/// program, `Check`) can still get them via `render_type_error_with_source`,
/// while the rarer "infrastructure" failures around it (a module
/// genuinely missing from disk, a cross-file def-name collision) fall
/// back to a plain message.
pub enum BuildCoreProgramError {
  /// Something went wrong assembling the capturing-check's module list
  /// itself, before `check_all_modules_capturing_core` ever ran (a
  /// `LoadingError`, a `load_decls` failure, this function's own
  /// cross-module collision check).
  Setup(String),
  /// `check_all_modules_capturing_core` itself failed — an ordinary
  /// type/syntax error in some module's own source, exactly the kind
  /// `render_type_error_with_source` already knows how to render nicely.
  Check(crate::eval::r#type::TypeError),
}

impl std::fmt::Display for BuildCoreProgramError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      BuildCoreProgramError::Setup(s) => write!(f, "{s}"),
      BuildCoreProgramError::Check(e) => write!(f, "{e}"),
    }
  }
}

/// Build ONE combined `CoreProgram` (Phase 0's `check_all_modules_
/// capturing_core`) covering the `init` package plus every OTHER module
/// `loaded` now knows about — the shared machinery both `run()` and
/// `run_tests()` need now that core-eval is the default evaluator (and
/// `eval_core_program`'s own, narrower single-module case below).
/// `loaded` must already have every module of interest loaded through
/// the ordinary (non-capturing) pipeline first — this function only
/// RE-READS each one's raw source text (`check_all_modules_capturing_core`
/// needs unchecked `Decl`s, not `loaded`'s own already-checked copies —
/// see that function's own doc comment) and re-checks it through the
/// capturing path; it never loads a NEW module `loaded` doesn't already
/// know about.
/// `extra_modules` covers callers that already have a module's raw
/// `Decl`s in hand from an IN-MEMORY source (`eval_core_program`'s own
/// `source: &str` parameter, or `run()`'s already-read target file) —
/// those never get re-read from disk (there may be no backing file to
/// find at all, e.g. every `eval_core_program` caller in the test suite
/// passes an inline string with no file on disk anywhere); every module
/// `loaded` knows about that ISN'T in `extra_modules` (or the `init`
/// package) IS re-read from disk, via search-path resolution, since
/// that's the only way to get an on-disk module's raw source back once
/// `loaded`'s own copy of it has already been checked/discarded.
fn build_core_program(
  loaded: &LoadedModules,
  extra_modules: &[(ModulePath, Vec<SourceContext<Decl>>)],
) -> Result<core_program::CoreProgram, BuildCoreProgramError> {
  let init_sources = term::module::init_package_sources()
    .map_err(|e| BuildCoreProgramError::Setup(format!("{e}")))?;
  let init_paths: Set<ModulePath> = init_sources.iter().map(|(p, _)| p.clone()).collect();
  let mut capture_modules: Vec<(ModulePath, Vec<SourceContext<Decl>>)> = init_sources
    .into_iter()
    .map(|(p, text)| {
      term::module::load_decls_from_text_with_path(&text, &Default::default())
        .map(|d| (p.clone(), d))
        .map_err(|e| BuildCoreProgramError::Setup(format!("parse {p}: {e}")))
    })
    .collect::<Result<Vec<_>, _>>()?;

  let extra_paths: Set<ModulePath> = extra_modules.iter().map(|(p, _)| p.clone()).collect();
  for module in loaded.modules() {
    let path = module.path().clone();
    if init_paths.contains(&path) || extra_paths.contains(&path) {
      continue;
    }
    let decls = term::module::load_decls(&path, loaded.search_paths()).map_err(|e| {
      BuildCoreProgramError::Setup(format!(
        "re-reading {path} for core-eval's capturing check: {e}"
      ))
    })?;
    capture_modules.push((path, decls));
  }
  capture_modules.extend(extra_modules.iter().cloned());

  // No cross-module bare-name collision check here anymore -- `CoreProgram`
  // (`core_program.rs`) used to key `defs`/`match_resolutions` by a def's
  // bare (non-module-qualified) name, which broke whenever two
  // INDEPENDENT modules declared the same bare name (confirmed for real:
  // `list_contains` in both `lang.module` and `string`; `main` itself,
  // in any two files each with their own entry point -- near-universal,
  // not a rare edge case). Fixed at the root in
  // `core_check_module.rs`'s `type_check_module_decls_new_inner`:
  // `capture_path` (this function's own capture key) and
  // `global_atom_paths`'s per-module override both now use each def's
  // full MODULE-qualified path, so two same-named-but-unrelated defs
  // get distinct keys and distinct lowered global slots regardless of
  // which order their modules happen to be checked in.
  core_check_module::check_all_modules_capturing_core(&capture_modules, loaded)
    .map_err(BuildCoreProgramError::Check)
}

/// A `Value`-shaped `List String` built from CLI `argv` — the
/// `core_value::Value` counterpart to `strings_to_list_term`, needed
/// because `main`'s CLI arguments are applied AFTER forcing it to a
/// `Value` (`run()`), not before type-checking the way the tree-walker
/// applies them to a `Term`.
fn strings_to_list_value(
  well_known: &lower_core_ir::WellKnownCtors,
  args: Vec<String>,
) -> Result<core_value::Value, String> {
  let empty = well_known
    .list_empty
    .ok_or_else(|| "List.empty not found (was the init package loaded?)".to_string())?;
  let cons = well_known
    .list_cons
    .ok_or_else(|| "List.cons not found (was the init package loaded?)".to_string())?;
  let mut result = core_value::Value::Con {
    tag: empty.tag,
    args: Vec::new(),
  };
  for s in args.into_iter().rev() {
    result = core_value::Value::Con {
      tag: cons.tag,
      args: vec![core_value::Value::Lit(core_ir::IrLit::Str(s)), result],
    };
  }
  Ok(result)
}

/// Evaluate a source module's `main` def through the `CoreTerm`-closure
/// evaluator (`build_core_program` (Phase 0) -> `lower_core_ir::
/// lower_program` (Phase 2) -> `core_eval::force_global` (Phases 3-5)).
///
/// Unlike the tree-walker's `eval()` (which walks an already-checked
/// `Term` produced by the OLD checker path against a `Scope`), this
/// rebuilds a whole-program `CoreProgram` from scratch every call: the
/// capturing checker needs every module's raw, unchecked `Decl`s run
/// back through the NEW capturing checker — including the `init` package
/// itself, since `default_modules()`'s own already-checked copy of it
/// (used here purely for name/scope resolution) never populates a
/// `CoreProgram` on its own.
/// `insert_checked_def` (`core_check_module.rs`) stores every def under
/// BOTH its bare AND its module-qualified path — but only the qualified
/// form (`path`'s own `main`, not bare `main`) is GUARANTEED to be
/// *this* file's own `main` rather than some other loaded module's
/// same-named one (the bare slot is whichever module's `main` happened
/// to be checked last, when more than one exists) — since callers here
/// always know exactly which file's `main` they want, always ask for it
/// by its own qualified path.
fn find_main_def<'a>(
  program: &'a core_program::CoreProgram,
  path: &ModulePath,
) -> Option<&'a core_program::CheckedCoreDef> {
  program.defs.get(&path.clone().extend(mpt("main")))
}

fn main_index(lowered: &lower_core_ir::LoweredProgram, path: &ModulePath) -> Option<u32> {
  lowered.index_of(&path.clone().extend(mpt("main")))
}

pub fn eval_core_program(path: &ModulePath, source: &str) -> Result<core_value::Value, String> {
  let mut loaded = default_modules().map_err(|e| format!("{e}"))?;
  // The ordinary (non-capturing) load is still needed here, even though
  // `source`'s own decls are passed to `build_core_program` explicitly
  // below (never re-read from disk — there may be no file backing
  // `source` at all, e.g. every caller in this crate's own test suite
  // passes an inline string) — this is what actually RESOLVES and loads
  // any module `source` itself transitively `use`s, so `build_core_
  // program`'s generic `loaded.modules()` scan can find and re-read
  // those (see its own doc comment).
  load_module_from_text(source, path, &mut loaded).map_err(|e| format!("{e}"))?;
  let decls = term::module::load_decls_from_text_with_path(source, &Default::default())
    .map_err(|e| format!("parse {path}: {e}"))?;

  let program =
    build_core_program(&loaded, &[(path.clone(), decls)]).map_err(|e| format!("{e}"))?;
  let lowered = lower_core_ir::lower_program(&program).map_err(|e| format!("lower: {e:?}"))?;
  let main_idx = main_index(&lowered, path).ok_or_else(|| "main not found".to_string())?;
  let natives = core_value::NativeTable::from_lowered(&lowered);
  let globals = core_value::GlobalTable::new(lowered.globals);
  let mut cache = core_value::GlobalCache::new(globals.len());
  core_eval::force_global(main_idx, &globals, &natives, &mut cache)
    .map_err(|e| format!("eval: {e}"))
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

  let decls = term::module::load_decls_from_text_with_path(&source, &Default::default())
    .map_err(|e| format!("parse {path}: {e}"))?;
  let program = build_core_program(&loaded, &[(path.clone(), decls)]).map_err(|e| match e {
    BuildCoreProgramError::Check(e) => {
      render_type_error_with_source(&source, &e, options.use_colors, Some(&input))
    }
    BuildCoreProgramError::Setup(s) => s,
  })?;
  // `CoreTerm`'s own `Display` renders an unresolved `Free(Atom)` as a
  // bare `@{id}` (it carries no name table of its own) -- raise the
  // type back to an ordinary `Term` first, purely for THIS display (not
  // for evaluation), using this def's own captured `atom_paths` to
  // resolve every atom back to a real, readable name the same way
  // `check_one_def_new` already does when raising a def's checked body.
  let main_typ = find_main_def(&program, &path)
    .map(|d| raise_core::raise_core(&d.typ, &d.atom_paths).to_string())
    .unwrap_or_else(|| "?".to_string());
  println!("Eval type {main_typ}");

  let lowered = lower_core_ir::lower_program(&program).map_err(|e| format!("lower: {e:?}"))?;
  let main_idx = main_index(&lowered, &path).ok_or("main not found")?;
  let natives = core_value::NativeTable::from_lowered(&lowered);
  let globals = core_value::GlobalTable::new(lowered.globals);
  let mut cache = core_value::GlobalCache::new(globals.len());
  let main_value = core_eval::force_global(main_idx, &globals, &natives, &mut cache)
    .map_err(|e| format!("{e}"))
    .inspect_err(|e| eprintln!("{e}"))?;

  // Apply CLI args only if `main` is actually a function -- mirrors the
  // tree-walker's own `if def.term.is_lam() { app(...) } else { ... }`
  // check, just against the FORCED runtime `Value` instead of the
  // pre-eval `Term` (a `Value::Closure` is exactly what a `Lam`-headed
  // `main` forces to).
  let result = if let core_value::Value::Closure { .. } = &main_value {
    let arg = strings_to_list_value(&natives.well_known, args)?;
    core_eval::apply(main_value, arg, &globals, &natives, &mut cache)
      .map_err(|e| format!("{e}"))
      .inspect_err(|e| eprintln!("{e}"))?
  } else {
    main_value
  };

  if options.debug {
    println!("Eval result {result:?}");
  }
  Ok(())
}

pub fn vec_fmt<T: Display>(v: &[T]) -> String {
  v.iter()
    .map(|t| format!("{t}"))
    .collect::<Vec<String>>()
    .join(", ")
}

/// True when `file` is literally one of the on-disk source files backing an
/// embedded default module (`init/prelude.mo`, `init/string.mo`, etc.) —
/// compares canonicalized paths, not module-path names, so a file that
/// merely shares a *name* with a default module (e.g. `lang/parser/
/// number.mo` vs. the top-level `number` default) is never mistaken for
/// it. Used to skip re-checking/re-testing files that `default_modules()`
/// already loaded, without false-positiving on unrelated same-named files.
fn is_default_module_file(file: &Path) -> bool {
  let Ok(canon) = file.canonicalize() else {
    return false;
  };
  default_module_source_files().contains(&canon)
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

/// The `core_value::Value` counterpart to `detect_test_result` — same
/// `Bool`/`IO`/`Result` unwrapping convention, reading well-known
/// constructor *tags* (resolved once per test run, via `NativeTable::
/// well_known`) instead of a `Term::Con`'s own `typ_name` field, since a
/// runtime `Value::Con` carries no type name at all (see
/// `lower_core_ir::WellKnownCtors`'s own doc comment for why). Shares
/// `TestResult` with the tree-walker's own version so both evaluators'
/// results print through the exact same PASS/FAIL/message formatting
/// below — nothing downstream needs to know or care which evaluator
/// actually produced a given `TestResult`.
fn detect_test_result_value(
  value: &core_value::Value,
  well_known: &lower_core_ir::WellKnownCtors,
) -> TestResult {
  match value {
    core_value::Value::Con { tag, args } => {
      if well_known.bool_true.is_some_and(|t| t.tag == *tag) {
        TestResult::Pass
      } else if well_known.bool_false.is_some_and(|t| t.tag == *tag) {
        TestResult::Fail
      } else if well_known.io_io.is_some_and(|t| t.tag == *tag) {
        match args.first() {
          Some(inner) => detect_test_result_value(inner, well_known),
          None => TestResult::FailWithMessage(format!("unexpected result: {value:?}")),
        }
      } else if well_known.result_ok.is_some_and(|t| t.tag == *tag) {
        TestResult::Pass
      } else if well_known.result_err.is_some_and(|t| t.tag == *tag) {
        let msg = args.first().and_then(|v| match v {
          core_value::Value::Lit(core_ir::IrLit::Str(s)) => Some(s.clone()),
          _ => None,
        });
        TestResult::FailWithMessage(msg.unwrap_or_else(|| format!("{value:?}")))
      } else {
        TestResult::FailWithMessage(format!("unexpected result: {value:?}"))
      }
    }
    other => TestResult::FailWithMessage(format!("unexpected result: {other:?}")),
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

/// Tree-walker-specific test evaluation, kept solely for
/// `core_parity.rs`'s Phase 8 harness — it deliberately runs BOTH the
/// tree-walker and core-eval over the same corpus and diffs their
/// results, so the tree-walker side still needs its own entry point
/// even now that `run_tests` itself no longer uses it.
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

/// `force_global`, but bailing out after `timeout` instead of blocking
/// forever — core-eval has no equivalent of the tree-walker's own
/// `eval_test`/`eval_inner`'s cooperative per-step deadline check (that
/// would mean threading a deadline through every recursive call in
/// `core_eval.rs`), so this wraps the SAME call in a plain OS thread +
/// channel instead: a generic, evaluator-agnostic timeout, at the cost
/// of a real (if minor) one-thread-per-timed-call overhead, and a
/// runaway call that times out CONTINUES running in its own thread in
/// the background rather than actually stopping (Rust has no safe way
/// to force-kill a thread) — acceptable for a CLI test runner that's
/// about to exit once the whole suite finishes anyway, unlike a
/// long-lived server that would need to actually reclaim the thread.
/// `globals`/`natives` are `Arc`-wrapped (not plain refs) specifically
/// so they can be moved into the spawned thread without needing it to
/// borrow from (and therefore block) the calling scope.
fn force_global_with_timeout(
  idx: u32,
  globals: Arc<core_value::GlobalTable>,
  natives: Arc<core_value::NativeTable>,
  timeout: std::time::Duration,
) -> Result<core_value::Value, String> {
  let (tx, rx) = std::sync::mpsc::channel();
  std::thread::Builder::new()
    .stack_size(8 * 1024 * 1024)
    .spawn(move || {
      let mut cache = core_value::GlobalCache::new(globals.len());
      let result = core_eval::force_global(idx, &globals, &natives, &mut cache);
      // A send failure just means the receiver already gave up and
      // stopped listening (the timeout already fired) -- this thread is
      // about to exit either way, nothing to do about it.
      let _ = tx.send(result.map_err(|e| format!("{e}")));
    })
    .expect("failed to spawn eval thread");
  rx.recv_timeout(timeout)
    .unwrap_or_else(|_| Err(format!("timed out after {timeout:?}")))
}

/// Load, capturing-check, lower, and evaluate every `#[test]` def in one
/// file, entirely in isolation from every OTHER test file in the run.
///
/// This isolation is deliberate, not incidental: `build_core_program`'s
/// `CoreProgram` keys every top-level def by its bare (non-module-
/// qualified) name across every module handed to it AT ONCE (see its
/// own doc comment) — fine for `init` plus exactly one file (`run()`,
/// `eval_core_program`), but genuinely unsafe across an arbitrary batch
/// of test files, which (confirmed against the real corpus — two
/// distinct `init` test files, `foldable_tests.mo` and
/// `foldable_tests_fold.mo`, both declare a `#[test] def
/// test_foldr_sum`) have no reason to avoid reusing each other's names.
/// The tree-walker never combined separate files into one keyed table,
/// so this was never a collision before core-eval became the default.
/// Cloning a FIXED `base_loaded` (the state before ANY test file is
/// loaded) fresh for every file, rather than accumulating `loaded`
/// across files the way the old tree-walker runner did, is what
/// preserves that guarantee: no test file's module is ever visible to
/// another file's own capturing check, matching the tree-walker's own
/// per-file independence exactly (just against a faster evaluator).
fn evaluate_one_test_file(
  file: &Path,
  base_loaded: &LoadedModules,
  options: &EvalOptions,
  test_timeout: Option<std::time::Duration>,
  file_index: usize,
  total_files: usize,
) -> FileOutput {
  let file_path = file.to_path_buf();
  let path: ModulePath = file_path.clone().into();

  println!(
    "{YELLOW}[{}/{}] Testing {}...{RESET}",
    file_index + 1,
    total_files,
    file_path.display()
  );

  macro_rules! fail_file {
    ($msg:expr) => {
      return FileOutput {
        passed: 0,
        failed: 1,
        output_lines: vec![format!("{RED}FAIL{RESET} {}", file_path.display())],
        error_message: Some($msg),
        failures: Vec::new(),
      }
    };
  }

  let source = match fs::read_to_string(&file_path) {
    Ok(s) => s,
    Err(e) => fail_file!(format!("failed to read {}: {e}", file_path.display())),
  };

  let mut loaded = base_loaded.clone();
  if let Err(e) = load_module_from_text(&source, &path, &mut loaded) {
    fail_file!(format!("failed to compile {}: {e}", file_path.display()));
  }

  let module = match loaded.get_module(&path) {
    Some(m) => m,
    None => {
      return FileOutput {
        passed: 0,
        failed: 0,
        output_lines: Vec::new(),
        error_message: None,
        failures: Vec::new(),
      };
    }
  };

  if options.debug {
    let loaded_scopes = loaded.scopes();
    let global = loaded_scopes.global(&path).expect("Module not loaded");
    println!("{global}");
  }

  let warnings = module_warnings(module, Some(&file_path));
  if !warnings.is_empty() {
    println!(
      "{}",
      render_diagnostics(&warnings, None, options.use_colors)
    );
  }

  let entries: Vec<(ModulePath, String)> = module
    .defs()
    .into_iter()
    .filter(|ctx| ctx.value().has_test_attr())
    .map(|ctx| {
      let def = ctx.value();
      // Bare, matching `CoreProgram.defs`'/`lowered`'s own DEFAULT
      // (non-colliding) capture key -- the later `lowered.index_of`
      // lookup falls back to `path`-qualified only if this test's own
      // name happened to collide with some OTHER loaded module's own
      // def of the same name (see `core_check_module.rs`'s
      // `capture_path_for`). Display name (second element) stays bare
      // either way, for PASS/FAIL output.
      (def.name.clone(), def.name.to_string())
    })
    .collect();

  if entries.is_empty() {
    return FileOutput {
      passed: 0,
      failed: 0,
      output_lines: Vec::new(),
      error_message: None,
      failures: Vec::new(),
    };
  }

  let decls = match term::module::load_decls_from_text_with_path(&source, &Default::default()) {
    Ok(d) => d,
    Err(e) => fail_file!(format!("parse {}: {e}", file_path.display())),
  };
  let program = match build_core_program(&loaded, &[(path.clone(), decls)]) {
    Ok(p) => p,
    Err(e) => fail_file!(format!("{e}")),
  };
  let lowered = match lower_core_ir::lower_program(&program) {
    Ok(l) => l,
    Err(e) => fail_file!(format!("lower {}: {e:?}", file_path.display())),
  };

  // `NativeTable::from_lowered` only borrows `lowered` -- computed before
  // `lowered.globals` is moved out below.
  let natives = Arc::new(core_value::NativeTable::from_lowered(&lowered));
  let globals = Arc::new(core_value::GlobalTable::new(lowered.globals.clone()));
  let mut cache = core_value::GlobalCache::new(globals.len());

  let mut output_lines: Vec<String> = Vec::new();
  let mut passed = 0;
  let mut failed = 0;
  let mut failures: Vec<(String, String)> = Vec::new();

  for (test_path, name) in &entries {
    let start = Instant::now();
    // Qualified by `path` (this test file's own module) -- the bare
    // slot could belong to some OTHER loaded module's same-named def
    // instead, if one exists (see `insert_checked_def`'s own doc
    // comment); the qualified one is always THIS file's own.
    let idx = lowered.index_of(&path.clone().extend(test_path.clone()));
    let result = match idx {
      None => Err("not present in the lowered program (skipped)".to_string()),
      Some(idx) => match test_timeout {
        Some(timeout) => {
          force_global_with_timeout(idx, Arc::clone(&globals), Arc::clone(&natives), timeout)
        }
        None => {
          core_eval::force_global(idx, &globals, &natives, &mut cache).map_err(|e| format!("{e}"))
        }
      },
    };
    let duration = start.elapsed();
    let duration_str = format_duration(duration);

    let value = match result {
      Ok(v) => v,
      Err(e) => {
        failed += 1;
        failures.push((name.clone(), format!("eval error: {e}")));
        continue;
      }
    };

    if options.debug {
      output_lines.push(format!("  eval: {value:?}"));
    }

    match detect_test_result_value(&value, &natives.well_known) {
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

  FileOutput {
    passed,
    failed,
    output_lines,
    error_message: None,
    failures,
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
      let is_default = master_loaded.get_module(&path).is_some() || is_default_module_file(file);
      !is_default
    })
    .collect();

  let mut total_passed = 0;
  let mut total_failed = 0;
  let mut overall_errors: Vec<String> = Vec::new();
  let total = files.len();

  // `master_loaded` is never mutated after this point -- every file
  // clones it fresh (inside `evaluate_one_test_file`), which is exactly
  // what keeps files independent of each other (see that function's own
  // doc comment). Single-threaded and multi-threaded dispatch below
  // differ only in scheduling, not in this isolation guarantee.
  if num_threads <= 1 || files.len() <= 1 {
    for (i, file) in files.iter().enumerate() {
      let output = evaluate_one_test_file(file, &master_loaded, &options, test_timeout, i, total);
      print_file_output(&output);
      total_passed += output.passed;
      total_failed += output.failed;
      if let Some(ref err) = output.error_message {
        eprintln!("  {err}");
        overall_errors.push(err.clone());
      }
    }
  } else {
    let n_threads = std::cmp::min(num_threads, files.len());
    let chunk_size = files.len().div_ceil(n_threads);

    let passed_counter = Arc::new(AtomicUsize::new(0));
    let failed_counter = Arc::new(AtomicUsize::new(0));
    let overall_errors_shared: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));

    let mut handles = Vec::with_capacity(n_threads);
    for (chunk_idx, chunk) in files.chunks(chunk_size).enumerate() {
      let chunk_files: Vec<PathBuf> = chunk.to_vec();
      let base_loaded = master_loaded.clone();
      let opts = options.clone();
      let passed = Arc::clone(&passed_counter);
      let failed = Arc::clone(&failed_counter);
      let errors = Arc::clone(&overall_errors_shared);
      let base_idx = chunk_idx * chunk_size;

      let handle = std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || {
          for (i, file) in chunk_files.iter().enumerate() {
            let output =
              evaluate_one_test_file(file, &base_loaded, &opts, test_timeout, base_idx + i, total);
            print_file_output(&output);
            passed.fetch_add(output.passed, Ordering::Relaxed);
            failed.fetch_add(output.failed, Ordering::Relaxed);
            if let Some(err) = output.error_message {
              eprintln!("  {err}");
              errors.lock().unwrap().push(err);
            }
          }
        })
        .expect("failed to spawn test thread");
      handles.push(handle);
    }
    for handle in handles {
      handle.join().expect("test thread panicked");
    }

    total_passed += passed_counter.load(Ordering::Relaxed);
    total_failed += failed_counter.load(Ordering::Relaxed);
    overall_errors.extend(
      Arc::try_unwrap(overall_errors_shared)
        .unwrap()
        .into_inner()
        .unwrap(),
    );
  }

  print_final_summary(total_passed, total_failed, &overall_errors)
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
      let is_default = master_loaded.get_module(&path).is_some() || is_default_module_file(file);
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
      let is_default = master_loaded.get_module(&path).is_some() || is_default_module_file(file);
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
      let is_default = master_loaded.get_module(&path).is_some() || is_default_module_file(file);
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

  /// `eval_core_program` (Phase 6 of
  /// `plans/implementations/core-term-closure-evaluator.md`) end-to-end,
  /// via the public API rather than hand-assembling the pipeline (see
  /// `core_eval_native_integration_test.rs`'s own `run()` helper, which
  /// this mirrors internally).
  #[test]
  fn eval_core_program_evaluates_real_arithmetic_end_to_end() {
    let source = r#"
use init

@[terminating]
def fib (n : I64) : I64 :=
    if n == 0
    then 0
    else if n == 1
    then 1
    else (fib (n - 1)) + (fib (n - 2))

def main : I64 := fib 10
"#;
    let result = eval_core_program(&ModulePath::top("'eval_core_program_test"), source)
      .unwrap_or_else(|e| panic!("eval_core_program failed: {e}"));
    match result {
      core_value::Value::Lit(core_ir::IrLit::Num(n, _)) => assert_eq!(n, 55),
      other => panic!("expected an int literal, got {other:?}"),
    }
  }
}
