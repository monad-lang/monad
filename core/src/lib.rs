use std::collections::{BTreeMap, HashSet};
use std::fmt::Display;
use std::fs;
use std::hash::{BuildHasherDefault, DefaultHasher, Hash};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use crate::diag::render_diagnostics;
use crate::eval::EvalOptions;
use crate::eval::r#type::render_type_error_with_source;
#[cfg(feature = "repl")]
use crate::parser::{ReplInput, repl_parser};
use crate::term::Decl;
// Unused by the lib itself when `repl` is off (only `eval_repl_term` refers
// to it bare), but still needed unqualified by `mod test`'s `use super::*`
// regression test below -- cfg-gating this import would break that test's
// compilation under a `repl`-less `cargo test`.
#[cfg_attr(not(feature = "repl"), allow(unused_imports))]
use crate::term::Term;
#[cfg(feature = "repl")]
use crate::term::Term::Hole;
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
  InductiveVariant, ModulePath, Named, SearchPaths, SourceContext, SourceRange, mpt,
};

pub mod core_check;
pub mod core_check_module;
pub mod core_eval;
pub mod core_ir;
pub mod core_native;
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
pub mod shared_str;
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

/// Reverse `Atom -> ModulePath` lookup, used by `raise_core` (and its
/// callers) to turn a checker-internal `Free(Atom)` occurrence back into a
/// durable global/local name. Deliberately NOT `Map<Atom, ModulePath>`
/// (plain `BTreeMap`): `core_check_module.rs`'s `global_atom_paths` is
/// built once per module (covering every global loaded so far, i.e.
/// growing toward whole-corpus size) and then cloned-and-extended once per
/// checked `def`/instance method -- thousands of times across the self-
/// hosted corpus. A `BTreeMap` here made every one of those clones a full
/// O(corpus size) copy (confirmed via profiling to dominate
/// `test_typecheck_lang_main`'s ~7-minute cost, the same "gets worse as
/// the corpus grows" shape as the `LoadedModules` clone-per-file bug fixed
/// in `core/src/term/module.rs` -- see that type's own doc comment).
/// `im::OrdMap` is structurally-shared (ref-counted internally), so
/// `.clone()` is O(1) and the subsequent `.insert`/`.extend` calls are
/// O(log n) persistent updates instead of full copies, with an API
/// (`.get`/`.contains_key`/`.insert`/`.extend`/iteration-by-key-order)
/// close enough to `BTreeMap`'s to be a drop-in replacement at every
/// existing call site. Scoped to exactly this one type family rather than
/// changing the general-purpose `Map<K, V>` alias above, which is used
/// pervasively for unrelated tables that are never cloned per-def and
/// have no equivalent hot-path pressure.
pub type AtomPathMap = im::OrdMap<crate::core_term::Atom, ModulePath>;

/// A `Value`, formatted for REPL display. `core_value::Value` has no
/// `Display` of its own (see its own doc comment: it's deliberately kept
/// separate from `CoreTerm`, and a *reduced* value's constructors/
/// closures carry no name table to render with — see `raise_core`, which
/// only knows how to raise a checker-time `CoreTerm`, not a runtime
/// `Value`). A `Lit` still prints its real content (numbers/strings/etc,
/// via `IrLit`'s own `Display`); anything else (a constructor, a still-
/// partial closure/native) falls back to `Debug`, which is honest about
/// showing raw tags/slots rather than pretending to a fidelity this
/// function can't deliver without a whole name-resolving value-printer.
#[cfg(feature = "repl")]
fn format_repl_value(value: &core_value::Value) -> String {
  match value {
    core_value::Value::Lit(lit) => format!("{lit}"),
    other => format!("{other:?}"),
  }
}

/// Evaluate one REPL-entered term against everything accumulated in
/// `repl_decls` so far, through the same `CoreTerm`-closure pipeline
/// `run()` uses for a whole file — see `build_core_program`'s own doc
/// comment. Wraps `term` in a synthetic, `Hole`-typed `def` (so the
/// checker infers its type rather than requiring the user to annotate
/// every REPL expression) appended to a throwaway copy of `repl_decls`,
/// rather than mutating `repl_decls` itself — a bare expression is not a
/// declaration and must not persist into later inputs the way an actual
/// `def`/`type`/... entered at the prompt does.
#[cfg(feature = "repl")]
fn eval_repl_term(
  loaded: &LoadedModules,
  module_path: &ModulePath,
  repl_decls: &[SourceContext<Decl>],
  term: Term,
  options: &EvalOptions,
) -> Result<(), String> {
  let tmp_name = mpt("__repl_result");
  let tmp_decl = SourceContext::no_ctx(Decl::Def(crate::term::def(
    tmp_name.clone(),
    vec![],
    Hole,
    term,
    vec![],
  )));
  let mut extra_decls = repl_decls.to_vec();
  extra_decls.push(tmp_decl);

  let full_path = module_path.extend_borrowed(&mpt("__repl_result"));
  let program = build_core_program(loaded, &[(module_path.clone(), extra_decls)])
    .map_err(|e| format!("Type error: {e}"))?;
  let Some(checked) = program.defs.get(&full_path) else {
    return Err("Type error: __repl_result not found after check".to_string());
  };
  if options.debug {
    let typ = raise_core::raise_core(&checked.typ, &checked.atom_paths);
    println!("Eval type {typ}");
  }
  let lowered = lower_core_ir::lower_program(&program).map_err(|e| format!("lower: {e:?}"))?;
  let idx = lowered
    .index_of(&full_path)
    .ok_or_else(|| "__repl_result not found in lowered program".to_string())?;
  let natives = core_value::NativeTable::from_lowered(&lowered);
  let globals = core_value::GlobalTable::new(lowered.globals);
  let mut cache = core_value::GlobalCache::new(globals.len());
  let value =
    core_eval::force_global(idx, &globals, &natives, &mut cache).map_err(|e| format!("{e}"))?;
  println!("{}", format_repl_value(&value));
  Ok(())
}

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
  // Every non-`use` decl entered at the prompt so far — threaded into
  // `eval_repl_term`'s own capturing check as `extra_modules` alongside
  // the `init` package (see `build_core_program`), since a synthetic
  // `'repl` module has no on-disk file `build_core_program` could
  // otherwise re-read.
  let mut repl_decls: Vec<SourceContext<Decl>> = vec![];
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
                if let Err(e) =
                  eval_repl_term(&loaded_modules, &module_path, &repl_decls, term, &options)
                {
                  eprintln!("{e}");
                }
              }
              ReplInput::Decls(Decl::Use(u)) => {
                if loaded_modules.get_module(&u.module_path).is_none() {
                  let loaded = loaded_modules.clone();
                  match load_module_files(&u.module_path, loaded) {
                    Ok(loaded) => {
                      if options.debug {
                        for module in loaded.modules() {
                          println!("Adding module {} to scope", module.path());
                        }
                      }
                      loaded_modules = loaded;
                    }
                    Err(e) => eprintln!("loading error {e}"),
                  }
                }
                repl_decls.push(SourceContext::no_ctx(Decl::Use(u)));
              }
              ReplInput::Decls(decl) => {
                loaded_modules
                  .get_module_mut(&module_path)
                  .unwrap()
                  .add_decl(decl.clone());
                repl_decls.push(SourceContext::no_ctx(decl));
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
pub(crate) fn build_core_program(
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
    args: std::sync::Arc::new(Vec::new().into()),
  };
  for s in args.into_iter().rev() {
    result = core_value::Value::Con {
      tag: cons.tag,
      args: std::sync::Arc::new(
        vec![
          core_value::Value::Lit(core_ir::IrLit::Str(s.into())),
          result,
        ]
        .into(),
      ),
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
  program.defs.get(&path.extend_borrowed(&mpt("main")))
}

fn main_index(lowered: &lower_core_ir::LoweredProgram, path: &ModulePath) -> Option<u32> {
  lowered.index_of(&path.extend_borrowed(&mpt("main")))
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

  // `core_eval`'s own recursion depth can exceed the OS default
  // main-thread stack (commonly 8MB on Linux, see `ulimit -s`) for
  // large/deeply-nested programs -- e.g. self-hosted-checking
  // `lang/main.mo` (whose dependency closure pulls in `lang/parser.mo`
  // at 5,563 lines) reliably stack-overflows here, at a consistent
  // wall-clock point regardless of `RUST_MIN_STACK`, since that only
  // affects threads spawned with an explicit `stack_size` -- never the
  // main thread. `run_tests()`'s own evaluation paths
  // (`force_global_with_timeout`, the parallel test-file workers) both
  // already spawn a 64MB-stack thread for exactly this reason; `run()`'s
  // single-shot eval never did. Match that existing precedent here.
  let eval_result: Result<(), String> = std::thread::Builder::new()
    .stack_size(64 * 1024 * 1024)
    .spawn(move || {
      let natives = core_value::NativeTable::from_lowered(&lowered);
      let globals = core_value::GlobalTable::new(lowered.globals);
      let mut cache = core_value::GlobalCache::new(globals.len());
      let main_value = core_eval::force_global(main_idx, &globals, &natives, &mut cache)
        .map_err(|e| format!("{e}"))
        .inspect_err(|e| eprintln!("{e}"))?;

      // Apply CLI args only if `main` is actually a function -- mirrors
      // the tree-walker's own `if def.term.is_lam() { app(...) } else {
      // ... }` check, just against the FORCED runtime `Value` instead of
      // the pre-eval `Term` (a `Value::Closure` is exactly what a
      // `Lam`-headed `main` forces to).
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
    })
    .map_err(|e| format!("failed to spawn eval thread: {e}"))?
    .join()
    .map_err(|_| "eval thread panicked".to_string())?;
  eval_result
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

/// Reads well-known constructor *tags* (resolved once per test run, via
/// `NativeTable::well_known`) to unwrap `Bool`/`IO`/`Result` values —
/// used to be paired with a `Term`-level twin (`detect_test_result`,
/// walking a `Term::Con`'s own `typ_name` field) for the tree-walking
/// evaluator, removed along with it (see `core-term-closure-evaluator.md`
/// — a runtime `Value::Con` carries no type name at all, only a tag, so
/// the two were never quite the same shape to begin with).
fn detect_test_result_value(
  value: &core_value::Value,
  well_known: &lower_core_ir::WellKnownCtors,
) -> TestResult {
  match value {
    core_value::Value::Con { tag, args } => {
      // `CtorTag.tag` (`lower_core_ir.rs`'s `find_ctor`) is a PER-
      // INDUCTIVE-LOCAL constructor index (0 for a type's first
      // constructor, 1 for its second, ...), not a globally unique
      // discriminator — so comparing a bare `tag` alone across
      // DIFFERENT well-known types is genuinely ambiguous: `IO A`'s
      // sole constructor (`io_io`) and `Bool`'s `true` (`bool_true`)
      // are BOTH each their own type's first constructor, so both have
      // `tag == 0`. This function used to check `bool_true`/
      // `bool_false` BEFORE `io_io`, so an `IO Bool` test's own OUTER
      // `IO.io` wrapper (tag 0) matched `bool_true` immediately and was
      // reported Pass unconditionally — CONFIRMED via a direct repro:
      // `#[test] def t : IO Bool := IO.io false` (no exec_cmd/native
      // calls involved at all) reported PASS. This silently made every
      // `IO`-typed compile-and-run e2e test in this codebase (any test
      // asserting `exec_result == expected` via `return (exec_result ==
      // expected)`) pass regardless of the actual assertion — a real,
      // separate, and serious gap, found while validating the
      // dictionary-passing plan's own e2e tests
      // (lang/codegen/test/compile_tests.mo).
      //
      // Fixed by checking `io_io` FIRST (an `IO`-wrapped value must
      // always be unwrapped before its own payload's pass/fail meaning
      // can be judged, regardless of what tag its wrapper happens to
      // share with some other type's own leaf constructor) and by
      // comparing `arity` alongside `tag` everywhere (`args.len()` vs
      // `t.arity`) as a second discriminator — cheaply rules out most
      // OTHER same-tag cross-type pairs (e.g. `bool_true`'s arity 0
      // vs `io_io`'s arity 1) without needing `Value::Con` to carry its
      // own owning-type identity, a larger change out of scope here.
      // Does NOT fully resolve every possible collision on its own
      // (`io_io` and `result_ok` are both their type's first
      // constructor AND both carry exactly one payload arg — tag 0,
      // arity 1, identical on both axes — only the ordering below saves
      // that specific pair, by construction: `io_io` is checked, and
      // therefore unwrapped, before `result_ok` is ever considered) —
      // a fully robust fix needs `Value::Con` to carry real type
      // identity, a separate, larger change.
      if well_known
        .io_io
        .is_some_and(|t| t.tag == *tag && t.arity == args.len() as u32)
      {
        match args.first() {
          Some(inner) => detect_test_result_value(inner, well_known),
          None => TestResult::FailWithMessage(format!("unexpected result: {value:?}")),
        }
      } else if well_known
        .bool_true
        .is_some_and(|t| t.tag == *tag && t.arity == args.len() as u32)
      {
        TestResult::Pass
      } else if well_known
        .bool_false
        .is_some_and(|t| t.tag == *tag && t.arity == args.len() as u32)
      {
        TestResult::Fail
      } else if well_known
        .result_ok
        .is_some_and(|t| t.tag == *tag && t.arity == args.len() as u32)
      {
        TestResult::Pass
      } else if well_known
        .result_err
        .is_some_and(|t| t.tag == *tag && t.arity == args.len() as u32)
      {
        let msg = args.first().and_then(|v| match v {
          core_value::Value::Lit(core_ir::IrLit::Str(s)) => Some(s.as_str().to_string()),
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

/// Outcome of evaluating one `#[test]`-attributed def — the public,
/// every-test-not-just-failures counterpart of the private `TestResult`
/// enum `detect_test_result_value` above produces. Kept as a separate
/// type (rather than reusing `TestResult` itself) so `TestResult` stays
/// free to remain private/printing-oriented while this one is part of
/// `run_tests_for_files`'s public, structured result.
#[derive(Debug, Clone)]
pub enum TestOutcome {
  Pass,
  Fail,
  FailWithMessage(String),
}

/// One `#[test]` def's result: name, outcome, wall time, and its own
/// declaration-level location — captured from the same
/// `SourceContext<Def>` `evaluate_one_test_file` already iterates over
/// (see its `entries` computation below), not a second lookup. The
/// location is what lets an LSP caller place a failure's diagnostic at
/// the right spot without re-deriving it from a separate symbol scan.
#[derive(Debug, Clone)]
pub struct TestCaseResult {
  pub name: Arc<str>,
  pub outcome: TestOutcome,
  pub duration: std::time::Duration,
  pub location: Option<SourceRange>,
}

/// One file's structured test result — the `run_tests_for_files`
/// counterpart of `FileCheckResult`. `tests` is empty whenever
/// `error_message` is `Some`: a file that failed to read/parse/compile
/// never got to run any of its `#[test]` defs, mirroring `FileOutput`'s
/// own `fail_file!` semantics below.
#[derive(Debug, Clone)]
pub struct FileTestResult {
  pub path: PathBuf,
  pub tests: Vec<TestCaseResult>,
  pub error_message: Option<String>,
}

#[derive(Debug)]
struct FileOutput {
  path: PathBuf,
  passed: usize,
  failed: usize,
  output_lines: Vec<String>,
  error_message: Option<String>,
  failures: Vec<(String, String)>,
  tests: Vec<TestCaseResult>,
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
    .stack_size(64 * 1024 * 1024)
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
/// `quiet`: suppresses every `println!` this function would otherwise do
/// (the progress line, the `options.debug` scope dump, and the rendered
/// warnings) — required whenever the caller's stdout IS a protocol
/// stream (MCP's newline-delimited JSON-RPC, LSP's `Content-Length`-
/// framed JSON-RPC), where any stray text corrupts the stream rather
/// than just looking ugly. `run_tests`'s own printing CLI path passes
/// `quiet: false` and is unaffected; `run_tests_for_files` always passes
/// `quiet: true`.
///
/// `test_name_filter`: `Some(name)` restricts evaluation to the
/// `#[test]` def with that bare name (used by the LSP's per-test
/// `monad.runTest` command so a single test can be re-run without paying
/// for the whole file); `None` runs every `#[test]` def found, matching
/// this function's original behavior.
fn evaluate_one_test_file(
  file: &Path,
  base_loaded: &LoadedModules,
  options: &EvalOptions,
  test_timeout: Option<std::time::Duration>,
  file_index: usize,
  total_files: usize,
  test_name_filter: Option<&str>,
  quiet: bool,
) -> FileOutput {
  let file_path = file.to_path_buf();
  let path: ModulePath = file_path.clone().into();

  if !quiet {
    println!(
      "{YELLOW}[{}/{}] Testing {}...{RESET}",
      file_index + 1,
      total_files,
      file_path.display()
    );
  }

  macro_rules! fail_file {
    ($msg:expr) => {
      return FileOutput {
        path: file_path.clone(),
        passed: 0,
        failed: 1,
        output_lines: vec![format!("{RED}FAIL{RESET} {}", file_path.display())],
        error_message: Some($msg),
        failures: Vec::new(),
        tests: Vec::new(),
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
        path: file_path.clone(),
        passed: 0,
        failed: 0,
        output_lines: Vec::new(),
        error_message: None,
        failures: Vec::new(),
        tests: Vec::new(),
      };
    }
  };

  if options.debug && !quiet {
    let loaded_scopes = loaded.scopes();
    let global = loaded_scopes.global(&path).expect("Module not loaded");
    println!("{global}");
  }

  let warnings = module_warnings(module, Some(&file_path));
  if !warnings.is_empty() && !quiet {
    println!(
      "{}",
      render_diagnostics(&warnings, None, options.use_colors)
    );
  }

  let entries: Vec<(ModulePath, Arc<str>, Option<SourceRange>)> = module
    .defs()
    .into_iter()
    .filter(|ctx| ctx.value().has_test_attr())
    .filter(|ctx| match test_name_filter {
      Some(wanted) => ctx.value().name.to_string() == wanted,
      None => true,
    })
    .map(|ctx| {
      let def = ctx.value();
      // Bare, matching `CoreProgram.defs`'/`lowered`'s own DEFAULT
      // (non-colliding) capture key -- the later `lowered.index_of`
      // lookup falls back to `path`-qualified only if this test's own
      // name happened to collide with some OTHER loaded module's own
      // def of the same name (see `core_check_module.rs`'s
      // `capture_path_for`). Display name (second element) stays bare
      // either way, for PASS/FAIL output. Third element is this def's
      // own declaration-level span, for `TestCaseResult::location`.
      (
        def.name.clone(),
        Arc::from(def.name.to_string()),
        Some(ctx.loc.clone()),
      )
    })
    .collect();

  if entries.is_empty() {
    return FileOutput {
      path: file_path.clone(),
      passed: 0,
      failed: 0,
      output_lines: Vec::new(),
      error_message: None,
      failures: Vec::new(),
      tests: Vec::new(),
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
  let mut lowered = match lower_core_ir::lower_program(&program) {
    Ok(l) => l,
    Err(e) => fail_file!(format!("lower {}: {e:?}", file_path.display())),
  };

  // `NativeTable::from_lowered` only borrows `lowered` -- computed before
  // `lowered.globals` is moved out below. The comment used to describe
  // a `.clone()` two lines down as a move, which it wasn't -- fixed to
  // an actual `mem::take` (the only other later use of `lowered` is
  // `.index_of(...)` below, which reads `lowered.paths`, a different
  // field, so this is safe). Matters because this clones the ENTIRE
  // loaded program's global count (init+std+lang+file), once per file,
  // in both the single- and multi-threaded test/check runners.
  let natives = Arc::new(core_value::NativeTable::from_lowered(&lowered));
  let globals = Arc::new(core_value::GlobalTable::new(std::mem::take(
    &mut lowered.globals,
  )));
  let mut cache = core_value::GlobalCache::new(globals.len());

  let mut output_lines: Vec<String> = Vec::new();
  let mut passed = 0;
  let mut failed = 0;
  let mut failures: Vec<(String, String)> = Vec::new();
  let mut tests: Vec<TestCaseResult> = Vec::new();

  for (test_path, name, location) in &entries {
    let start = Instant::now();
    // Qualified by `path` (this test file's own module) -- the bare
    // slot could belong to some OTHER loaded module's same-named def
    // instead, if one exists (see `insert_checked_def`'s own doc
    // comment); the qualified one is always THIS file's own.
    let idx = lowered.index_of(&path.extend_borrowed(test_path));
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
        let msg = format!("eval error: {e}");
        failures.push((name.to_string(), msg.clone()));
        tests.push(TestCaseResult {
          name: Arc::clone(name),
          outcome: TestOutcome::FailWithMessage(msg),
          duration,
          location: location.clone(),
        });
        continue;
      }
    };

    if options.debug && !quiet {
      output_lines.push(format!("  eval: {value:?}"));
    }

    match detect_test_result_value(&value, &natives.well_known) {
      TestResult::Pass => {
        passed += 1;
        output_lines.push(format!("{GREEN}PASS{RESET} {name} ({duration_str})"));
        tests.push(TestCaseResult {
          name: Arc::clone(name),
          outcome: TestOutcome::Pass,
          duration,
          location: location.clone(),
        });
      }
      TestResult::Fail => {
        failed += 1;
        output_lines.push(format!("{RED}FAIL{RESET} {name} ({duration_str})"));
        tests.push(TestCaseResult {
          name: Arc::clone(name),
          outcome: TestOutcome::Fail,
          duration,
          location: location.clone(),
        });
      }
      TestResult::FailWithMessage(msg) => {
        failed += 1;
        output_lines.push(format!("{RED}FAIL{RESET} {name} ({duration_str}): {msg}"));
        failures.push((name.to_string(), msg.clone()));
        tests.push(TestCaseResult {
          name: Arc::clone(name),
          outcome: TestOutcome::FailWithMessage(msg),
          duration,
          location: location.clone(),
        });
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
    path: file_path,
    passed,
    failed,
    output_lines,
    error_message: None,
    failures,
    tests,
  }
}

/// Shared setup for both `run_tests` and `run_tests_for_files`:
/// collected/sorted/deduped `.mo` files (skipping ones already covered
/// by the embedded default modules) plus the `LoadedModules` base every
/// file's `evaluate_one_test_file` call clones fresh from — the exact
/// file-discovery/`std/test`-preload logic `run_tests` always had,
/// factored out and named so the structured entry point can't drift from
/// it.
fn discover_test_files(
  inputs: &[PathBuf],
  options: &EvalOptions,
  extra_mote_paths: Vec<PathBuf>,
) -> Result<(Vec<PathBuf>, LoadedModules), String> {
  let mut files: Vec<PathBuf> = Vec::new();
  for input in inputs {
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

  Ok((files, master_loaded))
}

/// Runs `evaluate_one_test_file` over every file in `files`, single- or
/// multi-threaded per `num_threads` (`<=1` or one file: inline;
/// otherwise chunked across OS threads) — the one dispatch both
/// `run_tests` (live per-file progress printing) and `run_tests_for_files`
/// (a structured batch report) build on, so they can't drift on
/// scheduling/isolation semantics (see `evaluate_one_test_file`'s own
/// doc comment on per-file independence). Printing happens HERE, per
/// file, gated by `!quiet` — exactly where and when `run_tests` always
/// printed it, so sharing this with the structured path costs it nothing.
///
/// Always returned in ORIGINAL `files` order, regardless of which
/// thread/chunk finishes first — multi-threaded dispatch tags each
/// `FileOutput` with its input index and sorts before returning, so a
/// structured caller's output order is reproducible across runs.
fn evaluate_test_files(
  files: &[PathBuf],
  master_loaded: &LoadedModules,
  options: &EvalOptions,
  num_threads: usize,
  test_timeout: Option<std::time::Duration>,
  test_name_filter: Option<&str>,
  quiet: bool,
) -> Vec<FileOutput> {
  let total = files.len();

  fn report(output: &FileOutput, quiet: bool) {
    if quiet {
      return;
    }
    print_file_output(output);
    if let Some(ref err) = output.error_message {
      eprintln!("  {err}");
    }
  }

  // `master_loaded` is never mutated after this point -- every file
  // clones it fresh (inside `evaluate_one_test_file`), which is exactly
  // what keeps files independent of each other (see that function's own
  // doc comment). Single-threaded and multi-threaded dispatch below
  // differ only in scheduling, not in this isolation guarantee.
  if num_threads <= 1 || files.len() <= 1 {
    files
      .iter()
      .enumerate()
      .map(|(i, file)| {
        let output = evaluate_one_test_file(
          file,
          master_loaded,
          options,
          test_timeout,
          i,
          total,
          test_name_filter,
          quiet,
        );
        report(&output, quiet);
        output
      })
      .collect()
  } else {
    let n_threads = std::cmp::min(num_threads, files.len());
    let chunk_size = files.len().div_ceil(n_threads);

    // Indexed so results can be restored to input order once every
    // thread finishes, regardless of completion timing.
    let outputs_shared: Arc<Mutex<Vec<(usize, FileOutput)>>> = Arc::new(Mutex::new(Vec::new()));

    let mut handles = Vec::with_capacity(n_threads);
    for (chunk_idx, chunk) in files.chunks(chunk_size).enumerate() {
      let chunk_files: Vec<PathBuf> = chunk.to_vec();
      let base_loaded = master_loaded.clone();
      let opts = options.clone();
      let outputs = Arc::clone(&outputs_shared);
      let base_idx = chunk_idx * chunk_size;
      // Owned copy: the spawned closure below must be `'static`, but
      // `test_name_filter` only borrows from the caller's stack frame.
      let filter = test_name_filter.map(|s| s.to_string());

      let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
          for (i, file) in chunk_files.iter().enumerate() {
            let output = evaluate_one_test_file(
              file,
              &base_loaded,
              &opts,
              test_timeout,
              base_idx + i,
              total,
              filter.as_deref(),
              quiet,
            );
            report(&output, quiet);
            outputs.lock().unwrap().push((base_idx + i, output));
          }
        })
        .expect("failed to spawn test thread");
      handles.push(handle);
    }
    for handle in handles {
      handle.join().expect("test thread panicked");
    }

    let mut indexed = Arc::try_unwrap(outputs_shared)
      .unwrap()
      .into_inner()
      .unwrap();
    indexed.sort_by_key(|(i, _)| *i);
    indexed.into_iter().map(|(_, output)| output).collect()
  }
}

pub fn run_tests(
  inputs: Vec<PathBuf>,
  options: EvalOptions,
  num_threads: usize,
  test_timeout: Option<std::time::Duration>,
  extra_mote_paths: Vec<PathBuf>,
) -> Result<(), String> {
  let (files, master_loaded) = discover_test_files(&inputs, &options, extra_mote_paths)?;
  let outputs = evaluate_test_files(
    &files,
    &master_loaded,
    &options,
    num_threads,
    test_timeout,
    None,
    false,
  );

  let mut total_passed = 0;
  let mut total_failed = 0;
  let mut overall_errors: Vec<String> = Vec::new();
  for output in &outputs {
    total_passed += output.passed;
    total_failed += output.failed;
    if let Some(ref err) = output.error_message {
      overall_errors.push(err.clone());
    }
  }

  print_final_summary(total_passed, total_failed, &overall_errors)
}

/// Batch, disk-reading, print-free test run — the `run_tests_for_files`
/// counterpart of `check_files`. Reused by the CLI's `test --json`, the
/// MCP `test` tool, and the LSP's `monad.runTest`/`monad.runFileTests`
/// commands, none of which can tolerate `run_tests`'s own printing (it
/// would corrupt MCP's newline-delimited or LSP's `Content-Length`-
/// framed stdout stream — see `evaluate_one_test_file`'s `quiet`
/// parameter).
///
/// Unlike `run_tests` (whose CLI-level `inputs` is effectively always
/// non-empty), an empty `inputs` here defaults to the current directory,
/// matching `check_files`/`symbols_for_files` — needed so a `workspace:
/// true` (MCP) / zero-explicit-paths caller still gets sane recursive
/// discovery, exactly like the `check`/`symbols` tools already promise.
///
/// `test_name_filter`: `Some(name)` restricts evaluation to `#[test]`
/// defs with that bare name (used by the LSP's per-test `monad.runTest`
/// command); `None` runs every `#[test]` def found, matching `run_tests`.
pub fn run_tests_for_files(
  inputs: Vec<PathBuf>,
  options: EvalOptions,
  num_threads: usize,
  test_timeout: Option<std::time::Duration>,
  extra_mote_paths: Vec<PathBuf>,
  test_name_filter: Option<&str>,
) -> Result<Vec<FileTestResult>, String> {
  let inputs = if inputs.is_empty() {
    vec![PathBuf::from(".")]
  } else {
    inputs
  };
  let (files, master_loaded) = discover_test_files(&inputs, &options, extra_mote_paths)?;
  let outputs = evaluate_test_files(
    &files,
    &master_loaded,
    &options,
    num_threads,
    test_timeout,
    test_name_filter,
    true,
  );
  Ok(
    outputs
      .into_iter()
      .map(|o| FileTestResult {
        path: o.path,
        tests: o.tests,
        error_message: o.error_message,
      })
      .collect(),
  )
}

/// One target file's `organize-imports` result: the rewritten source if
/// anything changed (`None` means the file already has no bare
/// `use`/`open` to convert), or the error that kept it from being checked
/// at all (parse/type error — same as `check_files`, a broken file is
/// reported rather than silently skipped or guessed at).
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
/// — unlike `run_tests` — never evaluates `#[test]` defs or anything else;
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
  // Threaded alongside `results` so the whole-program pass below (which
  // only ever sees `ModulePath`s, via `Module::path`) can find each
  // warning's own originating `FileCheckResult` to merge into.
  let mut path_by_module: Map<ModulePath, PathBuf> = Map::new();
  for file in &files {
    let path: ModulePath = file.clone().into();
    path_by_module.insert(path.clone(), file.clone());
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

  // Whole-program pass, run once the corpus loop above has finished (so
  // `master_loaded` holds every checked file, not just one at a time) — a
  // def used only by a sibling file needs the full accumulated corpus to
  // avoid a false "unused" positive; see `unused_def_warnings`'s own doc
  // comment. Merged into each warning's own originating file's
  // `FileCheckResult` (matched by `ModulePath`, via `path_by_module`, not
  // appended as one lump at the end) — a module outside `files` (an
  // embedded default, or a dependency never explicitly checked) has no
  // `FileCheckResult` to merge into and its warnings are dropped, same as
  // `module_warnings`'s own existing per-file scope never surfacing
  // anything for a file that was never checked.
  for (module_path, mut warning) in crate::term::module::unused_def_warnings(&master_loaded) {
    if let Some(result) = path_by_module
      .get(&module_path)
      .and_then(|file| results.iter_mut().find(|r| &r.path == file))
    {
      warning.path = Some(result.path.clone());
      result.diagnostics.push(warning);
    }
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

/// One `#[test]`-attributed `def`'s name and declaration-level location
/// — the minimal "where do the test code lenses go" data
/// `textDocument/codeLens` needs. Deliberately separate from
/// `SymbolInfo`/`SymbolKind` (which has no "test" kind of its own):
/// widening `symbols`/`workspace/symbol`'s existing wire format to
/// distinguish test defs would be a compatibility change for every
/// existing consumer of `monad symbols --json`, for zero benefit here.
#[derive(Debug, Clone)]
pub struct TestDefLocation {
  pub name: String,
  pub location: Option<SourceRange>,
}

/// Same shape as `symbols_from_decls`, filtered to `#[test]`-attributed
/// `def`s only (`has_test_attr` — the exact predicate `evaluate_one_test_
/// file`'s own `entries` computation already uses on checked defs, here
/// applied to the same parsed `Decl::Def` `symbols_from_decls` iterates).
fn test_defs_from_decls(decls: &[SourceContext<Decl>]) -> Vec<TestDefLocation> {
  decls
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::Def(def) if def.has_test_attr() => Some(TestDefLocation {
        name: def.name.to_string(),
        location: Some(ctx.loc.clone()),
      }),
      _ => None,
    })
    .collect()
}

/// Test-def locations for a single file's CURRENT in-memory content —
/// the LSP server's `textDocument/codeLens` handler calls this, same
/// "single in-memory buffer" shape as `symbols_from_source`. No batch
/// (`_for_files`) counterpart exists: code lenses only ever operate on
/// the open document, never a whole-workspace scan.
pub fn test_defs_from_source(
  path: &Path,
  source: &str,
  extra_mote_paths: Vec<PathBuf>,
) -> Result<Vec<TestDefLocation>, String> {
  let path = path.to_path_buf();
  let module_path: ModulePath = path.clone().into();
  let mut loaded = default_modules().map_err(|e| format!("{e}"))?;
  loaded.set_search_paths(build_default_search_paths(&path, &extra_mote_paths));
  match crate::term::module::load_module_from_text_typed(source, &module_path, &mut loaded) {
    Ok(()) => Ok(
      loaded
        .get_module(&module_path)
        .map(|m| test_defs_from_decls(m.clone().to_decls().as_slice()))
        .unwrap_or_default(),
    ),
    Err(_) => Ok(Vec::new()),
  }
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

#[test]
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

  /// `run_tests`'s own `std/test.mo` resolution needs the real workspace
  /// root (see `test_direct_generic_call_via_lambda_does_not_regress`'s
  /// comment above) — shared by every `run_tests_for_files`/
  /// `test_defs_from_source` test below so they don't each re-derive it.
  fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
      .parent()
      .unwrap()
      .to_path_buf()
  }

  /// A fresh, uniquely-named temp dir for one test — same convention as
  /// `test_direct_generic_call_via_lambda_does_not_regress`'s own `dir`,
  /// just parameterized by a per-test tag so parallel tests never share
  /// a directory.
  fn temp_test_dir(tag: &str) -> PathBuf {
    let dir = PathBuf::from("/tmp").join(format!(
      "monad-test-{tag}-{:x}-{:x}",
      std::process::id(),
      std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos()
    ));
    fs::create_dir_all(&dir).unwrap();
    dir
  }

  #[test]
  fn test_run_tests_for_files_reports_pass_and_fail() {
    let dir = temp_test_dir("run-tests-pass-fail");
    let file = dir.join("t.mo");
    fs::write(
      &file,
      "#[test]\ndef test_a : Bool := true\n\n#[test]\ndef test_b : Bool := false\n",
    )
    .unwrap();

    let results = run_tests_for_files(
      vec![file],
      EvalOptions::default(),
      1,
      None,
      vec![workspace_root()],
      None,
    )
    .unwrap();
    fs::remove_dir_all(&dir).unwrap();

    assert_eq!(results.len(), 1);
    let file_result = &results[0];
    assert!(file_result.error_message.is_none());
    assert_eq!(file_result.tests.len(), 2);
    let outcome_of = |name: &str| {
      &file_result
        .tests
        .iter()
        .find(|t| t.name.as_ref() == name)
        .unwrap()
        .outcome
    };
    assert!(matches!(outcome_of("test_a"), TestOutcome::Pass));
    assert!(matches!(outcome_of("test_b"), TestOutcome::Fail));
  }

  /// Regression test for `detect_test_result_value`'s own tag-collision
  /// bug: `IO A`'s sole constructor and `Bool`'s `true` are each their
  /// own type's first constructor, so both have the same PER-TYPE-
  /// LOCAL `CtorTag.tag` (0) — before this test was added,
  /// `detect_test_result_value` checked `bool_true` before ever
  /// unwrapping `io_io`, so ANY `IO`-wrapped test result (regardless of
  /// its actual payload) matched `bool_true` immediately and reported
  /// Pass unconditionally. Found while validating the dictionary-
  /// passing plan's own end-to-end compile-and-run tests
  /// (lang/codegen/test/compile_tests.mo), which are exactly this
  /// shape (`IO Bool`, asserting a compiled program's real exit code).
  #[test]
  fn test_run_tests_for_files_io_wrapped_bool_reports_correctly() {
    let dir = temp_test_dir("run-tests-io-bool");
    let file = dir.join("t.mo");
    fs::write(
      &file,
      "#[test]\ndef test_io_true : IO Bool := IO.io true\n\n#[test]\ndef test_io_false : IO Bool := IO.io false\n",
    )
    .unwrap();

    let results = run_tests_for_files(
      vec![file],
      EvalOptions::default(),
      1,
      None,
      vec![workspace_root()],
      None,
    )
    .unwrap();
    fs::remove_dir_all(&dir).unwrap();

    assert_eq!(results.len(), 1);
    let file_result = &results[0];
    assert!(file_result.error_message.is_none());
    assert_eq!(file_result.tests.len(), 2);
    let outcome_of = |name: &str| {
      &file_result
        .tests
        .iter()
        .find(|t| t.name.as_ref() == name)
        .unwrap()
        .outcome
    };
    assert!(matches!(outcome_of("test_io_true"), TestOutcome::Pass));
    assert!(matches!(outcome_of("test_io_false"), TestOutcome::Fail));
  }

  #[test]
  fn test_run_tests_for_files_file_level_error_on_parse_failure() {
    let dir = temp_test_dir("run-tests-parse-error");
    let file = dir.join("broken.mo");
    fs::write(&file, "def x : I64 := \n").unwrap(); // incomplete, doesn't parse

    let results = run_tests_for_files(
      vec![file],
      EvalOptions::default(),
      1,
      None,
      vec![workspace_root()],
      None,
    )
    .unwrap();
    fs::remove_dir_all(&dir).unwrap();

    assert_eq!(results.len(), 1);
    assert!(results[0].error_message.is_some());
    assert!(results[0].tests.is_empty());
  }

  #[test]
  fn test_run_tests_for_files_filters_by_test_name() {
    let dir = temp_test_dir("run-tests-filter");
    let file = dir.join("t.mo");
    fs::write(
      &file,
      "#[test]\ndef test_a : Bool := true\n\n#[test]\ndef test_b : Bool := true\n",
    )
    .unwrap();

    let results = run_tests_for_files(
      vec![file],
      EvalOptions::default(),
      1,
      None,
      vec![workspace_root()],
      Some("test_a"),
    )
    .unwrap();
    fs::remove_dir_all(&dir).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].tests.len(), 1);
    assert_eq!(results[0].tests[0].name.as_ref(), "test_a");
  }

  #[test]
  fn test_run_tests_for_files_preserves_file_order_across_threads() {
    let dir = temp_test_dir("run-tests-order");
    let mut files = Vec::new();
    for i in 0..4 {
      let file = dir.join(format!("t{i}.mo"));
      fs::write(&file, format!("#[test]\ndef test_t{i} : Bool := true\n")).unwrap();
      files.push(file);
    }
    let mut expected = files.clone();
    expected.sort();

    let results = run_tests_for_files(
      files,
      EvalOptions::default(),
      2, // multi-threaded dispatch
      None,
      vec![workspace_root()],
      None,
    )
    .unwrap();
    fs::remove_dir_all(&dir).unwrap();

    let actual: Vec<PathBuf> = results.into_iter().map(|r| r.path).collect();
    assert_eq!(actual, expected);
  }

  /// Empty `inputs` must default to scanning the current directory
  /// (matching `check_files`/`symbols_for_files`), not silently produce
  /// zero results — confirmed by checking `vec![]` and `vec![PathBuf::
  /// from(".")]` scan the identical file set, without actually changing
  /// the test process's shared, global current directory (unsafe to do
  /// from a single test in a parallel test binary).
  #[test]
  fn test_run_tests_for_files_defaults_empty_inputs_to_cwd() {
    let empty_result = run_tests_for_files(
      vec![],
      EvalOptions::default(),
      1,
      None,
      vec![workspace_root()],
      None,
    )
    .unwrap();
    let dot_result = run_tests_for_files(
      vec![PathBuf::from(".")],
      EvalOptions::default(),
      1,
      None,
      vec![workspace_root()],
      None,
    )
    .unwrap();

    let empty_paths: Vec<PathBuf> = empty_result.into_iter().map(|r| r.path).collect();
    let dot_paths: Vec<PathBuf> = dot_result.into_iter().map(|r| r.path).collect();
    assert_eq!(empty_paths, dot_paths);
  }

  #[test]
  fn test_test_defs_from_source_finds_test_attributed_defs_only() {
    let source = "def plain : Bool := true\n\n#[test]\ndef test_one : Bool := true\n\n#[test]\ndef test_two : Bool := false\n";
    let defs = test_defs_from_source(
      &PathBuf::from("/tmp/monad-test-defs-mixed.mo"),
      source,
      vec![],
    )
    .unwrap();
    let names: Vec<&str> = defs.iter().map(|d| d.name.as_str()).collect();
    assert_eq!(names, vec!["test_one", "test_two"]);
    assert!(defs.iter().all(|d| d.location.is_some()));
  }

  #[test]
  fn test_test_defs_from_source_empty_when_no_tests() {
    let source = "def plain : Bool := true\n";
    let defs = test_defs_from_source(
      &PathBuf::from("/tmp/monad-test-defs-none.mo"),
      source,
      vec![],
    )
    .unwrap();
    assert!(defs.is_empty());
  }

  #[test]
  fn test_test_defs_from_source_empty_on_parse_error() {
    let source = "def x : I64 := \n"; // incomplete, doesn't parse
    let defs = test_defs_from_source(
      &PathBuf::from("/tmp/monad-test-defs-broken.mo"),
      source,
      vec![],
    )
    .unwrap();
    assert!(defs.is_empty());
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

#[terminating]
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

  /// `@` carries no built-in meaning — `infix (@) := ...` binds it to an
  /// ordinary function like any other operator (mirrors the arithmetic
  /// test above, but exercises a user-defined `infix` declaration end to
  /// end through the same `eval_core_program` pipeline).
  #[test]
  fn eval_core_program_user_defined_at_operator_end_to_end() {
    let source = r#"
use init

def my_append (xs ys : List I64) : List I64 :=
    match xs {
        List.empty => ys,
        List.cons h t => List.cons h (my_append t ys)
    }

infix (@) := my_append

#[terminating]
def sum (xs : List I64) : I64 :=
    match xs {
        List.empty => 0,
        List.cons h t => h + sum t
    }

def main : I64 :=
    sum (List.cons 1 (List.cons 2 List.empty) @ List.cons 3 List.empty)
"#;
    let result = eval_core_program(
      &ModulePath::top("'eval_core_program_at_operator_test"),
      source,
    )
    .unwrap_or_else(|e| panic!("eval_core_program failed: {e}"));
    match result {
      core_value::Value::Lit(core_ir::IrLit::Num(n, _)) => assert_eq!(n, 6),
      other => panic!("expected an int literal, got {other:?}"),
    }
  }

  /// Regression test for a `MatchTraversalMismatch` bug in
  /// `core_check.rs`'s `try_resolve_class_method`: a non-speculative
  /// arg (`class_meta` already resolved before this arg is processed)
  /// that itself desugars to a dict-projection call — here,
  /// `Show.show xs` where `xs : List I64` needs a NESTED `Show I64`
  /// dictionary via `instance [Show A] Show (List A)` — used to have its
  /// already-correct `arg_d` re-`check`ed and spuriously rejected
  /// (`check`'s generic `Match`-arm mis-infers a synthesized dictionary-
  /// projection `Match`'s field type), aborting `try_resolve_class_method`
  /// entirely and forcing the caller down `desugar_struct_literals`'s
  /// generic `App` fallback — which re-resolves (and re-records) the SAME
  /// call a second time in the wrong order (self before its own arg),
  /// desyncing `lower_core_ir.rs`'s later traversal. Mirrors the real bug
  /// found in `lang/module.mo`'s `show_loaded_modules` (an `Append`/`Show`
  /// chain inside a single-case `match`) at a scale small enough to keep
  /// here. Confirmed this reproduces `MatchTraversalMismatch { expected:
  /// [Append], found: [Show] }` before the fix, by temporarily reverting
  /// it during investigation.
  #[test]
  fn eval_core_program_nested_class_method_inside_single_case_match_does_not_desync_match_queue() {
    let source = r#"
use init

class Show A {
    def show : A -> String
}

instance Show I64 {
    def show (n : I64) : String := I64.to_string n
}

def list_show (show_elem : A -> String) (xs : List A) : String :=
    match xs {
        List.empty => "",
        List.cons h t => show_elem h ++ list_show show_elem t
    }

instance [Show A] Show (List A) {
    def show (xs : List A) : String := list_show (fn a => Show.show a) xs
}

struct Pair {
    x : I64,
    xs : List I64,
}

def show_pair (p : Pair) : String :=
    match p {
        mk x xs => "x=" ++ Show.show x ++ ",xs=" ++ Show.show xs
    }

def main : String := show_pair { x := 1, xs := List.cons 2 List.empty }
"#;
    let result = eval_core_program(&ModulePath::top("'group2_regression_test"), source)
      .unwrap_or_else(|e| panic!("eval_core_program failed: {e}"));
    match result {
      core_value::Value::Lit(core_ir::IrLit::Str(s)) => assert_eq!(s.as_str(), "x=1,xs=2"),
      other => panic!("expected a string literal, got {other:?}"),
    }
  }

  /// Regression test for an `UnknownInductive` bug in
  /// `core_check.rs`'s `desugar_struct_literals`: an anonymous struct
  /// literal's type atom (`atom`, derived from `expected` — the literal
  /// itself carries no explicit type name) used to be looked up in
  /// `atom_paths` alone, falling back to a synthetic
  /// `<unresolved-struct-...>` placeholder when absent — unlike every
  /// other atom-to-path lookup in this file, which also falls back to
  /// `structs.inductive_paths`. `atom_paths` only gains an entry for a
  /// struct type that appears as an explicit SOURCE TOKEN somewhere in
  /// the def being lowered; a NESTED anonymous literal (here, `inner`'s
  /// own `{ a := 1 }`) whose type is only ever implied by an enclosing
  /// struct's field type — never spelled out as `Inner` anywhere in this
  /// def's own source — never gets that entry, so the fallback used to
  /// matter. Mirrors the real bug found in `lang/tests/types_tests.mo`'s
  /// `test_scope_construct` (a `Scope { scope := { ... }, ... }` literal
  /// with a bare, un-annotated nested struct value). Confirmed this
  /// reproduces `UnknownInductive` before the fix, by temporarily
  /// reverting it during investigation.
  #[test]
  fn eval_core_program_nested_anonymous_struct_literal_resolves_its_type() {
    let source = r#"
use init

struct Inner {
    a : I64,
}

struct Outer {
    inner : Inner,
    b : I64,
}

def main : I64 :=
    let o : Outer := {
        inner := { a := 1 },
        b := 2,
    } in
    match o {
        mk inner b => b
    }
"#;
    let result = eval_core_program(&ModulePath::top("'group1_regression_test"), source)
      .unwrap_or_else(|e| panic!("eval_core_program failed: {e}"));
    match result {
      core_value::Value::Lit(core_ir::IrLit::Num(n, _)) => assert_eq!(n, 2),
      other => panic!("expected an int literal, got {other:?}"),
    }
  }

  /// Regression test for a `MatchTraversalMismatch` bug in
  /// `core_check.rs`'s `desugar_struct_literals`'s `Match` arm: a list
  /// LITERAL used directly as a match scrutinee (`match [1, 2, 3] {
  /// ... }`, parsing to a raw `FromListLiteral.cons`/`.empty` chain)
  /// used to have its own `record_match_resolution` call silently
  /// skipped — the plain `infer` this arm called on the RAW pre-desugar
  /// scrutinee never resolves/defaults class methods (only
  /// `desugar_struct_literals` itself does that), so it always landed on
  /// a `Meta`-headed application type `resolve_match_inductive_atom`
  /// can't turn into an atom. Skipping that one match's own resolution
  /// WITHOUT also skipping its case bodies' own captures (an intervening
  /// `BEq` dict projection from `h == 1`, recursed into regardless)
  /// desynced the queue for `lower_core_ir.rs`'s later traversal.
  ///
  /// Fixed by re-deriving the scrutinee's type from the ALREADY-
  /// desugared `scrutinee_d` whenever the raw attempt can't resolve one
  /// (raw stays the primary path — trying `scrutinee_d` first or
  /// unconditionally regressed several other corpus files, e.g. `std/
  /// test_map_full.mo`, since `infer` on an already-desugared term can
  /// itself land on an unresolvable type when that term contains a
  /// synthesized single-case dict-projection `Match` — a separate, known
  /// gap), and by reusing that ONE resolved type for the per-case
  /// pattern-variable field-type lookup (E2) too, rather than
  /// independently re-`infer`ring it a second time per case: `infer`
  /// isn't idempotent across separate calls on the same term (each
  /// `Forall` it crosses is instantiated with brand-new metas every
  /// call), so a second, independent `infer(&scrutinee_d)` call was
  /// observed to land back on an unresolved `Meta`-headed type even
  /// right after the first call just resolved the identical term
  /// concretely.
  ///
  /// Mirrors the real bug in `examples/pattern_matching.mo`'s
  /// `test_match_list_nonempty`/`test_match_guard` (a list literal
  /// scrutinee combined with a `BEq` call in one of the match's own
  /// explicit arms; `test_match_guard`'s NESTED `match t { ... }` needed
  /// the field-type fix too, since `t`'s own type is only resolvable via
  /// the outer match's E2 field-type lookup). Confirmed this reproduces
  /// `MatchTraversalMismatch { expected: [empty, cons], found: [BEq] }`
  /// before the fix, by temporarily reverting it during investigation.
  #[test]
  fn eval_core_program_list_literal_match_scrutinee_with_class_method_in_arm_does_not_desync_match_queue()
   {
    let source = r#"
use init

def main : Bool :=
    match [1, 2, 3] {
        empty => false,
        cons h t => h == 1
    }
"#;
    let result = eval_core_program(
      &ModulePath::top("'list_literal_match_regression_test"),
      source,
    )
    .unwrap_or_else(|e| panic!("eval_core_program failed: {e}"));
    match result {
      // `Bool` is an ordinary two-constructor inductive (see
      // `core_native.rs`'s own module doc comment for why `CoreIr` has
      // no `IrLit::Bool`), declared `true` then `false`
      // (`init/prelude.mo`) — tag 0 is `true`.
      core_value::Value::Con { tag, ref args } if args.is_empty() => assert_eq!(tag, 0),
      other => panic!("expected Bool.true, got {other:?}"),
    }
  }

  /// Regression test for the REPL's "Free(atom) missing from atom_paths"
  /// panic (`raise_core.rs:227`) — reliably reproduced by ANY REPL input
  /// before the fix (`cargo run -- repl` then entering `1`, `"hello"`,
  /// or `true` all panicked identically). Doesn't go through
  /// `eval_repl_term` itself (gated behind the `repl` Cargo feature, not
  /// enabled by this crate's own default `cargo test`) — instead
  /// constructs the exact same shape of input `eval_repl_term` builds
  /// internally (a `Hole`-typed synthetic `def`, `check_one_def_new`'s
  /// "no declared type, infer one" branch — the ONLY branch that raises
  /// an INFERRED type back to a `Term`, which is where the missing atom
  /// came from: `core_check.rs`'s `primitive_type`, interning a
  /// literal's default type fresh via `mctx` during inference, never
  /// captured by lowering the def's own source text since there's no
  /// type annotation to lower) and drives it through `build_core_
  /// program` directly, the same function `eval_repl_term` itself calls.
  #[test]
  fn build_core_program_hole_typed_def_does_not_panic_on_missing_atom() {
    let loaded = default_modules().expect("default_modules");
    let module_path = ModulePath::top("'repl_regression_test");
    for term in [
      Term::Lit {
        value: term::Literal::Num {
          value: 1,
          suffix: term::NumSuffix::I64,
        },
      },
      Term::Lit {
        value: term::Literal::Str {
          value: "hello".to_string(),
        },
      },
    ] {
      let decl = SourceContext::no_ctx(Decl::Def(term::def(
        mpt("__repl_result"),
        vec![],
        Term::Hole,
        term,
        vec![],
      )));
      build_core_program(&loaded, &[(module_path.clone(), vec![decl])])
        .unwrap_or_else(|e| panic!("build_core_program failed (should succeed, not panic): {e}"));
    }
  }
}
