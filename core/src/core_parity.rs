//! Phase 8 of `plans/implementations/core-term-closure-evaluator.md`:
//! correctness parity between the tree-walker (`eval::eval`, reached via
//! `run_tests`/the CLI's `test` command today) and the `CoreTerm`-closure
//! evaluator (`eval_core_program`'s own pipeline). Runs the exact same
//! `#[test]`-attributed defs discovered across a set of input files/dirs
//! through both evaluators and diffs pass/fail — the actual gate before
//! `run()`/`run_tests()` can default to core-eval and the tree-walker gets
//! deprecated.
//!
//! Deliberately reuses `run_tests`'s own file-collection/module-loading/
//! test-discovery machinery (`crate::collect_mo_files`, `crate::
//! load_module`, `crate::detect_test_result`, `crate::run_test_eval`, all
//! private `fn`s in `lib.rs` but visible here since this module is a
//! descendant of the crate root) rather than reimplementing it, so "what
//! counts as a test" and "does the tree-walker currently pass it" can
//! never drift from what the real CLI reports.

use std::path::PathBuf;

use crate::core_check_module::check_all_modules_capturing_core;
use crate::core_eval::force_global;
use crate::core_ir::IrLit;
use crate::core_value::{GlobalCache, GlobalTable, NativeTable, Value};
use crate::eval::EvalOptions;
use crate::lower_core_ir::{WellKnownCtors, lower_program};
use crate::term::module::{
  default_modules, init_package_sources, load_decls, load_decls_from_text_with_path,
  load_module_files,
};
use crate::term::{ModulePath, id};

/// One test's outcome under one evaluator. `NotPass` folds together every
/// way a test can fail to demonstrate success — an assertion that came
/// back `false`/`err` (with a message when one's available), an eval-time
/// crash, or (core-eval only) a pipeline failure with no tree-walker
/// equivalent at all (check/lower error, or the def never making it into
/// the lowered program). Phase 8 only cares whether the two evaluators
/// reach the *same verdict* on the same test, not whether their failure
/// messages happen to match word for word — they never will, since the
/// two pipelines fail in structurally different ways.
#[derive(Debug, Clone)]
pub enum ParityOutcome {
  Pass,
  NotPass(String),
}

impl ParityOutcome {
  pub fn is_pass(&self) -> bool {
    matches!(self, ParityOutcome::Pass)
  }
}

pub struct ParityTestResult {
  pub path: ModulePath,
  pub tree_walker: ParityOutcome,
  pub core_eval: ParityOutcome,
}

impl ParityTestResult {
  pub fn matches(&self) -> bool {
    self.tree_walker.is_pass() == self.core_eval.is_pass()
  }
}

pub struct ParitySummary {
  pub results: Vec<ParityTestResult>,
}

impl ParitySummary {
  pub fn mismatches(&self) -> impl Iterator<Item = &ParityTestResult> {
    self.results.iter().filter(|r| !r.matches())
  }
}

/// A single discovered `#[test]` def, kept just long enough to pair its
/// tree-walker outcome (computed while its module is loaded) with its
/// later core-eval outcome (computed once, after every module involved
/// has been captured into one combined `CoreProgram`).
struct DiscoveredTest {
  path: ModulePath,
  /// The module this test was discovered in — needed to fall back to a
  /// module-qualified `lowered.index_of` lookup when `path`'s own bare
  /// name happens to collide with some OTHER loaded module's own def of
  /// the same name (see `core_check_module.rs`'s `capture_path_for`).
  module_path: ModulePath,
  tree_walker: ParityOutcome,
}

fn term_test_outcome(term: &crate::term::Term) -> ParityOutcome {
  match crate::detect_test_result(term) {
    crate::TestResult::Pass => ParityOutcome::Pass,
    crate::TestResult::Fail => ParityOutcome::NotPass("assertion failed".to_string()),
    crate::TestResult::FailWithMessage(msg) => ParityOutcome::NotPass(msg),
  }
}

/// The `Value`-shaped counterpart to `crate::detect_test_result` — same
/// `Bool`/`IO`/`Result` unwrapping convention, just reading constructor
/// *tags* (resolved once, via `well_known`) instead of a `Term::Con`'s
/// own `typ_name` field, since a runtime `Value::Con` carries no type
/// name at all (see `WellKnownCtors`'s own doc comment for why).
///
/// TODO: `IO` is slated to be replaced with an opaque indexed monad whose
/// internal value isn't reachable via an ordinary constructor match —
/// this `io_io` unwrap will need to change to whatever that type's own
/// (non-structural) unwrap mechanism ends up being once that lands.
fn value_test_outcome(value: &Value, well_known: &WellKnownCtors) -> ParityOutcome {
  match value {
    Value::Con { tag, args } => {
      if well_known.bool_true.is_some_and(|t| t.tag == *tag) {
        ParityOutcome::Pass
      } else if well_known.bool_false.is_some_and(|t| t.tag == *tag) {
        ParityOutcome::NotPass("assertion failed".to_string())
      } else if well_known.io_io.is_some_and(|t| t.tag == *tag) {
        match args.first() {
          Some(inner) => value_test_outcome(inner, well_known),
          None => ParityOutcome::NotPass("IO.io with no inner value".to_string()),
        }
      } else if well_known.result_ok.is_some_and(|t| t.tag == *tag) {
        ParityOutcome::Pass
      } else if well_known.result_err.is_some_and(|t| t.tag == *tag) {
        let msg = args.first().and_then(value_extract_string);
        ParityOutcome::NotPass(msg.unwrap_or_else(|| format!("{value:?}")))
      } else {
        ParityOutcome::NotPass(format!("unexpected result: {value:?}"))
      }
    }
    other => ParityOutcome::NotPass(format!("unexpected result: {other:?}")),
  }
}

fn value_extract_string(value: &Value) -> Option<String> {
  match value {
    Value::Lit(IrLit::Str(s)) => Some(s.clone()),
    _ => None,
  }
}

/// Run every `#[test]` def discovered under `inputs` (files or
/// directories, expanded recursively — same as `run_tests`) through both
/// the tree-walker and `core-eval`, and report each one's verdict under
/// both.
///
/// Two passes: first, `inputs` are loaded module-by-module through the
/// ordinary (non-capturing) pipeline `run_tests` itself uses, discovering
/// every `#[test]` def and its tree-walker outcome as each module loads
/// (this ALSO grows one shared `LoadedModules`, needed for the second
/// pass's own name resolution). Second, every module that ended up
/// loaded — the `init` package (via `init_package_sources`, same as
/// `eval_core_program`) plus everything else (read fresh from disk via
/// `load_decls`, since `check_all_modules_capturing_core` needs each
/// module's raw, unchecked `Decl`s, not `loaded`'s own already-checked
/// copies — see that function's own doc comment) — is re-checked
/// together through `check_all_modules_capturing_core` into one combined
/// `CoreProgram`, lowered once, and every discovered test's def is forced
/// through it.
///
/// A `check_all_modules_capturing_core`/`lower_program` failure aborts
/// the whole second pass (both are all-or-nothing over their module set)
/// — reported as an `Err` from this function, not a per-test outcome,
/// since there's no way to know which subset of tests it would have
/// affected.
pub fn run_parity_tests(
  inputs: Vec<PathBuf>,
  extra_mote_paths: Vec<PathBuf>,
) -> Result<ParitySummary, String> {
  let mut files: Vec<PathBuf> = Vec::new();
  for input in &inputs {
    if input.is_dir() {
      files.extend(crate::collect_mo_files(input));
    } else {
      files.push(input.clone());
    }
  }
  files.sort();
  files.dedup();

  let mut master_loaded = default_modules().map_err(|e| format!("{e}"))?;
  master_loaded.set_test_mode(true);
  let search_paths = if let Some(first_input) = inputs.first() {
    crate::build_default_search_paths(first_input, &extra_mote_paths)
  } else {
    crate::build_default_search_paths(&PathBuf::from("."), &extra_mote_paths)
  };
  master_loaded.set_search_paths(search_paths);

  // Ensure std/test is loaded (for Test.assert), mirrors `run_tests`.
  let test_path: ModulePath = ModulePath::new(vec![id("std"), id("test")]);
  if master_loaded.get_module(&test_path).is_none() {
    master_loaded = load_module_files(&test_path, master_loaded)
      .map_err(|e| format!("Failed to load std/test: {e}"))?;
  }

  // Skip files already satisfied by the embedded `init` package --
  // `crate::is_default_module_file` (canonicalized-path comparison
  // against `default_module_source_files()`) is `run_tests`'s OWN,
  // current filter. An earlier version of this filter used a
  // `ModulePath`-string heuristic (`path.last()` matched against a
  // plain single-segment lookup) that does NOT work for `prelude.mo`
  // specifically -- it's registered internally as `'prelude` (leading
  // quote), which never matches a plain `"prelude"` lookup, so that
  // older heuristic let `init/prelude.mo` slip through and get loaded a
  // SECOND time under a different `ModulePath`. Confirmed via a real
  // hang: with prelude double-loaded, `init/tests.mo`'s later, otherwise
  // trivial tests (`1 + 2 == 3`) got stuck for minutes -- almost
  // certainly duplicate/ambiguous typeclass instances blowing up
  // instance search. `is_default_module_file` sidesteps the whole
  // `ModulePath`-naming question entirely by comparing canonicalized
  // file paths instead.
  let files: Vec<PathBuf> = files
    .into_iter()
    .filter(|file| !crate::is_default_module_file(file))
    .collect();

  let mut discovered: Vec<DiscoveredTest> = Vec::new();
  for file in &files {
    let module_path: ModulePath = file.clone().into();
    eprintln!("[parity] tree-walker: loading {}", file.display());
    master_loaded = crate::load_module(file, &module_path, master_loaded)?;
    let module = master_loaded
      .get_module(&module_path)
      .cloned()
      .ok_or_else(|| format!("module {module_path} not loaded after load_module succeeded"))?;
    let loaded_scopes = master_loaded.scopes();
    let global = loaded_scopes
      .global(&module_path)
      .ok_or_else(|| format!("no scope built for {module_path}"))?;
    let test_defs: Vec<_> = module
      .defs()
      .into_iter()
      .filter(|c| c.value().has_test_attr())
      .collect();
    eprintln!(
      "[parity] tree-walker: {} test(s) in {}",
      test_defs.len(),
      file.display()
    );
    for ctx in test_defs {
      let def = ctx.value();
      eprintln!("[parity] tree-walker: running {}", def.name);
      // A fresh `Scope` per test, not one reused for the whole file --
      // matching `test_one_file`'s own `&global.scope()` call site
      // exactly (`lib.rs`). Reusing one `Scope` across many evaluations
      // is confirmed NOT equivalent: it reproducibly hung (multiple
      // CPU-minutes, no forward progress) on trivial tests like `1 + 2
      // == 3` once enough prior modules had been loaded into `global`,
      // while a fresh `Scope` per call -- the same workload, only
      // differing in this one respect -- runs every test in
      // microseconds. Root cause not chased further (out of scope for
      // Phase 8, which is about the NEW evaluator's correctness, not
      // auditing `Scope`'s own internals) -- avoided instead.
      let outcome = match crate::run_test_eval(
        def.term.clone(),
        &global.scope(),
        &EvalOptions::default(),
        None,
      ) {
        Ok(result) => term_test_outcome(&result),
        Err(e) => ParityOutcome::NotPass(format!("eval error: {e}")),
      };
      discovered.push(DiscoveredTest {
        path: def.name.clone(),
        module_path: module_path.clone(),
        tree_walker: outcome,
      });
    }
  }

  // Second pass: one combined capturing check + lowering over every
  // module that ended up loaded, mirroring `eval_core_program` but for
  // the whole corpus at once instead of one module at a time.
  let init_paths: std::collections::HashSet<ModulePath> = init_package_sources()
    .map_err(|e| format!("{e}"))?
    .iter()
    .map(|(p, _)| p.clone())
    .collect();
  let mut capture_modules: Vec<_> = init_package_sources()
    .map_err(|e| format!("{e}"))?
    .into_iter()
    .map(|(p, text)| {
      load_decls_from_text_with_path(&text, &Default::default())
        .map(|d| (p.clone(), d))
        .map_err(|e| format!("parse {p}: {e}"))
    })
    .collect::<Result<Vec<_>, String>>()?;

  for module in master_loaded.modules() {
    let path = module.path().clone();
    if init_paths.contains(&path) {
      continue;
    }
    let decls = load_decls(&path, master_loaded.search_paths())
      .map_err(|e| format!("re-reading {path} for capturing check: {e}"))?;
    capture_modules.push((path, decls));
  }
  eprintln!(
    "[parity] core-eval: capturing-check {} modules ({} discovered test defs)",
    capture_modules.len(),
    discovered.len()
  );

  let program = check_all_modules_capturing_core(&capture_modules, &master_loaded)
    .map_err(|e| format!("check_all_modules_capturing_core: {e:?}"))?;
  eprintln!("[parity] core-eval: check complete, lowering");
  let lowered = lower_program(&program).map_err(|e| format!("lower_program: {e:?}"))?;
  eprintln!("[parity] core-eval: lowering complete, forcing tests");
  let natives = NativeTable::from_lowered(&lowered);
  // Resolve every test's global slot BEFORE `lowered.globals` is moved
  // into `GlobalTable::new` below -- `index_of` borrows `lowered` as a
  // whole, which a partial move out of one of its fields would forbid.
  // Qualified by `t.module_path` (this test's own declaring module) --
  // the bare slot could belong to some OTHER loaded module's same-named
  // def instead, if one exists (see `insert_checked_def`'s own doc
  // comment, core_check_module.rs); the qualified one is always this
  // test's own.
  let indices: Vec<Option<u32>> = discovered
    .iter()
    .map(|t| lowered.index_of(&t.module_path.clone().extend(t.path.clone())))
    .collect();
  let globals = GlobalTable::new(lowered.globals);
  let mut cache = GlobalCache::new(globals.len());

  let mut results = Vec::with_capacity(discovered.len());
  for (test, idx) in discovered.into_iter().zip(indices) {
    let core_eval = match idx {
      None => ParityOutcome::NotPass("not present in the lowered program (skipped)".to_string()),
      Some(idx) => match force_global(idx, &globals, &natives, &mut cache) {
        Ok(value) => value_test_outcome(&value, &natives.well_known),
        Err(e) => ParityOutcome::NotPass(format!("eval error: {e}")),
      },
    };
    results.push(ParityTestResult {
      path: test.path,
      tree_walker: test.tree_walker,
      core_eval,
    });
  }

  Ok(ParitySummary { results })
}
