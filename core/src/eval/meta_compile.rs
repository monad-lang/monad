//! On-demand compilation and invocation of already-loaded Monad
//! "meta"/derive-handler functions (ordinary `def`s, e.g. `std/derive.mo`'s
//! `derive_lens`) via the real production evaluator (`core_eval`), for use
//! during macro expansion — see `plans/review-and-reduce-the-greedy-nest.md`.
//!
//! `CoreIr` (what `core_eval` actually runs) can only be produced as a
//! byproduct of a def successfully passing the real type checker — there
//! is no path that produces evaluable code for something that hasn't been
//! checked (unlike the old, removed tree-walking evaluator, which was
//! untyped). Rather than attempt fine-grained per-def transitive-
//! dependency resolution (working out exactly which OTHER defs a target
//! def's body references, transitively, and checking only those), this
//! reuses the existing, already-tested whole-loaded-program capture path
//! (`core_check_module::check_all_modules_capturing_core` +
//! `lower_core_ir::lower_program`) — the plan's own explicitly-sanctioned
//! fallback, adopted directly rather than as a last resort, since it's
//! simple and robust and the cost is paid at most once per `expand_macros`
//! call, only for files that actually invoke a meta/derive function.

use crate::core_eval;
use crate::core_program::CoreProgram;
use crate::core_value::{GlobalCache, GlobalTable, NativeTable, Value};
use crate::lower_core_ir::{LoweredProgram, lower_program};
use crate::term::module::{LoadedModules, Module};
use crate::term::{Decl, ModulePath, SourceContext};

use super::macro_expand::MacroError;

/// A fully compiled, directly-evaluable snapshot of every module
/// currently in a `LoadedModules` — built once (lazily, only when a file
/// actually invokes a meta/derive function) and reused for every further
/// meta invocation within that same `expand_macros` call. Evaluation runs
/// against a `GlobalCache::new_pure` sandbox: no IO/concurrency natives
/// are reachable (`core_eval.rs`'s `fire_or_accumulate` enforces this via
/// `core_native::is_pure_native`).
pub struct MetaEvalContext {
  paths: Vec<ModulePath>,
  globals: GlobalTable,
  natives: NativeTable,
  cache: GlobalCache,
}

impl MetaEvalContext {
  /// `current_decls` — the file `expand_macros` is currently processing,
  /// not yet a `loaded` module of its own — is threaded in as an extra,
  /// in-memory capture batch (`build_core_program`'s own `extra_modules`
  /// parameter), needed for a same-file "meta" def (one defined right
  /// alongside a `reflect_type_info!` call in the file being expanded,
  /// rather than in an already-`use`d dependency like `std/derive.mo`,
  /// which is captured via the ordinary `loaded`-re-read-from-disk path
  /// with no special-casing needed).
  ///
  /// `current_path` — the file's own `ModulePath` — MUST be used as that
  /// `extra_modules` entry's key, not a synthetic placeholder. If the
  /// file currently being expanded is already registered in `loaded` (as
  /// the real CLI's `test`/`run` commands do, ahead of checking it) and
  /// `current_path` doesn't match that registration, `build_core_program`
  /// treats it as a *different*, not-yet-captured module and additionally
  /// RE-READS it from disk — picking up its ORIGINAL, un-expanded source,
  /// which still contains the very `reflect_type_info!`/`derive_lens!`
  /// call this whole invocation started from, and recursing without
  /// bound. Confirmed directly as a real stack overflow, not
  /// hypothetical — this was the actual root cause, not the
  /// `Decl::MacroCall` filtering below (necessary, but insufficient on
  /// its own).
  pub fn build(
    loaded: &LoadedModules,
    current_path: &ModulePath,
    current_decls: &[SourceContext<Decl>],
  ) -> Result<Self, MacroError> {
    // Reuses the exact same whole-program capture path the production
    // `run`/`test` commands use (`lib.rs::build_core_program`), rather
    // than re-checking `loaded`'s own already-checked `Decl`s directly —
    // `check_all_modules_capturing_core` needs UNCHECKED decls (re-read
    // from raw source text), since feeding it already-elaborated decls a
    // second time corrupts generic type variables (confirmed directly:
    // doing that naively broke every generic def in `init`, e.g.
    // `List.map`, with spurious "type mismatch: A vs <unknown>" errors).
    //
    // Also drop `Decl::MacroCall` entries before capturing — belt and
    // braces alongside the `current_path` fix above: `current_decls`
    // (once callers stop over-filtering it down to just one target def,
    // see `expand_reflect_type_info_decl`'s own comment) could still
    // contain other macro calls that would otherwise get re-expanded a
    // second time by the nested `type_check_module_decls_new_inner` call
    // below.
    let filtered_decls: Vec<SourceContext<Decl>> = current_decls
      .iter()
      .filter(|ctx| !matches!(ctx.value(), Decl::MacroCall { .. } | Decl::Generated(_)))
      .cloned()
      .collect();
    let extra_modules = vec![(current_path.clone(), filtered_decls)];
    // Trim `loaded` to just the modules this meta invocation could reach
    // — the `init` package plus the transitive `use`-closure of the file
    // being expanded — before re-capturing. The whole-program capture
    // this replaced fed the ENTIRE `loaded` set (for `check lang`, every
    // `lang/*.mo`) into one flat bare-key `program.inductives` map
    // (`lower_core_ir::lower_program`), so two independent modules
    // declaring the same bare type name collided: `init/meta.mo`'s
    // meta-language `MatchArm`/`Decl`/`Param` vs `lang/core_ir.mo`'s
    // `MatchArm` and `lang/types.mo`'s `Decl`/`Param`. Last insert won,
    // and `derive_cli_meta`'s `open`-aliased `match_arm`/`d_def`/
    // `meta_param` references lowered to `GlobalDef::Unresolved`, failing
    // `check lang` (the self-hosted `test` path resolves the same names
    // through its own scope mechanism and was unaffected). `derive_cli`
    // is the only macro actually invoked in `lang/`, and its
    // `derive_cli_meta` only depends on `lang.cli` (→ `std.list`,
    // `init.meta`), so the closure excludes the colliding compiler
    // modules and the meta-eval ends up seeing exactly the `loaded` set
    // the Rust `derive_cli_test` harness already builds — which passes.
    let trimmed_loaded = dep_closure_loaded(loaded, current_decls)?;
    let program: CoreProgram =
      crate::build_core_program(&trimmed_loaded, &extra_modules).map_err(|e| {
        MacroError::Generic(format!(
          "meta: failed to check + capture the loaded program: {e}"
        ))
      })?;
    let lowered: LoweredProgram = lower_program(&program).map_err(|e| {
      MacroError::Generic(format!("meta: failed to lower the captured program: {e:?}"))
    })?;
    let LoweredProgram {
      globals,
      natives,
      native_arities,
      paths,
      well_known,
      ..
    } = lowered;
    let globals = GlobalTable::new(globals);
    let natives = NativeTable::new(natives, native_arities, well_known);
    let cache = GlobalCache::new_pure(globals.len());
    Ok(MetaEvalContext {
      paths,
      globals,
      natives,
      cache,
    })
  }

  fn index_of(&self, path: &ModulePath) -> Option<u32> {
    self.paths.iter().position(|p| p == path).map(|i| i as u32)
  }

  /// Evaluate the def at `path` (e.g. `derive_lens`, `mpt("derive_lens")`
  /// — top-level Monad names are bare/single-segment, see
  /// `meta_reflect.rs`'s module doc comment) and apply it to `args` in
  /// order (ordinary curried application, one arg at a time).
  pub fn invoke(&mut self, path: &ModulePath, args: Vec<Value>) -> Result<Value, MacroError> {
    let idx = self.index_of(path).ok_or_else(|| {
      MacroError::Generic(format!(
        "meta: `{path}` has no compiled definition (not `use`d, or not a top-level `def`?)"
      ))
    })?;
    let mut value = core_eval::force_global(idx, &self.globals, &self.natives, &mut self.cache)
      .map_err(|e| MacroError::Generic(format!("meta: evaluating `{path}` failed: {e}")))?;
    for arg in args {
      value = core_eval::apply(value, arg, &self.globals, &self.natives, &mut self.cache)
        .map_err(|e| MacroError::Generic(format!("meta: applying `{path}` failed: {e}")))?;
    }
    Ok(value)
  }
}

/// Trim `loaded` down to just the modules a meta invocation rooted at
/// `current_decls` could actually reach: the `init` package (always —
/// `check_all_modules_capturing_core` → `type_check_module_decls_new_inner`
/// looks up the prelude in `loaded` and interns every loaded module's
/// defs as ground truth for cross-module resolution) plus the transitive
/// `use`-closure of the file being expanded. See `MetaEvalContext::build`
/// for why the whole-program capture this replaces caused a bare-key
/// collision in `program.inductives`.
///
/// The closure is seeded from `current_decls`' own `Decl::Use` entries
/// rather than `current_path` because the file being expanded is not
/// necessarily registered in `loaded` yet — the Rust `derive_cli_test`
/// harness, for instance, adds it only AFTER type-checking — so looking
/// it up by path would find nothing. Its own `use`s are in `current_decls`
/// regardless, and that's the seed the closure needs.
pub(crate) fn dep_closure_loaded(
  loaded: &LoadedModules,
  current_decls: &[SourceContext<Decl>],
) -> Result<LoadedModules, MacroError> {
  use std::collections::HashSet;

  // Init package is always kept — `build_core_program` captures it
  // separately, but the capturing checker still reads it back out of
  // `loaded` (prelude lookup + ground-truth interning), so a trimmed
  // `loaded` that dropped it would lose builtins. Use the exact same
  // path set `build_core_program` itself treats as init.
  let init_paths: crate::Set<ModulePath> = crate::term::module::init_package_sources()
    .map_err(|e| MacroError::Generic(format!("meta: loading init package: {e}")))?
    .into_iter()
    .map(|(p, _)| p)
    .collect();

  // BFS the transitive `use`-closure of the file being expanded.
  let mut visited: HashSet<ModulePath> = HashSet::new();
  let mut stack: Vec<ModulePath> = Vec::new();
  for ctx in current_decls {
    if let Decl::Use(u) = ctx.value() {
      stack.push(u.module_path().clone());
    }
  }
  let mut closure: HashSet<ModulePath> = HashSet::new();
  while let Some(path) = stack.pop() {
    if !visited.insert(path.clone()) {
      continue;
    }
    let Some(module) = loaded.get_module(&path) else {
      // A `use`d module not in `loaded` (e.g. resolved through a
      // different path, or not yet demand-loaded here) just isn't
      // captured — `build_core_program` re-reads captured modules from
      // disk via search paths, so the only cost is not traversing its
      // further `use`s; skip it rather than failing.
      continue;
    };
    closure.insert(path);
    for use_ctx in module.get_uses() {
      stack.push(use_ctx.value().module_path().clone());
    }
  }

  let kept: Vec<Module> = loaded
    .modules()
    .into_iter()
    .filter(|m| init_paths.contains(m.path()) || closure.contains(m.path()))
    .cloned()
    .collect();
  let mut trimmed = LoadedModules::from(kept);
  trimmed.set_search_paths(loaded.search_paths().clone());
  trimmed.set_test_mode(loaded.test_mode());
  Ok(trimmed)
}
