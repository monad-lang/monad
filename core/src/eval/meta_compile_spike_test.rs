//! Phase 0 spike for the reflection-as-data metaprogramming kernel plan
//! (`plans/review-and-reduce-the-greedy-nest.md`) — proves, standalone,
//! with no `std/derive.mo`/`init/meta.mo` involvement, that an already-
//! loaded dependency module's `def` can be re-type-checked ON DEMAND
//! (after the fact, not as part of its original load) with `CoreTerm`
//! capture turned on, lowered to `CoreIr`, and evaluated via
//! `core_eval::apply`/`force_global` — matching what the normal
//! whole-program path produces for the same def.
//!
//! This is the load-bearing assumption the rest of the plan depends on:
//! that `type_check_module_decls_new_inner`'s `core_out: Option<&mut
//! CoreProgram>` capture (Phase 0 of
//! `plans/implementations/core-term-closure-evaluator.md`) can be
//! invoked on a SINGLE decl, scoped down from the whole-module wrappers,
//! reusing an already-loaded `LoadedModules` as context — not something
//! any existing call site does today.
//!
//! Deliberately uses plain `I64` arithmetic (a direct `#[native]`, no
//! typeclass dictionary involved) rather than `Bool`/`if` — a first spike
//! doesn't need `WellKnownCtors` constructor-tag resolution (which needs
//! the *referenced* type's own `Decl::Type` re-captured into the
//! `CoreProgram` too, not just the def under test — a real, separate
//! finding worth carrying into the actual `TypeInfo`/`Expr` value work,
//! not something this narrow spike needs to solve).

use crate::core_check_module::type_check_module_decls_new_inner;
use crate::core_program::CoreProgram;
use crate::core_value::{Env, GlobalCache, GlobalTable, NativeTable, Value};
use crate::lower_core_ir::lower_program;
use crate::parser::parse_file;
use crate::term::module::{ParsedModule, default_modules, module};
use crate::term::{Decl, ModulePath, NumSuffix, SourceContext};

/// A tiny "dependency module" — analogous to `std/derive.mo` in the real
/// plan — loaded normally (fully parsed + type-checked, exactly as any
/// `use`d module is) so its `bump` def is available in `LoadedModules`
/// the ordinary way, with its `CoreTerm` already discarded (no capture
/// happened during this initial load, matching every existing call site).
fn load_helper_dependency() -> (crate::term::module::LoadedModules, ModulePath) {
  let mut loaded = default_modules().unwrap();
  let path = ModulePath::top("meta_spike_helper");
  let parsed = parse_file(
    r#"
    use init

    def bump (n : I64) : I64 := I64.add n 5
    "#
    .into(),
  )
  .unwrap();
  let checked = type_check_module_decls_new_inner(&path, parsed.decls, &loaded, None).unwrap();
  loaded.add_module(module(
    path.clone(),
    ParsedModule {
      decls: checked,
      module_doc: None,
    },
  ));
  (loaded, path)
}

#[test]
fn test_on_demand_core_ir_capture_and_eval_matches_expected_result() {
  let (loaded, helper_path) = load_helper_dependency();

  // Pull `bump`'s already-checked `Def` back out of the already-loaded
  // dependency — this is the "derive_lens already lives in std/derive.mo,
  // loaded as an ordinary dependency" step in the real plan.
  let module_ref = loaded
    .modules()
    .into_iter()
    .find(|m| m.path() == &helper_path)
    .expect("helper module should be loaded");
  let bump_path = ModulePath::top("bump");
  let def_ctx = module_ref.get_def(&bump_path).cloned().unwrap_or_else(|| {
    let names: Vec<String> = module_ref
      .defs()
      .iter()
      .map(|d| d.value().name.to_string())
      .collect();
    panic!("bump not found at {bump_path}; available def names: {names:?}")
  });

  // `bump`'s body references `I64.add`, an ordinary (native-backed) def
  // from a different, already-loaded module — proving transitive
  // dependencies can be captured too (not just a fully self-contained
  // def) is the more representative case for the real plan, where
  // `derive_lens` will similarly reference helper defs from
  // `init.optics`/`init.meta`. `CoreIr::Global` references to anything
  // NOT included in this decls list lower to `GlobalDef::Unresolved`
  // (a real, confirmed finding from this spike, not an assumption) — so
  // every transitively-referenced def needs to be re-checked-and-captured
  // in the same batch.
  let i64_add_path = loaded
    .modules()
    .into_iter()
    .find_map(|m| {
      m.defs()
        .into_iter()
        .find(|d| d.value().name.to_string() == "I64.add")
        .map(|d| d.value().name.clone())
    })
    .expect("I64.add should be a registered def in some loaded module");
  let i64_add_module = loaded
    .modules()
    .into_iter()
    .find(|m| m.get_def(&i64_add_path).is_some())
    .expect("the module owning I64.add should be found");
  let i64_add_def = i64_add_module.get_def(&i64_add_path).unwrap().clone();

  // Re-check JUST these two decls, ON DEMAND, with CoreTerm capture
  // turned on — this is the new, previously-unexercised path the whole
  // plan depends on. It must succeed against `loaded` alone (which
  // already fully contains everything both defs reference), without
  // needing either owning module's OTHER decls passed in again.
  let mut program = CoreProgram::new();
  let decls_to_capture = vec![
    SourceContext::no_ctx(Decl::Def(def_ctx.value().clone())),
    SourceContext::no_ctx(Decl::Def(i64_add_def.value().clone())),
  ];
  type_check_module_decls_new_inner(&helper_path, decls_to_capture, &loaded, Some(&mut program))
    .expect("on-demand multi-decl re-check with CoreTerm capture should succeed");

  assert!(
    program.defs.contains_key(&bump_path),
    "CoreProgram should have captured bump's CoreTerm body"
  );

  // Lower just this captured program to CoreIr and evaluate it via the
  // real production evaluator (core_eval), completely independent of the
  // normal whole-program `run`/`test` pipeline.
  let lowered = lower_program(&program).expect("lowering the captured program should succeed");
  let idx = lowered
    .index_of(&bump_path)
    .expect("bump should have a global slot in the lowered program");

  let globals = GlobalTable::new(lowered.globals);
  let natives = NativeTable::new(lowered.natives, lowered.native_arities, lowered.well_known);
  let mut cache = GlobalCache::new(globals.len());

  let ten = Value::Lit(crate::core_ir::IrLit::Num(10, NumSuffix::I64));
  let global_closure = crate::core_eval::force_global(idx, &globals, &natives, &mut cache)
    .expect("forcing bump's global should succeed");
  let result = crate::core_eval::apply(global_closure, ten, &globals, &natives, &mut cache)
    .expect("applying bump to 10 should succeed");

  match result {
    Value::Lit(crate::core_ir::IrLit::Num(n, _)) => {
      assert_eq!(n, 15, "bump 10 should evaluate to 15");
    }
    other => panic!("expected a numeric literal, got: {other:?}"),
  }
  let _ = Env::nil(); // sanity: Env is importable/constructible from here too
}
