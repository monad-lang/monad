//! Module-level parity harness — Phases 3-4 of
//! `plans/implementations/typechecker-de-bruijn-core.md`.
//!
//! Runs the new `CoreTerm`/`core_check` pipeline against real, parsed
//! `.mo` source, one top-level `def` at a time, and reports per-def
//! success/failure/skip. **This does not replace or gate the real
//! checker** — `core/src/eval/type.rs`'s `type_check`/`type_check_module_decls`
//! remain the sole authoritative path; nothing here is wired into the CLI
//! or `cargo run -- test`. This is purely a measurement tool for tracking
//! how far the new checker's real-file coverage has gotten.
//!
//! `Bool`/`I64`/`String`/etc. are NOT a special hardcoded "primitive"
//! category here — they're ordinary `type` declarations (with native
//! representations) living in `init/prelude.mo`, resolved the exact same
//! way as any other loaded name. This harness gets its ground truth for
//! "what names exist and what are their real (already-elaborated) types"
//! from the SAME machinery the real checker uses:
//! - `crate::term::module::default_modules()` — loads and fully
//!   type-checks prelude/id/io/number/math/string/init/process, exactly
//!   as the CLI does. Every `def`'s and every inductive constructor's
//!   type is read directly from this — never re-derived.
//! - `crate::eval::r#type::elaborate_decls` — the real implicit-`Forall`
//!   elaboration pass (adds `{A : Type}` for a `def`'s free lowercase
//!   type variables), run on the file being checked before anything else
//!   touches it, using `default_modules()`'s actual known-names set.
//! - `crate::eval::macro_expand::expand_macros` — real macro expansion,
//!   run immediately after elaboration, matching
//!   `type_check_module_decls`'s own pipeline order and this whole
//!   redesign's standing rule that lowering must run strictly after
//!   macro expansion (`Quote`/hygiene need names).
//!
//! Everything downstream of that (lowering `Term`→`CoreTerm`, and
//! `core_check::infer`/`check`) is this redesign's own new code — that's
//! the actual thing being measured.
//!
//! Still-deliberate gaps in this increment:
//! - `use`-declared modules outside `default_modules()`'s fixed embedded
//!   set (e.g. `std.test`) ARE now loaded on demand, from disk, via the
//!   real recursive loader (`term::module::load_module_files`, with
//!   `SearchPaths` anchored at the repo root — see `repo_search_paths`),
//!   and their own defs/inductives/infix operators are registered exactly
//!   like `default_modules()`'s are. This also fully type-checks each
//!   loaded dependency with the OLD checker, as a side effect of loading
//!   it (required for it to be usable as `loaded` context at all).
//! - `type`/`instance` declarations in the file being checked itself are
//!   still skipped as top-level decls, not checked — only their
//!   constructors/class methods get registered (via `register_type_decls`/
//!   `register_inductive`), so other `def`s can reference them.
//!   `instance` bodies specifically are never checked at all — see the
//!   typeclass note below.
//! - Native-op signatures (`Ntv`) are treated as opaque and trusted
//!   against whatever the call site expects (mirrors the real checker's
//!   own `Ntv` handling exactly) — not a real signature registry, but not
//!   an unconditional `CannotInfer` either.
//! - Struct literals (`Lit(StructLit)`) still can't be inferred/checked at
//!   all — `core_check::infer_lit` unconditionally returns `CannotInfer`.
//!   The real checker resolves a struct literal's constructor by reading
//!   its STRUCT NAME off the *expected* type (`eval/type.rs`'s `Lit`/
//!   `StructLit` arm, keyed on `expected_type` being a `Var` naming an
//!   inductive) — replicating that here needs `core_check::check` to
//!   consult module-level struct/inductive definitions
//!   (`ModuleCheckEnv`'s `known_globals`/an inductive registry), which
//!   `core_check.rs` deliberately has no access to today (it only knows
//!   about `TyCtx`, not "which fields does struct X have"). Not attempted
//!   in this increment — affects `examples/structs.mo` (mostly) and
//!   `examples/optics.mo` (partially).
//! - **Typeclass method dispatch is a coarse approximation, not real
//!   dictionary passing** — `register_inductive` registers each class
//!   method (`BEq.beq`, `Append.append`) under its CLASS's declared
//!   signature (e.g. `{A : Type} -> A -> A -> Bool`), reusing the same
//!   already-elaborated type `eval::type::elaborate_inductive` computes
//!   for it, with no check that an instance actually exists for whatever
//!   `A` gets solved to. Good enough for ordinary application/unification
//!   to type-check correctly in the common case (this is precisely what
//!   unblocked `std/list.mo`'s remaining defs — see below) but doesn't
//!   validate instance existence or resolve to a specific instance's
//!   implementation. Real compile-time instance resolution via dictionary
//!   passing (inserting explicit dictionary arguments at call sites,
//!   validating an instance exists) is a separate, already-tracked goal —
//!   see `plans/implementations/dictionary-passing-instance-resolution.md`
//!   — and this harness's approximation is deliberately a stepping stone
//!   toward it, not a competing design: once real dictionary elaboration
//!   exists, a class method reference should resolve through THAT
//!   machinery (an elaborated dictionary-parameter application) rather
//!   than this coarse "just use the class's bare signature" registration.
//!
//! **`Decl::Open` handling**: `open X` makes every name `X` exports
//! resolvable unqualified (`open Bool` → bare `true` means `Bool.true`).
//! Reusing the real ground truth again rather than reinventing
//! resolution: `crate::term::ModulePath::open(&self, opens: &Vec<&Open>)
//! -> Vec<ModulePath>` (already used by the real `Scope`/`GlobalScope`
//! machinery) computes, for one fully-qualified name, every short form
//! the currently-active `open`s make it reachable under. This harness
//! runs that over every name in `known_globals` (every `default_modules()`
//! def/constructor, plus the file's own) against the *active* opens
//! (`ModuleCheckEnv`'s loaded prelude module's own opens — which the real
//! `Scope` also always chains in, since prelude's `open Bool` etc. are
//! meant to be ambiently available everywhere — plus the file's own
//! `Decl::Open`s), producing an unqualified-name → `Atom` alias table fed
//! into `lower_core::LowerConfig::unqualified_aliases`.
//!
//! `ModuleCheckEnv` bundles the expensive-to-build ground truth
//! (`default_modules()`'s full load-and-typecheck, plus the `ctx`/`infix`/
//! `known_globals` derived from it) into one explicit struct that callers
//! construct and pass in, rather than hiding it behind a process-wide
//! lazy static — the cost and the dependency are both visible at every
//! call site that needs them.

use crate::Map;
use crate::core_check::{
  ClassMethodInfo, ConstructorInfo, DictScope, InferError, KnownClassMethods, KnownInstanceInfo,
  KnownInstances, StructFields, StructInfo, StructKind, TyCtx, check, desugar_struct_literals,
  head_atom_of, infer, is_class_atom,
};
use crate::core_program::{
  CheckedCoreDef, CoreConstructorInfo, CoreInductiveInfo, CoreInstanceInfo, CoreProgram,
};
use crate::core_term::{Atom, AtomTable, CoreLit, CoreTerm, DebugName, close, open_with};
use crate::core_unify::{MetaContext, UnifyError, generalize, zonk};
use crate::eval::macro_expand::expand_macros;
use crate::eval::termination::check_termination_all;
use crate::eval::r#type::{TypeError, check_strict_positivity, elaborate_decls};
use crate::lower_core::{LowerConfig, LowerContext, LowerError, lower_term};
use crate::parser::{ModuleContext, parse_file};
use crate::raise_core::raise_core;
use crate::term::module::{LoadedModules, ScopeError, default_modules, load_module_files};
use crate::term::{
  Decl, Def, Identifier, Inductive, InductiveVariant, Instance, Literal, ModulePath, Multiplicity,
  NameRef, Named, Open, Operator, SearchPaths, SourceContext, SourceRange, Term, TypeConstraint,
  Typed, constructor, def, forall,
};

/// `init/prelude.mo`'s own module path — `'prelude` (with the leading
/// apostrophe) is the exact internal path `term::module::init_module`
/// loads it under; duplicated here (rather than exported) since it's an
/// internal implementation detail of module loading, not public API.
/// Used to find prelude's own `open` declarations (`open Bool`, `open
/// Unit`, ...), which the real `GlobalScope` always chains into every
/// module's resolution — see `GlobalScope::for_module`'s "opens from
/// current module and prelude" handling.
fn prelude_path() -> ModulePath {
  ModulePath::top("'prelude")
}

/// Search paths anchored at the repo root (the parent of the `core` crate's
/// own manifest dir), used to resolve `use`-declared modules that live on
/// disk outside `default_modules()`'s fixed embedded set (e.g. `std.test`,
/// `std.show`) — mirrors the CLI's own `build_default_search_paths`
/// (`lib.rs`), minus the CWD/`MONAD_PATH` bits this harness doesn't need.
fn repo_search_paths() -> SearchPaths {
  let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
  let repo_root = manifest_dir
    .parent()
    .expect("core crate's manifest dir has a parent directory");
  SearchPaths::new(vec![repo_root.to_path_buf()])
}

/// Everything `check_module_source` needs that's expensive to build
/// (`default_modules()` parses and fully type-checks
/// prelude/id/io/number/math/string/init/process) and doesn't change
/// between calls — built explicitly by the caller via `ModuleCheckEnv::new()`
/// and passed in, rather than hidden behind a process-wide lazy static:
/// callers control exactly when that cost is paid and the dependency is
/// visible in every signature that needs it.
pub struct ModuleCheckEnv {
  loaded: LoadedModules,
  /// Every `default_modules()` `def`/constructor's REAL, already-elaborated
  /// type, lowered once and keyed by its atom.
  ctx: TyCtx,
  infix: Map<Operator, ModulePath>,
  /// Every registered name's fully-qualified path → its atom — the input
  /// `compute_unqualified_aliases` needs to work out what a file's active
  /// `open`s make reachable unqualified.
  known_globals: Map<ModulePath, Atom>,
  /// Every known struct-like inductive's field names/types — see
  /// `core_check::StructFields`'s doc comment.
  structs: StructFields,
  /// Global-name interning table, populated while building the rest of
  /// this ground truth — `check_module_source` clones this to seed its
  /// own per-call `MetaContext` (`MetaContext::new_with_atoms`), so a
  /// name interned here (e.g. "Bool", from `default_modules()`) and the
  /// same name referenced again while checking a file resolve to the
  /// identical `Atom`, without a process-wide global.
  atoms: AtomTable,
}

impl ModuleCheckEnv {
  pub fn new() -> Self {
    let loaded = default_modules().expect("default_modules() must load");
    let mut atoms = AtomTable::new();
    let GroundTruth {
      ctx,
      infix,
      known_globals,
      structs,
    } = ground_truth_from_loaded(&loaded, &mut atoms);
    Self {
      loaded,
      ctx,
      infix,
      known_globals,
      structs,
      atoms,
    }
  }
}

/// Build the same kind of ground truth `ModuleCheckEnv::new()` builds from
/// `default_modules()` (every currently-loaded module's def/constructor
/// types, infix operators, and struct-field registrations), but from
/// WHATEVER `LoadedModules` the caller has — not hardcoded to
/// `default_modules()`'s fixed 8-file set. Needed by
/// `type_check_module_decls_new` (B0c of
/// `plans/implementations/typechecker-de-bruijn-core.md`'s cutover phase),
/// which is called for arbitrary modules being loaded from disk (where
/// `loaded` is whatever's been loaded so far, not the fixed default set) —
/// factored out so the real cutover entry point and this harness's own
/// `ModuleCheckEnv` share one implementation rather than drifting apart.
///
/// KNOWN GAP: this registers every def from every loaded module into one
/// flat, ungated namespace (both bare and qualified names) — there is no
/// per-consuming-module scoping here at all, so neither `use Module
/// {name}` selective-import filtering nor `priv`/`pub` visibility
/// (`visibility-declarations.md`) is enforced by this checker. (Scope
/// resolution proper — `GlobalScopeData::from_module`/`from_modules` in
/// `term/module.rs`, always used by the LSP and by every checked module's
/// own `Scope` — DOES enforce both, since it works directly off each
/// decl's own `vis` field regardless of which checker validated it — see
/// `DefRef.vis`/`Visibility::Priv` filtering there.) Closing this gap for
/// THIS checker's own flat namespace means giving it real per-module
/// scoped resolution here, which is a substantially larger, separate
/// undertaking than adding `priv`/`pub` itself — tracked as follow-up
/// work, not attempted in this pass.
pub struct GroundTruth {
  pub ctx: TyCtx,
  pub infix: Map<Operator, ModulePath>,
  pub known_globals: Map<ModulePath, Atom>,
  pub structs: StructFields,
}

pub fn ground_truth_from_loaded(loaded: &LoadedModules, atoms: &mut AtomTable) -> GroundTruth {
  let mut infix = Map::new();
  for module in loaded.modules() {
    for infix_ctx in module.infix() {
      infix.insert(infix_ctx.operator().clone(), infix_ctx.name().clone());
    }
  }
  let mut ctx: TyCtx = TyCtx::new();
  let mut known_globals: Map<ModulePath, Atom> = Map::new();
  let mut structs = StructFields::new();
  let config = LowerConfig {
    infix: infix.clone(),
    ..Default::default()
  };
  // E7: `Type`/`Prop`/`Pred` used AS VALUES (`get_sort Type`, not just as
  // types themselves) — the OLD checker resolves these via its own,
  // entirely separate `Module::get_def_refs`/`Builtins` mechanism
  // (`term/module.rs`: "Type" -> `sort1()`, both term AND type; "Prop"/
  // "Pred" -> `sort0()`, both term and type — "Pred" is a plain alias for
  // "Prop", same value), never routed through the ordinary `.mo`-file def
  // registration this checker's own `ctx`/`known_globals` are built from.
  // Registered here so both this diagnostic harness AND the real
  // `type_check_module_decls_new` entry point (which also calls this
  // function) see them, since the runtime's own evaluation of a raised
  // `Free`/`Var` reference to "Type"/"Prop"/"Pred" already goes through
  // that same separate `Builtins` mechanism regardless of which checker
  // validated it.
  for (name, sort) in [
    ("Type", CoreTerm::Sort { level: 1 }),
    ("Prop", CoreTerm::Sort { level: 0 }),
    ("Pred", CoreTerm::Sort { level: 0 }),
  ] {
    let path = ModulePath::top(name);
    let atom = atoms.intern(path.clone());
    known_globals.insert(path, atom);
    ctx.insert(atom, sort);
  }
  for module in loaded.modules() {
    for def_ctx in module.defs() {
      let def: &Def = def_ctx;
      let atom = atoms.intern(def.name.clone());
      known_globals.insert(def.name.clone(), atom);
      let ty_c = lower_term(
        &mut LowerContext::with_config(config.clone(), atoms),
        &def.typ,
      )
      .ok();
      if let Some(ty_c) = &ty_c {
        ctx.insert(atom, ty_c.clone());
      }
      // A def's own name (e.g. `greet`) may be bare, without its enclosing
      // module's path prefix, but external references still qualify it
      // (e.g. `mylib.greet`), which `lower_term` resolves to a *different*
      // atom (atoms are keyed by the full `ModulePath`). Register that
      // qualified atom too so both forms type-check to the same type.
      let qualified = module.path().clone().extend(def.name.clone());
      if qualified != def.name {
        let qualified_atom = atoms.intern(qualified.clone());
        known_globals.insert(qualified, qualified_atom);
        if let Some(ty_c) = &ty_c {
          ctx.insert(qualified_atom, ty_c.clone());
        }
      }
    }
    for ind in module.inductives() {
      register_inductive(
        &mut ctx,
        &mut known_globals,
        &mut structs,
        ind,
        &config,
        atoms,
      );
    }
  }
  GroundTruth {
    ctx,
    infix,
    known_globals,
    structs,
  }
}

/// Every class method's atom, across every loaded module's classes plus
/// the file's own — see `core_check::KnownClassMethods`'s doc comment.
/// Dispatch is always on the class's FIRST param (`class_param_name`)
/// alone, even for a multi-param class (`class HMul A B C {...}`) — every
/// multi-param class instance in practice is homogeneous across its
/// params (`instance HMul F64 F64 F64`, never e.g. both `HMul I64 I64
/// I64` and `HMul I64 F64 F64` for the same first arg), matching
/// `collect_known_instances`'s own key (also just the first arg). A
/// class with zero params can't be dispatched on at all — skipped, same
/// as `ind.variant() != Class`.
fn collect_known_class_methods(
  loaded: &LoadedModules,
  expanded: &[SourceContext<Decl>],
  atoms: &mut AtomTable,
) -> KnownClassMethods {
  let mut out = KnownClassMethods::new();
  let mut visit = |ind: &Inductive, atoms: &mut AtomTable| {
    if *ind.variant() != InductiveVariant::Class {
      return;
    }
    let Some(param) = ind.params().first() else {
      return;
    };
    let Some(cons) = ind.constructors().first() else {
      return;
    };
    let default_type = param.default.as_deref().and_then(term_head_path);
    for method in &cons.params {
      let method_path = ind.name().clone().extend(method.name.clone().to_path());
      let atom = atoms.intern(method_path);
      out.insert(
        atom,
        ClassMethodInfo {
          class_path: ind.name().clone(),
          class_param_name: param.name.clone(),
          method_name: method.name.clone(),
          default_type: default_type.clone(),
        },
      );
    }
  };
  for module in loaded.modules() {
    for ind in module.inductives() {
      visit(ind, atoms);
    }
  }
  for decl in expanded {
    if let Decl::Type(ind) = &**decl {
      visit(ind, atoms);
    }
  }
  out
}

/// A class's own declared method names, in declaration order — needed to
/// build a dictionary `Con` value from an `instance`'s `impls_map` (a
/// `Map<Identifier, Def>`, unordered by name): a `Con`'s `args` are
/// positional, so an instance's method implementations must be placed in
/// exactly the same order the class declared them in, not whatever order
/// they happen to be written in the `instance` block itself (which the
/// language doesn't require to match).
fn collect_class_method_order(
  loaded: &LoadedModules,
  expanded: &[SourceContext<Decl>],
) -> Map<ModulePath, Vec<Identifier>> {
  let mut out = Map::new();
  let mut visit = |ind: &Inductive| {
    if *ind.variant() != InductiveVariant::Class {
      return;
    }
    let Some(cons) = ind.constructors().first() else {
      return;
    };
    out.insert(
      ind.name().clone(),
      cons.params.iter().map(|p| p.name.clone()).collect(),
    );
  };
  for module in loaded.modules() {
    for ind in module.inductives() {
      visit(ind);
    }
  }
  for decl in expanded {
    if let Decl::Type(ind) = &**decl {
      visit(ind);
    }
  }
  out
}

/// Every `instance`'s `(class, concrete-type-head) -> instance-name`
/// entry, across every loaded module's instances plus the file's own —
/// see `core_check::KnownInstances`'s doc comment.
/// Needs `structs`/`atoms`/`infix` (for `term_references_class`, to
/// compute each instance method's own `method_constraints` — see
/// `KnownInstanceInfo`'s doc comment) — called after `register_type_decls`
/// has fully populated `structs`, not at this file's original call site
/// (right after parsing, before any of those exist).
fn collect_known_instances(
  loaded: &LoadedModules,
  expanded: &[SourceContext<Decl>],
  structs: &StructFields,
  atoms: &mut AtomTable,
  infix: &Map<Operator, ModulePath>,
) -> KnownInstances {
  let mut out = KnownInstances::new();
  let mut visit = |instance: &crate::term::Instance, atoms: &mut AtomTable| {
    let Some(first_arg) = instance.args.first() else {
      return;
    };
    let Some(type_path) = term_head_path(first_arg) else {
      return;
    };
    // Mirrors `elaborate_constrained_type`'s own per-constraint
    // `term_references_class` decision (this same file) — the same
    // question, asked here per (method, constraint) pair instead of
    // during `check_one_def_new`, so `try_resolve_class_method` can look
    // it up directly instead of re-deriving it (or, as an earlier
    // version of this code did, ignoring it and appending every
    // instance-level constraint to every method uniformly).
    let method_constraints: Map<Identifier, Vec<TypeConstraint>> = instance
      .impls_map
      .iter()
      .map(|(method_name, def)| {
        let wrapped = instance
          .constraints
          .iter()
          .filter(|c| term_references_class(&def.term, c.class(), structs, atoms, infix))
          .cloned()
          .collect();
        (method_name.clone(), wrapped)
      })
      .collect();
    out.insert(
      (instance.class_name.clone(), type_path),
      KnownInstanceInfo {
        prefix: instance.name().clone(),
        constraints: instance.constraints.clone(),
        method_constraints,
      },
    );
  };
  for module in loaded.modules() {
    for instance in module.instances() {
      visit(instance, atoms);
    }
  }
  for decl in expanded {
    if let Decl::Ins(instance) = &**decl {
      visit(instance, atoms);
    }
  }
  out
}

/// The head `ModulePath` of a type-level application chain (`List A` ->
/// `List`, bare `List` -> `List`) — used to match an instance's own
/// first type argument (as written) against a concrete type's own path.
fn term_head_path(t: &Term) -> Option<ModulePath> {
  match t {
    Term::Var { name } => name.clone().to_path(),
    Term::App { fun, .. } => term_head_path(fun),
    Term::Ctx { term, .. } => term_head_path(term),
    _ => None,
  }
}

impl Default for ModuleCheckEnv {
  fn default() -> Self {
    Self::new()
  }
}

/// Register every name a single `type` declaration introduces: ordinary
/// constructors for `Struct`/`Generic` inductives (`List`'s `empty`/
/// `cons`), or — for `class` declarations, which are themselves
/// represented as an `Inductive` with `variant() ==
/// &InductiveVariant::Class` and exactly one constructor whose `params`
/// are the class's methods (confirmed by reading
/// `Module::get_class_def_refs`, the real `Scope`'s own class-method
/// lookup helper) — each method (`BEq.beq`, `Append.append`).
/// `elaborate_decls` (already run on the whole file/on `default_modules()`
/// before this is called) has already wrapped each method's type in the
/// class's own implicit Foralls (`eval::type::elaborate_inductive`'s
/// `is_class` branch), so — same as for ordinary constructors — no
/// per-method elaboration step is needed here.
///
/// This is a coarse approximation, not real typeclass dictionary passing:
/// a method resolves to its CLASS's declared signature (e.g. `BEq.beq :
/// {A : Type} -> A -> A -> Bool`), with no check that an instance
/// actually exists for whatever `A` later gets solved to. That's enough
/// for ordinary application/unification to type-check correctly in the
/// common case (ordinary code calling a class method on a type that DOES
/// have an instance, which is the overwhelming majority of real usage) —
/// real per-instance dictionary resolution is a further, deeper gap (see
/// the module doc), not attempted here.
fn register_inductive(
  ctx: &mut TyCtx,
  known_globals: &mut Map<ModulePath, Atom>,
  structs: &mut StructFields,
  ind: &Inductive,
  config: &LowerConfig,
  atoms: &mut AtomTable,
) {
  if *ind.variant() == InductiveVariant::Class {
    let Some(cons) = ind.constructors().first() else {
      return;
    };
    for method in &cons.params {
      let method_path = ind.name().clone().extend(method.name.clone().to_path());
      let atom = atoms.intern(method_path.clone());
      known_globals.insert(method_path.clone(), atom);
      if let Ok(ty_c) = lower_term(
        &mut LowerContext::with_config(config.clone(), atoms),
        &method.typ,
      ) {
        ctx.insert(atom, ty_c);
      }
    }
    // The class's own atom, registered as a "struct" type too — a
    // dictionary (an instance's own value) has exactly this shape: one
    // field per method, in declaration order — matching a `struct`'s
    // existing `StructFields` registration below almost exactly. The one
    // difference: each method's OWN surface type (`method.typ`) is
    // *individually* `Forall`-wrapped (per `elaborate_inductive`'s
    // class-branch, which wraps each method's type separately — NOT the
    // whole constructor once, the way a regular struct's `cons.typ` is),
    // over BOTH the class's own param AND, for a method like
    // `Foldable.foldr`, its own additional generics (`A`/`B`) — in no
    // guaranteed order. So instead of `peel_foralls`ing `cons.typ` as a
    // whole (the regular-struct approach, which doesn't apply here), peel
    // each method's OWN Forall chain one layer at a time, opening the
    // layer whose name matches the class's own declared param with ONE
    // shared, fresh atom (minted once, up front, so every field agrees
    // on the same concrete-type-to-be, the way a real instance's fields
    // must) — and any OTHER layer (a method-own generic, unrelated to the
    // class) with its own, independently-fresh atom.
    if let Some(class_param_name) = ind.params().first().map(|p| p.name.clone()) {
      let class_param_atom = Atom::fresh();
      let mut fields = Vec::with_capacity(cons.params.len());
      for method in &cons.params {
        if let Ok(method_ty_c) = lower_term(
          &mut LowerContext::with_config(config.clone(), atoms),
          &method.typ,
        ) {
          // Peel every leading `Forall` layer, substituting the class's
          // own param layer with the shared `class_param_atom` (dropped
          // from the result — a concrete instance fixes it) but, unlike
          // an earlier version of this loop, RE-WRAPPING any other
          // (method-own, e.g. `cons`'s own `A`) layer as a real `Forall`
          // again instead of also permanently opening it with its own
          // one-off fresh atom. That one-off atom used to leak into this
          // stored field type as if it were some fixed, already-concrete
          // type — harmless as long as only `project_dict_field` read
          // these fields (it only needs their NAMES/count, never the
          // type), but this same `fields` list also now backs `structs.
          // constructors`' `match_case_field_types` lookup (below),
          // which DOES use the type — feeding it a one-off hardcoded
          // atom instead of a real, freshly-instantiable `Forall` made
          // every use of a method with its own generic (`FromListLiteral
          // .cons`'s `A`, applied to a DIFFERENT concrete element type at
          // every list literal) fail to unify against the second and
          // subsequent call sites' own concrete argument type — two
          // unrelated rigid `Free` atoms can never unify with each other.
          let mut current = method_ty_c;
          let mut own_generics: Vec<(DebugName, CoreTerm, Atom)> = Vec::new();
          while let CoreTerm::Forall { dbg, typ, body } = current {
            if matches!(&dbg, DebugName::Named(n) if *n == class_param_name) {
              current = open_with(&body, &CoreTerm::Free(class_param_atom));
            } else {
              let atom = Atom::fresh();
              own_generics.push((dbg, *typ, atom));
              current = open_with(&body, &CoreTerm::Free(atom));
            }
          }
          let mut result = current;
          for (dbg, typ, atom) in own_generics.into_iter().rev() {
            result = CoreTerm::Forall {
              dbg,
              typ: Box::new(typ),
              body: Box::new(close(&result, atom)),
            };
          }
          fields.push((method.name.clone(), result));
        }
      }
      let class_atom = atoms.intern(ind.name().clone());
      // Unlike a method (`BEq.eq`), nothing referenced the class's own
      // BARE name before D3 — a dictionary parameter's type (`BEq K`,
      // `App(Free(class_atom), ...)`) is the first thing that does, so it
      // needs `known_globals`/`atom_paths` registered here too, or
      // `raise_core` panics the moment any def's elaborated type or body
      // embeds a `Free(class_atom)` dictionary-type reference.
      known_globals.insert(ind.name().clone(), class_atom);
      // Also register the class's dictionary shape under `structs.
      // constructors`, keyed exactly the way `project_dict_field` builds
      // its projection (`Match{scrutinee, cases: [{name: class_path.
      // last(), ...}]}`, one field per method in this SAME declaration
      // order) — `match_case_field_types` (E2's real-field-types lookup,
      // used by `infer`'s own `Match` handling) only ever consults THIS
      // map, never `structs.structs` below. Without this, `infer`ring a
      // class-method call site's own dictionary projection (e.g. `[1, 2,
      // 3]`'s desugared `FromListLiteral.cons`, or `BEq.beq`'s instance
      // dict) always fell back to `Hole` for the projected method's type,
      // so applying it to concrete arguments never pinned down anything —
      // the class param stayed an unresolved meta with no head atom,
      // silently failing `try_resolve_class_method`'s later resolution
      // and leaving the call site un-desugared (evaluated via `eval.rs`'s
      // runtime class-dispatch fallback instead of the real instance).
      structs.constructors.insert(
        (class_atom, ind.name().last().clone()),
        ConstructorInfo {
          param_atoms: vec![class_param_atom],
          fields: fields.iter().map(|(_, ty)| ty.clone()).collect(),
        },
      );
      structs.structs.insert(
        class_atom,
        StructInfo {
          kind: StructKind::Class,
          fields,
          defaults: Map::new(),
        },
      );
    }
  } else {
    for ctor in ind.constructors() {
      let ctor_atom = atoms.intern(ctor.name().clone());
      known_globals.insert(ctor.name().clone(), ctor_atom);
      if let Ok(ctor_ty_c) = lower_term(
        &mut LowerContext::with_config(config.clone(), atoms),
        &ctor.typ,
      ) {
        ctx.insert(ctor_atom, ctor_ty_c);
      }
    }
    // An ordinary (non-Class) inductive's own BARE name (`List`, `Option`)
    // never otherwise becomes a `known_globals` entry — only its
    // constructors (`List.cons`, `Option.some`) do, just above. But
    // `try_resolve_class_method` resolves a class param's concrete type by
    // looking up its atom's `ModulePath` (to key `known_instances` with —
    // e.g. `Foldable T` unifying `T := Option`), and without ANY record of
    // "Option"'s own atom, that lookup silently fails, resolution bails
    // out, and the call falls through to `eval.rs`'s OLD runtime
    // class-dispatch fallback (whichever instance happens to be tried
    // first — wrong result, not even an error). Recorded into `structs`'
    // own `inductive_paths` — NOT `known_globals` — deliberately: see
    // `StructFields::inductive_paths`'s doc comment for why inserting it
    // into `known_globals` (which also feeds `open`-based unqualified-name
    // aliasing) is the wrong place for this.
    structs
      .inductive_paths
      .insert(atoms.intern(ind.name().clone()), ind.name().clone());
    // E2: every ordinary constructor's own field types, in declaration
    // order, still referencing the inductive's own declared params freely
    // (NOT yet substituted with any specific use site's concrete type
    // arguments — `match_case_field_types`, `core_check.rs`, does that,
    // using `param_atoms` below to know which atom is which position).
    // Lets a `match` expression give its pattern-bound variables their
    // real field types instead of `Hole` — needed for a class-method call
    // inside a match arm on a pattern-bound variable (`cons a tail => ...
    // Foldable.foldr f z tail ...`) to resolve at all, since `Hole`
    // unifies with anything without binding any metavariable. Peels each
    // constructor's OWN `Forall`-wrapped type ONCE per constructor (not
    // shared across constructors, since each may bind fresh atoms) but
    // records the SAME LOGICAL param, across every constructor of this
    // ONE inductive, under a consistent position — matched positionally
    // against `ind.params()` by peel order (`elaborate_inductive` Forall-
    // wraps every constructor over the SAME declared param list, in the
    // same order, so this holds for every constructor of one inductive).
    let inductive_atom = atoms.intern(ind.name().clone());
    for ctor in ind.constructors() {
      if let Ok(ctor_ty_c) = lower_term(
        &mut LowerContext::with_config(config.clone(), atoms),
        &ctor.typ,
      ) {
        let (peeled_vars, mut current) = peel_foralls(ctor_ty_c);
        let param_atoms: Vec<Atom> = peeled_vars.iter().map(|(_, atom, _)| *atom).collect();
        let mut fields = Vec::new();
        while let CoreTerm::Pi { arg, ret, .. } = current {
          fields.push(*arg);
          current = open_with(&ret, &CoreTerm::Free(Atom::fresh()));
        }
        structs.constructors.insert(
          (inductive_atom, ctor.name().last().clone()),
          ConstructorInfo {
            param_atoms,
            fields,
          },
        );
      }
    }
    // A struct-like inductive (exactly one constructor — covers both
    // `struct X {...}` declarations and any other single-constructor
    // "product" inductive) also gets its OWN atom (not its constructor's)
    // registered with its field names/types, so `core_check::check`'s
    // `Lit(StructLit)` arm can resolve `{ x := 1, y := 2 }`-style literals
    // against it — see `core_check::StructFields`'s doc comment.
    if let Some(cons) = ind.constructors().first()
      && ind.constructors().len() == 1
    {
      let struct_atom = atoms.intern(ind.name().clone());
      // A generic struct's field types (e.g. `Lens S A`'s `get: S -> A`,
      // or `Any`'s constructor-level `any {A} (value: A)`) reference type
      // params that are only ever bound as part of `cons.typ`'s own
      // `Forall` wrapping (added by `elaborate_inductive`/
      // `constructor_parser` for the inductive's own declared params AND
      // any constructor-level implicit params — the latter aren't
      // recorded anywhere else `register_inductive` can see). Lowering
      // each `field.typ` on its own, with nothing bound, would see a bare
      // `S`/`A` as genuinely free, falling through to the GLOBAL atom
      // fallback and conflating every generic struct's same-named param
      // (overwhelmingly common: "A" is used everywhere) into one shared
      // atom. Instead, lower+peel `cons.typ` itself (correctly binding
      // every such param with a fresh, struct-local atom) and walk its
      // resulting Pi-chain to recover each field's now-properly-resolved
      // type, positionally matching `cons.params`' names in order.
      let mut fields = Vec::with_capacity(cons.params.len());
      if let Ok(ctor_ty_c) = lower_term(
        &mut LowerContext::with_config(config.clone(), atoms),
        &cons.typ,
      ) {
        let (_, mut current) = peel_foralls(ctor_ty_c);
        for field in &cons.params {
          let CoreTerm::Pi { arg, ret, .. } = current else {
            break;
          };
          fields.push((field.name.clone(), *arg));
          current = open_with(&ret, &CoreTerm::Free(Atom::fresh()));
        }
      }
      // E5: a field's own default value (`h: I64 := 100`) — lowered
      // separately from its type above, since a default is an ordinary
      // (usually literal, non-generic) value expression, not something
      // needing the same peeled-Forall substitution dance. NOTE: `stru()`
      // (term.rs) strips each field's `default_value` while building
      // `cons.params` (via `param_with_mult`, which has no default slot) and
      // instead collects them separately onto the `Inductive`'s own
      // `defaults: Map<Identifier, Term>` field — so the source here is
      // `ind.defaults()`, NOT `field.default` on `cons.params` (always
      // `None` for a struct's constructor).
      let defaults: Map<Identifier, CoreTerm> = ind
        .defaults
        .iter()
        .filter_map(|(name, default)| {
          let default_c = lower_term(
            &mut LowerContext::with_config(config.clone(), atoms),
            default,
          )
          .ok()?;
          Some((name.clone(), default_c))
        })
        .collect();
      structs.structs.insert(
        struct_atom,
        StructInfo {
          kind: StructKind::Struct,
          fields,
          defaults,
        },
      );
    }
  }
}

/// Register the file-under-test's OWN `type` declarations (constructors
/// and, per `register_inductive`, class methods) into `ctx`/
/// `known_globals` — `ModuleCheckEnv` only covers `default_modules()`'s,
/// not ones the file itself declares.
fn register_type_decls(
  ctx: &mut TyCtx,
  known_globals: &mut Map<ModulePath, Atom>,
  structs: &mut StructFields,
  decls: &[SourceContext<Decl>],
  config: &LowerConfig,
  atoms: &mut AtomTable,
) {
  for decl in decls {
    if let Decl::Type(ind) = &**decl {
      register_inductive(ctx, known_globals, structs, ind, config, atoms);
    }
  }
}

/// For every known global name, work out which unqualified short forms
/// `opens` make it reachable under (via the real `ModulePath::open`), and
/// map each such short form to that name's atom. Ambiguous shadowing
/// (two different opened names reducing to the same short form) is
/// last-write-wins — an acceptable simplification for a measurement
/// harness, not a claim of fully faithful shadowing semantics.
fn compute_unqualified_aliases(
  known_globals: &Map<ModulePath, Atom>,
  opens: &[&Open],
) -> Map<Identifier, Atom> {
  let opens_vec: Vec<&Open> = opens.to_vec();
  let mut aliases = Map::new();
  for (path, atom) in known_globals {
    for short in path.open(&opens_vec) {
      aliases.insert(short.last().clone(), *atom);
    }
  }
  aliases
}

#[derive(Debug, Clone, PartialEq)]
pub enum DefFailure {
  LowerType(LowerError),
  LowerBody(LowerError),
  Check(InferError),
  Infer(InferError),
}

#[derive(Debug, Clone)]
pub struct DefOutcome {
  pub name: String,
  pub result: Result<(), DefFailure>,
}

#[derive(Debug, Clone, Default)]
pub struct ModuleReport {
  pub defs: Vec<DefOutcome>,
  /// Non-`Def` declarations encountered (`type`/`instance`/`use`/...),
  /// recorded by kind — not attempted, not failures.
  pub skipped: Vec<&'static str>,
  pub parse_error: Option<String>,
}

impl ModuleReport {
  pub fn passed(&self) -> usize {
    self.defs.iter().filter(|d| d.result.is_ok()).count()
  }
  pub fn failed(&self) -> usize {
    self.defs.iter().filter(|d| d.result.is_err()).count()
  }
}

fn decl_kind(decl: &Decl) -> &'static str {
  match decl {
    Decl::Use(_) => "use",
    Decl::Open(_) => "open",
    Decl::ScopedOpen { .. } => "scoped_open",
    Decl::Def(_) => "def",
    Decl::DefMacro(_) => "defmacro",
    Decl::Type(_) => "type",
    Decl::Ins(_) => "instance",
    Decl::Infix(_) => "infix",
    Decl::MacroCall { .. } => "macro_call",
    Decl::DeclGen(_) => "declgen",
    Decl::Generated(_) => "generated",
  }
}

/// Check every top-level `def` in `source`, in declaration order.
/// `source` is elaborated (`elaborate_decls`) and macro-expanded
/// (`expand_macros`) against `env.loaded` FIRST, exactly as the real
/// checker would — this harness's own logic only starts at lowering.
/// `ctx` starts from `env`'s baseline (every name `default_modules()`
/// knows about), pre-registers every explicitly-typed def's declared
/// type up front (so sibling defs can reference each other regardless of
/// file order — e.g. a def calling another one declared later in the
/// same file), and only then checks each def's body in turn.
pub fn check_module_source(env: &ModuleCheckEnv, source: &str) -> ModuleReport {
  let parsed = match parse_file(source) {
    Ok(p) => p,
    Err(e) => {
      return ModuleReport {
        parse_error: Some(format!("{e}")),
        ..Default::default()
      };
    }
  };

  // `env.loaded` only carries `default_modules()`'s fixed embedded set
  // (prelude/id/io/number/math/string/init/process). A target file's own
  // `use` declarations can reference other on-disk modules (e.g.
  // `std.test`, `std.show`) — `elaborate_decls`'s scope-building panics
  // ("uses unloaded module") if such a module isn't already present in
  // `loaded`, since it assumes (as the real compiler's own loader
  // guarantees) that all `use`d modules are loaded ahead of time. Load any
  // missing ones now, via the same real recursive loader
  // (`load_module_files`) the CLI itself uses — this also fully
  // type-checks each dependency with the OLD checker as a side effect,
  // which is required for it to be usable as `loaded` context, not just
  // convenient.
  let use_paths: Vec<ModulePath> = parsed
    .decls
    .iter()
    .filter_map(|d| match &**d {
      Decl::Use(u) => Some(u.module_path.clone()),
      _ => None,
    })
    .collect();

  let known_module_paths: crate::Set<ModulePath> = env
    .loaded
    .modules()
    .iter()
    .map(|m| m.path().clone())
    .collect();

  let mut loaded_owned;
  let loaded: &LoadedModules = if use_paths.is_empty() {
    &env.loaded
  } else {
    loaded_owned = env.loaded.clone();
    loaded_owned.set_search_paths(repo_search_paths());
    for path in use_paths {
      if loaded_owned.get_module(&path).is_none() {
        match load_module_files(&path, loaded_owned.clone()) {
          Ok(updated) => loaded_owned = updated,
          Err(e) => {
            return ModuleReport {
              parse_error: Some(format!("failed to load `use {path}`: {e}")),
              ..Default::default()
            };
          }
        }
      }
    }
    &loaded_owned
  };

  let elaborated = elaborate_decls(parsed.decls, loaded);
  let synthetic_path = ModulePath::top("__check_module_source_target__");
  let expanded = match expand_macros(elaborated, loaded, &synthetic_path) {
    Ok(d) => d,
    Err(e) => {
      return ModuleReport {
        parse_error: Some(format!("macro expansion error: {e}")),
        ..Default::default()
      };
    }
  };

  let mut infix = env.infix.clone();
  for decl in &expanded {
    if let Decl::Infix(i) = &**decl {
      infix.insert(i.operator().clone(), i.name().clone());
    }
  }

  // Opens active for this file: prelude's own (`open Bool`, `open Unit`,
  // ...) — always ambiently chained in by the real `GlobalScope`, since
  // this is exactly how e.g. bare `true`/`false` are meant to work
  // everywhere — plus the file's own `Decl::Open`s.
  let mut opens: Vec<&Open> = Vec::new();
  if let Some(prelude_module) = loaded.get_module(&prelude_path()) {
    opens.extend(prelude_module.get_opens().iter().map(|ctx| ctx.value()));
  }
  let file_opens: Vec<&Open> = expanded
    .iter()
    .filter_map(|decl| match &**decl {
      Decl::Open(o) => Some(o),
      _ => None,
    })
    .collect();
  opens.extend(file_opens);

  // Also pull in infix operators declared by any module loaded on-demand
  // above for this file's own `use`s (e.g. a `use`d module could define an
  // operator this file's body actually calls).
  for module in loaded.modules() {
    if known_module_paths.contains(module.path()) {
      continue;
    }
    for infix_ctx in module.infix() {
      infix.insert(infix_ctx.operator().clone(), infix_ctx.name().clone());
    }
  }

  let config_no_aliases = LowerConfig {
    infix: infix.clone(),
    ..Default::default()
  };

  let mut known_globals = env.known_globals.clone();
  let mut ctx: TyCtx = env.ctx.clone();
  let mut structs: StructFields = env.structs.clone();
  // Continues `env`'s own table (cloned, not shared — this call's own
  // registrations, below, must not leak into `env` or a sibling call)
  // so a name `env` already interned (e.g. "Bool") and the same name
  // referenced again while checking THIS file resolve to the identical
  // `Atom` — see `ModuleCheckEnv::atoms`'s doc comment.
  let mut atoms = env.atoms.clone();

  // Register every def/inductive from modules loaded on-demand above (this
  // file's own `use`s, and their transitive deps) — mirrors
  // `ModuleCheckEnv::new()`'s own registration loop over
  // `default_modules()`, just applied to whatever got loaded for this one
  // file. Without this, a `use`d module's own class methods (e.g.
  // `Foldable.foldr`) or plain defs would be present in `loaded` (so scope
  // resolution/macro expansion work) but invisible to the type checker
  // itself, surfacing as spurious `UnboundVariable`s.
  for module in loaded.modules() {
    if known_module_paths.contains(module.path()) {
      continue;
    }
    for def_ctx in module.defs() {
      let def: &Def = def_ctx;
      let atom = atoms.intern(def.name.clone());
      known_globals.insert(def.name.clone(), atom);
      if let Ok(ty_c) = lower_term(
        &mut LowerContext::with_config(config_no_aliases.clone(), &mut atoms),
        &def.typ,
      ) {
        ctx.insert(atom, ty_c);
      }
    }
    for ind in module.inductives() {
      register_inductive(
        &mut ctx,
        &mut known_globals,
        &mut structs,
        ind,
        &config_no_aliases,
        &mut atoms,
      );
    }
  }

  register_type_decls(
    &mut ctx,
    &mut known_globals,
    &mut structs,
    &expanded,
    &config_no_aliases,
    &mut atoms,
  );

  // Also register the file's own `def`s into `known_globals` up front (a
  // real `open` could in principle alias a sibling def) — name
  // *visibility* for aliasing isn't order-sensitive within one file,
  // matching this harness's existing whole-file-scoped treatment of
  // `infix`/`type` decls, and (see below) `ctx`'s types now aren't
  // either.
  for decl in &expanded {
    if let Decl::Def(def) = &**decl {
      let atom = atoms.intern(def.name.clone());
      known_globals.insert(def.name.clone(), atom);
    }
  }

  let aliases = compute_unqualified_aliases(&known_globals, &opens);
  let config = LowerConfig {
    infix,
    unqualified_aliases: aliases,
    ..Default::default()
  };

  // Pre-register every explicitly-typed def's declared (already
  // elaborated) type into `ctx` BEFORE checking any bodies — sibling
  // defs reference each other regardless of file order (e.g.
  // `list_show`, defined first, calls `show_body`, defined after it;
  // real module name resolution isn't sensitive to declaration order
  // within one file, matching how `known_globals`/`infix`/`type` decls
  // are already treated whole-file-scoped above). `check_one_def` below
  // re-registers each def's own type again as it processes it — harmless
  // (same value) — and still does the real per-def work (peeling
  // Foralls, lowering+checking the body). Defs with NO declared type
  // (using `infer` instead) can't be pre-registered this way — their
  // type isn't known until their own body is inferred — so forward
  // references to an unannotated sibling remain unsupported, a much
  // narrower and rarer case than ordinary explicitly-typed forward
  // references.
  for decl in &expanded {
    if let Decl::Def(def) = &**decl
      && def.typ.is_known()
    {
      let self_atom = atoms.intern(def.name.clone());
      if let Ok(typ_c) = lower_term(
        &mut LowerContext::with_config(config.clone(), &mut atoms),
        &def.typ,
      ) {
        ctx.insert(self_atom, typ_c);
      }
    }
  }

  let mut mctx = MetaContext::new_with_atoms(atoms);
  let mut report = ModuleReport::default();

  for decl in &expanded {
    match &**decl {
      Decl::Def(def) => {
        let name = def.name.to_string();
        let result = check_one_def(&mut mctx, &mut ctx, &structs, def, &config);
        report.defs.push(DefOutcome { name, result });
      }
      Decl::ScopedOpen {
        module_path,
        filter,
        decl: inner,
        ..
      } => {
        // Mirrors `type_check_module_decls_new`'s `Decl::ScopedOpen`
        // handling: widen `unqualified_aliases` with the scoped open's
        // names, but only for checking this one wrapped `def`.
        let scoped_open_val = Open {
          source_location: SourceRange::default(),
          module_path: module_path.clone(),
          filter: filter.clone(),
          attributes: vec![],
        };
        let mut scoped_opens: Vec<&Open> = opens.clone();
        scoped_opens.push(&scoped_open_val);
        let scoped_aliases = compute_unqualified_aliases(&known_globals, &scoped_opens);
        let mut scoped_config = config.clone();
        scoped_config.unqualified_aliases.extend(scoped_aliases);
        match &**inner {
          Decl::Def(def) => {
            let name = def.name.to_string();
            let result = check_one_def(&mut mctx, &mut ctx, &structs, def, &scoped_config);
            report.defs.push(DefOutcome { name, result });
          }
          other => report.skipped.push(decl_kind(other)),
        }
      }
      other => report.skipped.push(decl_kind(other)),
    }
  }
  report
}

/// Strip `typ_c`'s leading `Forall`s, minting a fresh rigid atom for each
/// and returning `(name, atom, var's own type)` triples (skipping
/// anonymous binders — nothing in a body could reference those by name
/// anyway) alongside the fully-peeled residual type. Opening happens here
/// — not inside `check` — specifically so the atoms are visible to the
/// CALLER and can be threaded into a separate `lower_term` call for the
/// `def`'s body (see `LowerContext::free_overrides`'s doc comment for why
/// that's necessary: the body's own inline param-type annotations, e.g.
/// `(a : A)`, must resolve to these SAME atoms, not the unrelated
/// shared-by-name global atom `A` would otherwise get).
fn peel_foralls(typ_c: CoreTerm) -> (Vec<(Identifier, Atom, CoreTerm)>, CoreTerm) {
  let mut vars = Vec::new();
  let mut current = typ_c;
  while let CoreTerm::Forall { dbg, typ, body } = current {
    let atom = Atom::fresh();
    if let DebugName::Named(name) = dbg {
      vars.push((name, atom, *typ));
    }
    current = open_with(&body, &CoreTerm::Free(atom));
  }
  (vars, current)
}

/// Whether `term` (a def's own SOURCE-level body, before lowering)
/// references anything under `class_name`'s namespace — a qualified
/// reference (`Functor.map`) directly, or an unqualified one (`map`, only
/// resolvable via `structs`' already-registered field/method list for
/// `class_name`, since nothing else at this point knows what `open
/// Functor` made reachable unqualified). Used to decide whether a
/// `[ClassName Var]` constraint is only a phantom/documentation
/// annotation (see `elaborate_constrained_type`'s doc comment) — an
/// under-approximation is the SAFE direction here (worst case: an
/// unnecessary dict `Pi` gets inserted for a constraint that turns out
/// unused, exactly today's behavior before this check existed), so this
/// deliberately doesn't try to resolve every alias-resolution edge case.
fn term_references_class(
  term: &Term,
  class_name: &ModulePath,
  structs: &StructFields,
  atoms: &mut AtomTable,
  infix: &Map<Operator, ModulePath>,
) -> bool {
  let mut is_match = |path: &ModulePath| {
    path == class_name
      || path.is_prefix(class_name)
      || structs
        .structs
        .get(&atoms.intern(class_name.clone()))
        .is_some_and(|info| info.fields.iter().any(|(name, _)| path.last() == name))
  };
  match term {
    Term::Var {
      name: NameRef::P(path),
    } => is_match(path),
    Term::Var {
      name: NameRef::Id(id),
    } => structs
      .structs
      .get(&atoms.intern(class_name.clone()))
      .is_some_and(|info| info.fields.iter().any(|(name, _)| name == id)),
    // An infix operator (`a == b`, parsed as `App(App(Var{Op(==)},a),b)`)
    // is how a constrained instance's own generic method most often
    // invokes another class method recursively (`Option`'s `beq`'s `a ==
    // b`, never spelling out `BEq.beq` the way `List`'s `beq` happens to
    // ALSO do alongside its own operator use) — resolve it through the
    // same `infix (op) := path` table `lower_term` itself consults, or
    // this constraint is silently never detected as "actually used",
    // `elaborate_constrained_type` never adds its dictionary parameter,
    // and the method's own recursive class-method call is left with no
    // bound dictionary to resolve from at all.
    Term::Var {
      name: NameRef::Op(op),
    } => infix.get(op).is_some_and(|path| is_match(path)),
    Term::Var { .. } => false,
    Term::Forall { typ, body, .. } => {
      term_references_class(typ, class_name, structs, atoms, infix)
        || term_references_class(body, class_name, structs, atoms, infix)
    }
    Term::Pi { arg, ret, .. } => {
      term_references_class(arg, class_name, structs, atoms, infix)
        || term_references_class(ret, class_name, structs, atoms, infix)
    }
    Term::Lam { param, body } => {
      term_references_class(param.typ(), class_name, structs, atoms, infix)
        || term_references_class(body, class_name, structs, atoms, infix)
    }
    Term::App { fun, arg } => {
      term_references_class(fun, class_name, structs, atoms, infix)
        || term_references_class(arg, class_name, structs, atoms, infix)
    }
    Term::Ann { term, typ } => {
      term_references_class(term, class_name, structs, atoms, infix)
        || term_references_class(typ, class_name, structs, atoms, infix)
    }
    Term::Ctx { term, .. } => term_references_class(term, class_name, structs, atoms, infix),
    Term::Quote { term } => term_references_class(term, class_name, structs, atoms, infix),
    Term::Con(c) => c
      .args()
      .iter()
      .flatten()
      .any(|a| term_references_class(a, class_name, structs, atoms, infix)),
    Term::Ntv { native } => native
      .args
      .iter()
      .flatten()
      .any(|a| term_references_class(a, class_name, structs, atoms, infix)),
    Term::Lit { value } => literal_references_class(value, class_name, structs, atoms, infix),
    Term::Sort { .. } | Term::Hole => false,
  }
}

fn literal_references_class(
  lit: &Literal,
  class_name: &ModulePath,
  structs: &StructFields,
  atoms: &mut AtomTable,
  infix: &Map<Operator, ModulePath>,
) -> bool {
  match lit {
    Literal::Str { .. } | Literal::Char { .. } | Literal::Num { .. } | Literal::Float { .. } => {
      false
    }
    Literal::Match { value, cases } => {
      term_references_class(value, class_name, structs, atoms, infix)
        || cases
          .iter()
          .any(|c| term_references_class(&c.value, class_name, structs, atoms, infix))
    }
    Literal::If { value, then, els } => {
      term_references_class(value, class_name, structs, atoms, infix)
        || term_references_class(then, class_name, structs, atoms, infix)
        || term_references_class(els, class_name, structs, atoms, infix)
    }
    Literal::StructLit { fields, type_name } => {
      fields
        .values()
        .any(|v| term_references_class(v, class_name, structs, atoms, infix))
        || type_name
          .as_ref()
          .is_some_and(|t| term_references_class(t, class_name, structs, atoms, infix))
    }
    Literal::StructUpdate { fields, .. } => fields
      .values()
      .any(|v| term_references_class(v, class_name, structs, atoms, infix)),
    Literal::Term(t) => term_references_class(t, class_name, structs, atoms, infix),
    Literal::Foreign(_) => false,
  }
}

/// D3: elaborate a constrained def's (`[BOrd A]`) already-Forall-wrapped
/// type to additionally carry a real dictionary `Pi` parameter for each
/// single-var constraint whose class D1 registered into `structs`, AND
/// whose class is actually referenced somewhere in `term` (the def's own
/// SOURCE body — see `term_references_class`) — the user's own framing
/// for this feature ("real implicit function parameters when
/// *necessary*") is deliberately not "every constraint always gets a real
/// dictionary": a constraint that's structurally present but never
/// actually used (e.g. `init/prelude.mo`'s `Lens [Functor F] {F: Type ->
/// Type} ... := (A -> F B) -> S -> F T` — `Functor` here is a phantom/
/// documentation-only kind annotation on `F`, exactly like Haskell's
/// `type Lens s t a b = forall f. Functor f => ...`, never actually
/// calling any `Functor` method) would otherwise gain a spurious runtime
/// parameter that changes its arity for no semantic reason — and, for a
/// TYPE-level def like `Lens`, breaks any code that expands/substitutes
/// its definition directly (the OLD checker's `Scope` does exactly this
/// for a type alias) without knowing dictionaries exist at all.
///
/// For a constraint that IS used: `Forall A . Pi(x:A) -> ...` becomes
/// `Forall A . Pi(dict: BOrd A) . Pi(x:A) -> ...`, the dict inserted
/// immediately after the constrained var's own `Forall` (in
/// `type_constraints`' own declaration order, first constraint ending up
/// the outermost/first dict `Pi` — matters for `#`-explicit application,
/// D6, which will fill these positionally). Constraints this phase can't
/// place (multi-var, or a class D1 never registered — multi-param class
/// support is explicitly out of scope for this pass) are silently left
/// unelaborated too, same "approximate, don't guess" fallback style used
/// throughout this checker — not an error.
///
/// MUST be applied to every constrained def's type before it's inserted
/// anywhere a caller can see it (`ctx[self_atom]`, both in this
/// function's own pre-registration passes and `check_one_def_new`'s own
/// `ctx` insert) — a caller's own `instantiate_foralls` (`core_check.rs`)
/// already knows how to auto-skip a leading dict `Pi` once it's there,
/// but only if it's actually part of the registered type; skipping this
/// step for even one of the two would desync what callers see from what
/// the def's own body was checked against.
fn elaborate_constrained_type(
  typ_c: CoreTerm,
  type_constraints: &[TypeConstraint],
  body: &Term,
  structs: &StructFields,
  atoms: &mut AtomTable,
  infix: &Map<Operator, ModulePath>,
) -> (CoreTerm, bool) {
  if type_constraints.is_empty() {
    return (typ_c, false);
  }
  let (peeled_vars, residual) = peel_foralls(typ_c.clone());
  let mut with_dicts = residual;
  let mut wrapped_any = false;
  for constraint in type_constraints.iter().rev() {
    if constraint.vars().len() != 1 {
      continue;
    }
    if !term_references_class(body, constraint.class(), structs, atoms, infix) {
      continue;
    }
    let Some((_, var_atom, _)) = peeled_vars
      .iter()
      .find(|(n, _, _)| *n == constraint.vars()[0])
    else {
      continue;
    };
    let class_atom = atoms.intern(constraint.class().clone());
    if !is_class_atom(structs, class_atom) {
      continue;
    }
    // `dict_atom` is only minted to make `close` below a well-formed
    // (and, since it's fresh, a no-op) binder-closing step — nothing in
    // `with_dicts` ever references it; the dictionary VALUE only becomes
    // reachable from inside the body once `check_one_def_new`'s own
    // dict-peeling (mirroring this one on the OPENED type) wraps the body
    // in a matching `Lam`.
    let dict_atom = Atom::fresh();
    let dict_typ = CoreTerm::App {
      fun: Box::new(CoreTerm::Free(class_atom)),
      arg: Box::new(CoreTerm::Free(*var_atom)),
    };
    with_dicts = CoreTerm::Pi {
      dbg: DebugName::Named(Identifier::new(format!("${}", constraint.class()))),
      arg: Box::new(dict_typ),
      ret: Box::new(close(&with_dicts, dict_atom)),
      mult: Multiplicity::Many,
    };
    wrapped_any = true;
  }
  if !wrapped_any {
    return (typ_c, false);
  }
  let mut result = with_dicts;
  for (name, atom, var_typ) in peeled_vars.iter().rev() {
    result = CoreTerm::Forall {
      dbg: DebugName::Named(name.clone()),
      typ: Box::new(var_typ.clone()),
      body: Box::new(close(&result, *atom)),
    };
  }
  (result, true)
}

fn check_one_def(
  mctx: &mut MetaContext,
  ctx: &mut TyCtx,
  structs: &StructFields,
  def: &Def,
  config: &LowerConfig,
) -> Result<(), DefFailure> {
  let self_atom = mctx.intern(def.name.clone());

  if def.typ.is_known() {
    // `def.typ` is already fully elaborated (implicit Foralls included)
    // by `elaborate_decls`, called once for the whole file in
    // `check_module_source` — no per-def elaboration needed here.
    let typ_c = lower_term(
      &mut LowerContext::with_config(config.clone(), mctx.atoms_mut()),
      &def.typ,
    )
    .map_err(DefFailure::LowerType)?;
    // Register the full (still-polymorphic) type BEFORE lowering/checking
    // the body, so a recursive self-reference resolves to it — each
    // recursive call gets its own fresh instantiation via
    // `infer(App)`/`instantiate_foralls`, same as any other use of a
    // polymorphic function; this is correct, not a shortcut.
    ctx.insert(self_atom, typ_c.clone());

    let (peeled_vars, residual_typ) = peel_foralls(typ_c);
    let mut overrides = Map::new();
    for (name, atom, var_typ) in &peeled_vars {
      overrides.insert(name.clone(), *atom);
      ctx.insert(*atom, var_typ.clone());
    }
    let body_config = LowerConfig {
      infix: config.infix.clone(),
      free_overrides: overrides,
      unqualified_aliases: config.unqualified_aliases.clone(),
    };

    let body_c = lower_term(
      &mut LowerContext::with_config(body_config, mctx.atoms_mut()),
      &def.term,
    )
    .map_err(DefFailure::LowerBody)?;
    check(mctx, ctx, structs, &body_c, &residual_typ).map_err(DefFailure::Check)
  } else {
    let body_c = lower_term(
      &mut LowerContext::with_config(config.clone(), mctx.atoms_mut()),
      &def.term,
    )
    .map_err(DefFailure::LowerBody)?;
    let ty = infer(mctx, ctx, structs, &body_c).map_err(DefFailure::Infer)?;
    ctx.insert(self_atom, ty);
    Ok(())
  }
}

fn lower_error_to_type_error(e: LowerError) -> TypeError {
  TypeError::Generic(format!("{e:?}"), SourceRange::default())
}

/// Best-effort `Atom` -> readable name for error messages. Deliberately
/// NOT `raise_core` (which panics on a `Free` atom missing from its
/// `atom_paths` table) — an atom reaching here is, by construction, one
/// `infer`/`check` just failed on, so it may never have been registered
/// anywhere a full raiser would expect. Falls back to a placeholder
/// rather than ever panicking on an error-reporting path.
fn render_atom(atom: Atom, atoms: &AtomTable) -> String {
  match atoms.path_of(atom) {
    Some(path) => path.to_string(),
    None => "<unknown>".to_string(),
  }
}

/// Best-effort `CoreTerm` -> readable string for error messages, mirroring
/// `raise_core`'s traversal but never panicking: an unresolved `Meta`
/// prints as `_` (same convention as an unannotated hole) instead of
/// requiring the term to have already been zonked, and a `Free` atom
/// missing from `atoms` falls back to `render_atom`'s placeholder instead
/// of panicking. `bound_names` mirrors `raise_core::Raiser`'s own binder
/// stack (innermost last, `Bound(0)` = last-pushed).
fn render_core_term(term: &CoreTerm, atoms: &AtomTable, bound_names: &mut Vec<String>) -> String {
  match term {
    CoreTerm::Bound(i) => bound_names
      .len()
      .checked_sub(1 + *i as usize)
      .and_then(|idx| bound_names.get(idx))
      .cloned()
      .unwrap_or_else(|| "_".to_string()),
    CoreTerm::Free(atom) => render_atom(*atom, atoms),
    CoreTerm::Meta(_) => "_".to_string(),
    CoreTerm::Forall { dbg, typ, body } => {
      let name = dbg.as_str().to_string();
      let typ_s = render_core_term(typ, atoms, bound_names);
      bound_names.push(name.clone());
      let body_s = render_core_term(body, atoms, bound_names);
      bound_names.pop();
      format!("forall ({name} : {typ_s}), {body_s}")
    }
    CoreTerm::Pi { dbg, arg, ret, .. } => {
      let name = dbg.as_str().to_string();
      let arg_s = render_core_term(arg, atoms, bound_names);
      bound_names.push(name);
      let ret_s = render_core_term(ret, atoms, bound_names);
      bound_names.pop();
      format!("{arg_s} -> {ret_s}")
    }
    CoreTerm::Lam {
      dbg,
      param_typ,
      body,
    } => {
      let name = dbg.as_str().to_string();
      let typ_s = render_core_term(param_typ, atoms, bound_names);
      bound_names.push(name.clone());
      let body_s = render_core_term(body, atoms, bound_names);
      bound_names.pop();
      format!("fn ({name} : {typ_s}) => {body_s}")
    }
    CoreTerm::App { fun, arg } => {
      format!(
        "({} {})",
        render_core_term(fun, atoms, bound_names),
        render_core_term(arg, atoms, bound_names)
      )
    }
    CoreTerm::Sort { level } => {
      if *level == 0 {
        "Type".to_string()
      } else {
        format!("Type{level}")
      }
    }
    CoreTerm::Hole => "_".to_string(),
    CoreTerm::Lit(lit) => render_core_lit(lit, atoms, bound_names),
    CoreTerm::Con(c) => c.typ_name.to_string(),
    CoreTerm::Ntv(n) => n.native_name.to_string(),
    // Transparent for rendering: a `Ctx` wrapper is metadata for error
    // attribution (see `infer_error_to_type_error`, which reads it
    // separately via `strip_ctx_loc`), not part of what the term "is".
    CoreTerm::Ctx { term, .. } => render_core_term(term, atoms, bound_names),
  }
}

fn render_core_lit(lit: &CoreLit, atoms: &AtomTable, bound_names: &mut Vec<String>) -> String {
  match lit {
    CoreLit::Str { value } => format!("{value:?}"),
    CoreLit::Char { value } => format!("{value:?}"),
    CoreLit::Num { value, suffix } => format!("{value}{suffix:?}"),
    CoreLit::Float { value, suffix } => format!("{}{suffix:?}", value.0),
    CoreLit::Match { scrutinee, .. } => {
      format!(
        "match {} {{ .. }}",
        render_core_term(scrutinee, atoms, bound_names)
      )
    }
    CoreLit::If { cond, .. } => {
      format!(
        "if {} then .. else ..",
        render_core_term(cond, atoms, bound_names)
      )
    }
    CoreLit::StructLit { .. } => "{ .. }".to_string(),
    CoreLit::StructUpdate { base, .. } => {
      format!(
        "{} with {{ .. }}",
        render_core_term(base, atoms, bound_names)
      )
    }
  }
}

fn render_unify_error(e: &UnifyError, atoms: &AtomTable) -> String {
  match e {
    // `left`/`right` are just "the two sides `unify` was called with", not
    // a defined expected/actual pair (see `core_unify.rs`'s single
    // `mismatch(left, right)` call site) — phrase neutrally rather than
    // asserting a direction the type doesn't actually guarantee.
    UnifyError::Mismatch { left, right } => format!(
      "type mismatch: `{}` vs. `{}`",
      render_core_term(left, atoms, &mut Vec::new()),
      render_core_term(right, atoms, &mut Vec::new()),
    ),
    UnifyError::OccursCheck { term, .. } => format!(
      "infinite type: `{}` occurs in itself",
      render_core_term(term, atoms, &mut Vec::new()),
    ),
    UnifyError::UnsupportedPattern { left, right } => format!(
      "unsupported higher-order unification between `{}` and `{}`",
      render_core_term(left, atoms, &mut Vec::new()),
      render_core_term(right, atoms, &mut Vec::new()),
    ),
  }
}

/// A `CoreTerm`'s own best-known source location, if it (or its outermost
/// `Ctx` wrapper) has one — see `CoreTerm::strip_ctx_loc`.
fn source_range_of(t: &CoreTerm) -> Option<SourceRange> {
  t.strip_ctx_loc().1.cloned()
}

/// The most precise location available for an `InferError` — the
/// sub-expression that actually caused it, now that `CoreTerm::Ctx`
/// carries real spans through lowering/checking, not just the enclosing
/// def's whole span. `left`/`right` in a `Mismatch` are "the two sides
/// `unify` was called with" in `(actual, expected)` order (see
/// `render_unify_error`'s identical note) — the actual/inferred side is
/// more likely to trace back to a real written expression, so it's tried
/// first; falls back to `None` (the caller then falls back to the
/// enclosing decl's own location, via `TypeError::Context`) for error
/// kinds with no associated term at all (`UnboundVariable`, ...).
fn infer_error_location(e: &InferError) -> Option<SourceRange> {
  match e {
    InferError::Unify(UnifyError::Mismatch { left, right }) => {
      source_range_of(left).or_else(|| source_range_of(right))
    }
    InferError::Unify(UnifyError::OccursCheck { term, .. }) => source_range_of(term),
    InferError::Unify(UnifyError::UnsupportedPattern { left, right }) => {
      source_range_of(left).or_else(|| source_range_of(right))
    }
    InferError::ExpectedFunctionType(t) | InferError::CannotInfer(t) => source_range_of(t),
    InferError::UnboundVariable(_)
    | InferError::UnknownMeta(_)
    | InferError::UnexpectedBound(_)
    | InferError::CannotInferHole => None,
  }
}

fn infer_error_to_type_error(e: InferError, atoms: &AtomTable) -> TypeError {
  let location = infer_error_location(&e);
  let message = match &e {
    InferError::Unify(u) => render_unify_error(u, atoms),
    InferError::UnboundVariable(atom) => {
      format!("unbound variable `{}`", render_atom(*atom, atoms))
    }
    InferError::UnknownMeta(_) => {
      "internal error: reference to an unknown metavariable".to_string()
    }
    InferError::UnexpectedBound(_) => {
      "internal error: unexpected bound variable in inference".to_string()
    }
    InferError::CannotInferHole => {
      "cannot infer the type of a hole; add a type annotation".to_string()
    }
    InferError::ExpectedFunctionType(t) => format!(
      "expected a function type, found `{}`",
      render_core_term(t, atoms, &mut Vec::new())
    ),
    InferError::CannotInfer(t) => format!(
      "cannot infer the type of `{}`; add a type annotation",
      render_core_term(t, atoms, &mut Vec::new())
    ),
  };
  TypeError::Generic(message, location.unwrap_or_default())
}

/// Insert a checked def into `CoreProgram.defs` under `capture_path`
/// (the CALLER's own choice -- module-qualified for an ordinary
/// top-level def, instance-and-method-qualified for an instance
/// method), AND, when it differs, ALSO under `def_name` bare.
///
/// Why both: `capture_path` alone isn't enough once two INDEPENDENT
/// modules declare the same bare name (`list_contains` in both
/// `lang.module` and `string`, confirmed for real in this corpus) --
/// each module's own SELF/sibling references resolve via the qualified
/// atom (`type_check_module_decls_new_inner`'s own `global_atom_paths`
/// override forces this), so the qualified entry must exist. But
/// `def_name` bare alone isn't enough EITHER: an ORDINARY,
/// non-colliding cross-module reference (`fib`, in one module, calling
/// `I64.add`, a native declared in a totally different, unrelated
/// module) resolves via the BARE atom (nothing forces it to qualify a
/// name it never itself declares), and an EXPLICIT, programmer-written
/// qualified reference (`lang.parser.core.op_char_member`, spelled out
/// in source) resolves via the QUALIFIED atom regardless of whether
/// `op_char_member` happens to collide with anything (confirmed real:
/// `ground_truth_from_loaded` dual-registers every def under both
/// forms unconditionally, so a fully-qualified reference is valid
/// syntax even for names nobody else declares). Inserting under BOTH
/// keys, unconditionally, means whichever atom a given reference
/// (bare or qualified, colliding or not, self or cross-module) happens
/// to resolve to, some entry is there to find -- the only case left
/// genuinely ambiguous is a THIRD file bare-referencing a name that
/// collides between two OTHER modules it doesn't itself declare, where
/// the bare slot ends up whichever colliding module happened to be
/// checked last (unchanged from the pre-existing, accepted behavior).
fn insert_checked_def(
  program: &mut CoreProgram,
  capture_path: &ModulePath,
  def_name: &ModulePath,
  checked: CheckedCoreDef,
) {
  if capture_path != def_name {
    program.defs.insert(def_name.clone(), checked.clone());
  }
  program.defs.insert(capture_path.clone(), checked);
}

/// Same bare-and-qualified double-insert as `insert_checked_def`, for
/// `CoreProgram::match_resolutions` -- needed for the exact same reason:
/// `lower_program`'s per-def loop iterates `program.defs`'s own keys
/// (now both bare and qualified, per `insert_checked_def`) and looks up
/// `match_resolutions` using THAT SAME key for each one, so both need
/// an entry or the bare-keyed duplicate lowers with an empty resolution
/// queue.
fn insert_match_resolutions(
  program: &mut CoreProgram,
  capture_path: &ModulePath,
  def_name: &ModulePath,
  resolutions: Vec<(Vec<Identifier>, Atom)>,
) {
  if capture_path != def_name {
    program
      .match_resolutions
      .insert(def_name.clone(), resolutions.clone());
  }
  program
    .match_resolutions
    .insert(capture_path.clone(), resolutions);
}

/// Like `check_one_def`, but for the real production entry point
/// (`type_check_module_decls_new`) rather than this file's own diagnostic
/// harness: returns a fully checked, RAISED `Def` (its `.term`/`.typ`
/// replaced with the real `Term`s the rest of the pipeline consumes,
/// matching `eval::type::type_check_def`'s own contract exactly) instead
/// of a bare pass/fail outcome.
#[allow(clippy::too_many_arguments)]
fn check_one_def_new(
  mctx: &mut MetaContext,
  ctx: &mut TyCtx,
  structs: &StructFields,
  def: &Def,
  config: &LowerConfig,
  global_atom_paths: &Map<Atom, ModulePath>,
  known_class_methods: &KnownClassMethods,
  known_instances: &KnownInstances,
  // Phase 0 of `plans/implementations/core-term-closure-evaluator.md`:
  // opt-in capture of this def's pre-`raise_core` `CoreTerm`, keyed by
  // `capture_path` (usually `&def.name`, but instance-qualified for a
  // per-instance method — see `check_one_instance_new`). `None` (every
  // pre-existing call site) costs nothing extra.
  mut core_out: Option<&mut CoreProgram>,
  capture_path: &ModulePath,
) -> Result<Def, TypeError> {
  let self_atom = mctx.intern(def.name.clone());
  let mut new_def = def.clone();
  // Starts empty: no dictionary is bound yet at the top of a def's own
  // body — `desugar_struct_literals`'s `Lam` arm extends a local copy of
  // this the moment it opens a dictionary parameter (D3/D5).
  let dict_scope = DictScope::new();

  if def.typ.is_known() {
    let typ_lower_resolved = {
      let mut typ_lower_ctx = LowerContext::with_config(config.clone(), mctx.atoms_mut());
      let typ_c_result = lower_term(&mut typ_lower_ctx, &def.typ);
      (typ_c_result, typ_lower_ctx.resolved_atoms().clone())
    };
    let typ_c = typ_lower_resolved.0.map_err(lower_error_to_type_error)?;
    let typ_lower_resolved = typ_lower_resolved.1;
    let (typ_c, was_elaborated) = elaborate_constrained_type(
      typ_c,
      def.type_constraints(),
      &def.term,
      structs,
      mctx.atoms_mut(),
      &config.infix,
    );
    ctx.insert(self_atom, typ_c.clone());

    // `raise_core` needs to turn a `Free` occurrence of one of THESE
    // atoms back into a reference to the def's own Forall parameter name
    // (e.g. "A"), not a global — extend the reverse lookup with a
    // single-segment `ModulePath` per peeled var (`name.to_path()`, the
    // same "resolved bare name" shape `NameRef::P` already uses elsewhere
    // in this codebase — see `raise_core.rs`'s module doc) so one uniform
    // `Map<Atom, ModulePath>` covers both cases. Also fold in every atom
    // THIS lowering call resolved via the global fallback — `type_c` can
    // reference a name (e.g. an inductive's own bare name used as a type,
    // not just its constructors) that was never explicitly registered in
    // `known_globals`/`global_atom_paths`, since name resolution during
    // lowering never validates a path is "known" ahead of time (see
    // `LowerContext::resolved_atoms`'s doc comment).
    let mut atom_paths = global_atom_paths.clone();
    // `global_atom_paths` is authoritative for any atom it already knows
    // about (its own per-module override -- see `type_check_module_
    // decls_new_inner`'s own doc comment -- specifically needs to WIN
    // here, not get silently re-overwritten back to a bare path by a
    // fresh, ordinary resolution for the exact same, already-known
    // atom); only genuinely NEW atoms `global_atom_paths` has no entry
    // for at all get filled in from this lowering's own resolution.
    atom_paths.extend(
      typ_lower_resolved
        .iter()
        .filter(|(a, _)| !global_atom_paths.contains_key(a))
        .map(|(a, p)| (*a, p.clone())),
    );
    if was_elaborated {
      // D3 may have inserted a dictionary `Pi` this def's SURFACE `.typ`
      // (still the literal, un-elaborated source annotation) doesn't
      // mention — re-raise the elaborated `CoreTerm` back into `.typ` so
      // it stays consistent with `.term` (which DOES get a matching
      // extra `Lam`, below). Anything downstream that reads `.typ` to
      // know how many arguments `.term` actually expects — another def's
      // annotation expanding this one, `eval.rs`'s runtime application —
      // would otherwise silently desync the moment this def has any real
      // constraint, exactly the bug that motivated this: `Lens`'s own
      // `.typ` staying the unelaborated 4-Pi source annotation while its
      // `.term` gained a 5th, leading dict `Lam` broke every OTHER def
      // that expands `Lens`'s type to check against it.
      new_def.typ = raise_core(&typ_c, &atom_paths);
    }

    let (peeled_vars, residual_typ) = peel_foralls(typ_c);
    let mut overrides = Map::new();
    for (name, atom, var_typ) in &peeled_vars {
      overrides.insert(name.clone(), *atom);
      ctx.insert(*atom, var_typ.clone());
      atom_paths.insert(*atom, name.clone().to_path());
    }
    let body_config = LowerConfig {
      infix: config.infix.clone(),
      free_overrides: overrides,
      unqualified_aliases: config.unqualified_aliases.clone(),
    };

    let mut body_lower_ctx = LowerContext::with_config(body_config, mctx.atoms_mut());
    let body_c = lower_term(&mut body_lower_ctx, &def.term).map_err(lower_error_to_type_error)?;
    // `global_atom_paths` wins over a fresh resolution for an
    // already-known atom here too -- see the identical filter above,
    // on `typ_lower_resolved`, for why.
    atom_paths.extend(
      body_lower_ctx
        .resolved_atoms()
        .iter()
        .filter(|(a, _)| !global_atom_paths.contains_key(a))
        .map(|(a, p)| (*a, p.clone())),
    );
    // D3: `residual_typ` may start with one or more dictionary `Pi`s
    // (`elaborate_constrained_type`, above) that `def.term` — lowered
    // straight from source, which never spells out a dictionary
    // parameter the user didn't write — has no matching `Lam` for. Probe
    // (without disturbing `residual_typ` itself: `check`'s own `Lam`
    // arm needs to see the ORIGINAL dict `Pi`s to open in lockstep with
    // the `Lam`s wrapped in below) how many lead the chain, then prepend
    // that many synthetic `Lam`s to `body_c` — mirrors how a source-level
    // `(x y z : A)` parameter list already becomes a `Lam` chain during
    // lowering, just synthesized here instead of parsed.
    let mut dict_arg_types: Vec<CoreTerm> = Vec::new();
    let mut probe = residual_typ.clone();
    while let CoreTerm::Pi { arg, ret, .. } = probe {
      let Some(head) = head_atom_of(mctx, &arg) else {
        break;
      };
      if !is_class_atom(structs, head) {
        break;
      }
      dict_arg_types.push((*arg).clone());
      probe = open_with(&ret, &CoreTerm::Free(Atom::fresh()));
    }
    let mut body_c = body_c;
    for arg_typ in dict_arg_types.iter().rev() {
      let dict_atom = Atom::fresh();
      body_c = CoreTerm::Lam {
        // `DebugName::Anonymous` specifically means "raise to an
        // index-based `Par::I`" (`raise_core`'s own rule, there to
        // preserve a native def's positional-argument-absorption shape)
        // — NOT "give this parameter a placeholder name." An ordinary,
        // non-native `Lam` like this synthesized dictionary parameter
        // needs a real `DebugName::Named` so it raises as an ordinary
        // named `Par::P` and substitutes correctly at application time;
        // using `Anonymous` here made the evaluator silently fail to
        // bind it (`scope: _anon#N not found`) since it was raised as if
        // it were a native's own absorbed argument instead.
        dbg: DebugName::Named(Identifier::gensym("$dict")),
        param_typ: Box::new(arg_typ.clone()),
        body: Box::new(close(&body_c, dict_atom)),
      };
    }
    check(mctx, ctx, structs, &body_c, &residual_typ)
      .map_err(|e| infer_error_to_type_error(e, mctx.atoms()))?;
    // `check` never mutates the term it's checking (see `raise_core`'s
    // module doc), but the evaluator refuses to run a bare struct literal
    // (see `desugar_struct_literals`'s doc comment) — so unlike other
    // `Term`s here, `body_c` DOES need a rewrite pass before raising, not
    // just the raw checked term. `def.typ` is already the real,
    // already-elaborated `Term` — no need to raise a type we already have.
    let body_c = desugar_struct_literals(
      mctx,
      ctx,
      structs,
      &mut atom_paths,
      known_class_methods,
      known_instances,
      &dict_scope,
      &body_c,
      Some(&residual_typ),
    );
    // Drain this def's own Match/if resolutions right now (AFTER
    // desugar_struct_literals, not right after `check` — that pass is
    // what injects dictionary-projection Match nodes and produces the
    // FINAL body_c a lowering pass sees, so its traversal order is what
    // needs to be captured, not check's own pre-desugar one — see
    // `desugar_struct_literals`'s doc comment), before the NEXT def's
    // check appends more onto the same shared MetaContext — see
    // `CoreProgram::match_resolutions`'s doc comment for why this must
    // stay scoped per-def, not merged at the end of the whole module's
    // check.
    if let Some(program) = core_out.as_deref_mut() {
      insert_match_resolutions(
        program,
        capture_path,
        &def.name,
        mctx.take_match_resolutions(),
      );
    }
    if let Some(program) = core_out {
      insert_checked_def(
        program,
        capture_path,
        &def.name,
        CheckedCoreDef {
          term: body_c.clone(),
          typ: residual_typ.clone(),
          atom_paths: atom_paths.clone(),
        },
      );
    }
    new_def.term = raise_core(&body_c, &atom_paths);
    Ok(new_def)
  } else {
    let mut body_lower_ctx = LowerContext::with_config(config.clone(), mctx.atoms_mut());
    let body_c = lower_term(&mut body_lower_ctx, &def.term).map_err(lower_error_to_type_error)?;
    let mut atom_paths = global_atom_paths.clone();
    // `global_atom_paths` wins over a fresh resolution for an
    // already-known atom here too -- see the identical filter in the
    // `if def.typ.is_known()` branch above, for why.
    atom_paths.extend(
      body_lower_ctx
        .resolved_atoms()
        .iter()
        .filter(|(a, _)| !global_atom_paths.contains_key(a))
        .map(|(a, p)| (*a, p.clone())),
    );
    let ty =
      infer(mctx, ctx, structs, &body_c).map_err(|e| infer_error_to_type_error(e, mctx.atoms()))?;
    ctx.insert(self_atom, ty.clone());
    let body_c = desugar_struct_literals(
      mctx,
      ctx,
      structs,
      &mut atom_paths,
      known_class_methods,
      known_instances,
      &dict_scope,
      &body_c,
      Some(&ty),
    );
    // See the annotated branch above: drain this def's own resolutions
    // now (AFTER desugar_struct_literals), before the next def's check
    // appends more.
    if let Some(program) = core_out.as_deref_mut() {
      insert_match_resolutions(
        program,
        capture_path,
        &def.name,
        mctx.take_match_resolutions(),
      );
    }
    // Unlike the annotated branch, there's no pre-existing `Term` for an
    // inferred type — it has to be raised too, and (unlike the checked
    // term) it CAN contain unresolved metavariables at this point, so
    // `zonk` + `generalize` (re-closing any still-unresolved meta as a
    // fresh `Forall`) must run first — see `raise_core`'s module doc for
    // why this is the one case that needs it. No peeled vars exist in
    // this branch (nothing to peel from — the type isn't declared).
    let ty_zonked = zonk(mctx, &ty);
    let ty_generalized = generalize(mctx, &ty_zonked, |_m| {
      DebugName::Named(Identifier::new("T".to_string()))
    });
    if let Some(program) = core_out {
      insert_checked_def(
        program,
        capture_path,
        &def.name,
        CheckedCoreDef {
          term: body_c.clone(),
          typ: ty_generalized.clone(),
          atom_paths: atom_paths.clone(),
        },
      );
    }
    new_def.typ = raise_core(&ty_generalized, &atom_paths);
    new_def.term = raise_core(&body_c, &atom_paths);
    Ok(new_def)
  }
}

/// Turns an `instance` declaration into a real, checked dictionary value —
/// D2 of `plans/implementations/dictionary-passing-instance-resolution.md`'s
/// new-checker retargeting. A dictionary is just a value of the class's own
/// "class-as-single-constructor-inductive" type (see `register_inductive`'s
/// `Class` branch): each method in `instance.impls_map` is checked
/// independently via `check_one_def_new` (its own declared type, if any,
/// already fully monomorphic — e.g. `I64` substituted for the class's `A` —
/// so no dictionary-specific checking is needed here), then the checked
/// method bodies are assembled into a `Term::Con` in the class's own
/// DECLARED method order (`class_method_order`) — NOT `impls_map`'s
/// iteration order, which is unordered by name, and NOT `instance.cons`'s
/// own order, which follows the `instance` block's own (unspecified
/// relative to the class's) written order.
///
/// Returns `Ok(None)` (rather than erroring) for shapes this phase doesn't
/// yet handle — the class isn't a known single-param class, or a method the
/// class declares has no override in `impls_map` (a default-method
/// implementation, out of scope for now) — so callers fall back to the
/// pre-existing unchecked pass-through for those instances instead of
/// hard-failing the whole module.
#[allow(clippy::too_many_arguments)]
fn check_one_instance_new(
  mctx: &mut MetaContext,
  ctx: &mut TyCtx,
  structs: &StructFields,
  instance: &Instance,
  config: &LowerConfig,
  global_atom_paths: &Map<Atom, ModulePath>,
  known_class_methods: &KnownClassMethods,
  known_instances: &KnownInstances,
  class_method_order: &Map<ModulePath, Vec<Identifier>>,
  // Phase 0 capture — see `check_one_def_new`'s doc comment. Each
  // method's OWN `Def.name` is a bare, non-instance-qualified identifier
  // (`instance_inner_parser` parses each method with an ordinary
  // `def_parser`, same as a ordinary top-level def) — passing it through
  // to `check_one_def_new` unqualified would collide across different
  // instances' same-named methods (every `BEq` instance has a `beq`), so
  // each method is captured under `instance.name().append([method_name])`
  // instead, and the instance's own dictionary shape (which method path
  // implements which class, in declared order) is recorded separately —
  // no `CoreTerm::Con` for the instance's own assembled dictionary value
  // is built or captured here; a lowering pass reconstructs it on demand
  // from the per-method paths this records.
  mut core_out: Option<&mut CoreProgram>,
) -> Result<Option<Def>, TypeError> {
  let Some(method_order) = class_method_order.get(&instance.class_name) else {
    return Ok(None);
  };
  let mut args: Vec<Option<Term>> = Vec::with_capacity(method_order.len());
  for method_name in method_order {
    let Some(method_def) = instance.impls_map.get(method_name) else {
      return Ok(None);
    };
    // An instance is a def which is a value instance of the class — its
    // own constraints (`[BEq A]` in `instance [BEq A] BEq (List A) {...}`)
    // apply to every one of its methods too, even though each method's
    // OWN `Def.type_constraints` is always empty (the `[BEq A]` was
    // written on the `instance` line, not the individual `def beq (...)`
    // line). Without this, a method that recursively calls a class method
    // on the instance's own constrained type variable (e.g. `beq`'s
    // `BEq.beq x_tail y_tail`, needing a `BEq A` dictionary while `A` is
    // still abstract) can never resolve it.
    let mut method_def = method_def.clone();
    method_def
      .type_constraints
      .extend(instance.constraints.iter().cloned());
    let method_capture_path = instance.name().clone().append(vec![method_name.clone()]);
    let checked = check_one_def_new(
      mctx,
      ctx,
      structs,
      &method_def,
      config,
      global_atom_paths,
      known_class_methods,
      known_instances,
      core_out.as_deref_mut(),
      &method_capture_path,
    )?;
    args.push(Some(checked.term));
  }
  if let Some(program) = core_out {
    program.instances.insert(
      instance.name().clone(),
      CoreInstanceInfo {
        class_name: instance.class_name.clone(),
        method_paths: method_order
          .iter()
          .map(|m| instance.name().clone().append(vec![m.clone()]))
          .collect(),
      },
    );
  }
  let cons = constructor(
    instance.class_name.last().clone(),
    instance.class_name.clone(),
    args,
  );
  // Forall-wrap over the instance's own generic params before publishing
  // this dictionary def's `.typ` — this is what OTHER modules/files
  // actually read back (via `module.get_def`/`ground_truth_from_loaded`)
  // to build their OWN `ctx` entry for this instance atom, a separate
  // path from (and just as important as) the same Forall-wrap this
  // module's own pre-registration loop above applies for in-file forward
  // references. Without it, a still-generic instance's (`instance {A :
  // Type} Append (List A) {...}`) declared type publishes with "A" as a
  // bare, un-Forall-bound free identifier — every consumer's `lower_term`
  // then resolves it through the same fallback any other unbound
  // lowercase name gets, permanently fixing "A" to ONE shared,
  // non-reinstantiable atom instead of something `instantiate_foralls`
  // can freshly re-instantiate per use site.
  let typ_with_foralls = instance
    .params
    .iter()
    .rev()
    .fold(instance.typ().clone(), |body, param| {
      forall(param.clone(), body)
    });
  Ok(Some(def(
    instance.name().clone(),
    Vec::new(),
    typ_with_foralls,
    Term::Con(cons),
    instance.attributes.clone(),
  )))
}

/// The real, production module-level entry point for the checker — B0c of
/// `plans/implementations/typechecker-de-bruijn-core.md`'s cutover phase,
/// now the sole checker (the old name-keyed-unifier checker it replaced,
/// `eval::type::type_check_module_decls`, has been removed — see
/// `plans/implementations/core-term-closure-evaluator.md`). Reuses
/// `elaborate_decls`/`check_strict_positivity`/`check_termination_all`
/// from the old checker's module (none of which are implicated in the
/// name-collision bug this whole redesign targets — they don't touch
/// unification) rather than reimplementing them.
///
/// Known, documented gap relative to full parity: `Decl::Ins` (instance)
/// bodies are NOT checked by this path — passed through unchanged, same
/// as `Decl::DefMacro`/`Decl::DeclGen`/`Decl::MacroCall`/`Decl::Infix`/
/// `Decl::Open` already are in the OLD checker too. This mirrors the
/// "coarse class-method approximation" already documented at the top of
/// this file — real per-instance validation is
/// `implementations/dictionary-passing-instance-resolution.md`'s job (a
/// later phase this cutover is a prerequisite for), not attempted here.
pub fn type_check_module_decls_new(
  path: &ModulePath,
  decls: Vec<SourceContext<Decl>>,
  loaded: &LoadedModules,
) -> Result<Vec<SourceContext<Decl>>, TypeError> {
  type_check_module_decls_new_inner(path, decls, loaded, None)
}

/// Same as `type_check_module_decls_new`, plus opt-in whole-program
/// `CoreTerm` retention (Phase 0 of
/// `plans/implementations/core-term-closure-evaluator.md`) — every
/// checked def's/instance-method's pre-`raise_core` body, plus enough
/// `Match`/inductive/instance metadata for a `CoreTerm -> IR` lowering
/// pass to consume, are captured into `core_out` when `Some`. `None`
/// (via `type_check_module_decls_new`'s thin wrapper, every existing
/// call site) is behaviorally and cost-wise identical to before this was
/// added.
pub fn type_check_module_decls_new_inner(
  path: &ModulePath,
  decls: Vec<SourceContext<Decl>>,
  loaded: &LoadedModules,
  mut core_out: Option<&mut CoreProgram>,
) -> Result<Vec<SourceContext<Decl>>, TypeError> {
  let decls: Vec<SourceContext<Decl>> = if loaded.config.test_mode {
    decls
  } else {
    decls
      .into_iter()
      .filter(|ctx| match ctx.value() {
        Decl::Use(u) if u.has_cfg_test_attr() => false,
        Decl::Open(o) if o.has_cfg_test_attr() => false,
        _ => true,
      })
      .collect()
  };

  let elaborated = elaborate_decls(decls, loaded);
  let expanded = expand_macros(elaborated, loaded, path).map_err(TypeError::MacroExpansion)?;
  // Phase 0 capture: each inductive's constructors, in declaration order
  // (order *is* the constructor's tag, matching the recursor-compilation
  // convention `lower.rs`/`eval_term.rs` already use) — read directly off
  // the surface `Decl::Type` data, no dependency on `register_inductive`'s
  // internal `StructFields` bookkeeping.
  if let Some(program) = core_out.as_deref_mut() {
    for decl in &expanded {
      if let Decl::Type(ind) = &**decl {
        // A single-constructor ("struct-shaped") inductive's sole
        // constructor's params, in declaration order — needed to
        // re-order a `CoreLit::StructLit`/`StructUpdate` (keyed by field
        // name, unordered) into an ordinary positional `Con` at lowering
        // time.
        let struct_field_names = match ind.constructors().as_slice() {
          [only] => Some(only.params.iter().map(|p| p.name.clone()).collect()),
          _ => None,
        };
        program.inductives.insert(
          ind.name().clone(),
          CoreInductiveInfo {
            constructors: ind
              .constructors()
              .iter()
              .map(|c| CoreConstructorInfo {
                name: c.name().last().clone(),
                arity: c.params.len() as u32,
              })
              .collect(),
            struct_field_names,
          },
        );
      }
    }
  }
  let mut atoms = AtomTable::new();
  let known_class_methods = collect_known_class_methods(loaded, &expanded, &mut atoms);
  let class_method_order = collect_class_method_order(loaded, &expanded);

  let GroundTruth {
    mut ctx,
    mut infix,
    mut known_globals,
    mut structs,
  } = ground_truth_from_loaded(loaded, &mut atoms);
  for decl in &expanded {
    if let Decl::Infix(i) = &**decl {
      infix.insert(i.operator().clone(), i.name().clone());
    }
  }

  let mut opens: Vec<&Open> = Vec::new();
  if let Some(prelude_module) = loaded.get_module(&prelude_path()) {
    opens.extend(prelude_module.get_opens().iter().map(|ctx| ctx.value()));
  }
  let file_opens: Vec<&Open> = expanded
    .iter()
    .filter_map(|decl| match &**decl {
      Decl::Open(o) => Some(o),
      _ => None,
    })
    .collect();
  opens.extend(file_opens);

  let config_no_aliases = LowerConfig {
    infix: infix.clone(),
    ..Default::default()
  };
  register_type_decls(
    &mut ctx,
    &mut known_globals,
    &mut structs,
    &expanded,
    &config_no_aliases,
    &mut atoms,
  );
  // Needs `structs`/`infix` fully populated (see `collect_known_instances`'s
  // own doc comment) -- moved here from right after parsing, before
  // `register_type_decls` had run.
  let known_instances = collect_known_instances(loaded, &expanded, &structs, &mut atoms, &infix);
  for decl in &expanded {
    if let Decl::Def(def) = &**decl {
      let atom = atoms.intern(def.name.clone());
      known_globals.insert(def.name.clone(), atom);
    }
  }
  // An instance becomes an ordinary def too (see the `Decl::Ins` arm
  // below) — pre-register its own name/type here, same as an ordinary
  // `Decl::Def` just above, so a sibling def processed earlier in file
  // order can still forward-reference it (e.g. a class method call site
  // resolved before the instance producing its dictionary is reached).
  for decl in &expanded {
    if let Decl::Ins(instance) = &**decl {
      let atom = atoms.intern(instance.name().clone());
      known_globals.insert(instance.name().clone(), atom);
      // An instance's own generic params (`instance {A : Type} Append
      // (List A) {...}`) never go through `elaborate_decls`'s Forall-
      // elaboration the way a `Decl::Def`'s declared type does (that pass
      // only looks at `Decl::Def`s) — lowering `instance.typ()` as-is
      // (just `Append (List A)`, "A" a free lowercase identifier with no
      // binder) resolves "A" through the same global-name fallback every
      // OTHER unbound lowercase identifier gets, permanently fixing it to
      // ONE shared, non-reinstantiable atom for this instance's ENTIRE
      // registered type. Every later `infer` of this instance's own
      // dictionary value (e.g. `xs ++ ys`, needing `Append (List I64)`'s
      // concrete element type to pin down an outer `BEq.beq` call) then
      // tries to unify a real concrete type against this frozen
      // placeholder atom and fails, instead of freshly re-instantiating
      // it per use the way any other polymorphic def's type would.
      // Forall-wrap over the instance's own declared params first so
      // `instantiate_foralls` can do exactly that.
      let typ_with_foralls = instance
        .params
        .iter()
        .rev()
        .fold(instance.typ().clone(), |body, param| {
          forall(param.clone(), body)
        });
      if let Ok(typ_c) = lower_term(
        &mut LowerContext::with_config(config_no_aliases.clone(), &mut atoms),
        &typ_with_foralls,
      ) {
        ctx.insert(atom, typ_c);
      }
    }
  }
  let aliases = compute_unqualified_aliases(&known_globals, &opens);
  // Owned copy of `opens`, independent of `expanded`'s borrow (`opens`
  // itself holds `&Open`s borrowed from `expanded`'s `Decl::Open` decls) —
  // needed below since `Decl::ScopedOpen` handling in the per-decl loop
  // must build an augmented opens list while `expanded` is being moved
  // into that same loop.
  let owned_opens: Vec<Open> = opens.iter().map(|o| (*o).clone()).collect();
  let config = LowerConfig {
    infix,
    unqualified_aliases: aliases,
    ..Default::default()
  };

  for decl in &expanded {
    if let Decl::Def(def) = &**decl
      && def.typ.is_known()
    {
      let self_atom = atoms.intern(def.name.clone());
      if let Ok(typ_c) = lower_term(
        &mut LowerContext::with_config(config.clone(), &mut atoms),
        &def.typ,
      ) {
        let (typ_c, _) = elaborate_constrained_type(
          typ_c,
          def.type_constraints(),
          &def.term,
          &structs,
          &mut atoms,
          &config.infix,
        );
        ctx.insert(self_atom, typ_c);
      }
    }
  }

  let mut mctx = MetaContext::new_with_atoms(atoms);
  if core_out.is_some() {
    mctx.enable_match_capture();
  }
  let mut errors: Vec<TypeError> = Vec::new();
  let mut checked: Vec<SourceContext<Decl>> = Vec::with_capacity(expanded.len());
  let module_context = std::sync::Arc::new(ModuleContext::new(path.clone(), None));
  // `raise_core`'s reverse `Atom -> ModulePath` lookup for global names —
  // built once from the now-fully-populated `known_globals` (every
  // default/loaded-module name plus this file's own), reused for every
  // def (each def additionally extends its OWN copy with its peeled
  // Forall params — see `check_one_def_new`).
  let mut global_atom_paths: Map<Atom, ModulePath> = known_globals
    .iter()
    .map(|(path, atom)| (*atom, path.clone()))
    .collect();
  // Cross-module bare-name collision guard: `known_globals`'s BARE entry
  // for a given name (`list_contains`, say) is shared across every
  // MODULE that happens to declare something under that same bare name
  // (`ground_truth_from_loaded` interns every loaded module's defs under
  // their own bare `def.name`, one flat map for the whole program) --
  // two genuinely independent modules (`lang.module`/`string`, in the
  // real corpus) both declaring `list_contains` end up sharing ONE bare
  // atom. `ctx`'s own TYPE lookup for THIS module's own self-references
  // is already correct regardless (the `for decl in &expanded { ...
  // known_globals.insert(def.name.clone(), atom) ... }` loop above, and
  // `ctx`'s equivalent, re-register LAST, winning over whatever
  // `ground_truth_from_loaded`'s cross-module iteration left there) --
  // but `global_atom_paths` (this atom's PATH, not its type -- used by
  // `lower_program`'s whole-program `GlobalInterner` to assign a GLOBAL
  // SLOT during lowering) was still built from `known_globals`'s raw,
  // still-bare KEY. Force THIS module's own defs'/instances' bare atoms
  // to resolve through their OWN qualified path here, UNCONDITIONALLY
  // (not just for names that happen to collide -- an earlier, narrower
  // version of this fix needed to know which names were "genuinely
  // colliding," but that's no longer necessary now that
  // `insert_checked_def` inserts every def under BOTH its bare and
  // qualified `CoreProgram.defs` keys unconditionally: a non-colliding
  // name's bare and qualified slots simply hold the same body, so
  // forcing every self-reference through the qualified one is free and
  // always correct, colliding or not). This is what makes
  // `insert_checked_def`'s qualified slot reachable at all from a
  // same-module self-reference -- without it, `lang.module.mo`'s own
  // `list_contains` and `string.mo`'s own `list_contains` would both
  // still resolve their own bare self-references through the SAME
  // shared bare slot (whichever module's body was inserted last).
  // `Decl::Ins` (instance dictionaries) deliberately excluded here: an
  // instance's own name is already a synthesized, near-globally-unique
  // identifier ("instance-Similar-Identifier", one per (class, type)
  // pair) — qualifying it too would force its self-references through
  // the qualified path while `program.instances`/`check_one_instance_
  // new` still register it under the bare name only, unconditionally
  // (never double-inserted the way `insert_checked_def` handles
  // `program.defs`) -- a real regression found running lang's own
  // `Similar`-class tests (14 instances, one per lang.types.mo type)
  // through this exact override before it was narrowed to `Decl::Def`.
  //
  // Gated on `core_out.is_some()`: this override's ENTIRE purpose is
  // making `insert_checked_def`'s qualified `CoreProgram.defs` slot
  // reachable from a same-module self-reference, which only matters
  // when a `CoreProgram` is actually being captured (whole-program
  // lowering, `lower_program`'s `GlobalInterner`). When `core_out` is
  // `None` (`type_check_module_decls_new`'s ordinary single-module
  // path, e.g. every `load_module_from_text` call), this function's
  // OUTPUT is a raised old-style `Term` (`raise_core`, below, using this
  // same `global_atom_paths`/`atom_paths`), consumed by the OLD
  // Scope-based tree-walker -- which registers every def under its BARE
  // name, never a module-qualified one. Forcing `atom_paths` to the
  // qualified path here unconditionally made `raise_core` emit a
  // `Term::Global` the old scope could never resolve (confirmed
  // regression: `init/string.mo`'s `String.is_empty` calling its own
  // sibling `String.length` raised to `Global("string.String.length")`,
  // "not found" at runtime -- the old scope only knows `"String.length"`).
  if core_out.is_some() {
    for decl in &expanded {
      match &**decl {
        Decl::Def(def) => {
          let bare_atom = mctx.atoms_mut().intern(def.name.clone());
          global_atom_paths.insert(bare_atom, path.clone().extend(def.name.clone()));
        }
        _ => {}
      }
    }
  }
  for decl_ctx in expanded {
    let decl = decl_ctx.value().clone();
    let result: Result<Decl, TypeError> = match decl {
      Decl::Use(ref u) => {
        if loaded.get_module(&u.module_path).is_none() {
          Err(TypeError::Scope(
            ScopeError::PathNotFound(u.module_path.clone()),
            SourceRange::default(),
          ))
        } else {
          Ok(decl.clone())
        }
      }
      Decl::Def(def) => {
        // Module-qualified -- `insert_checked_def` (called from
        // `check_one_def_new`) additionally stores this under `def.name`
        // bare too, so either form finds it.
        let capture_path = path.clone().extend(def.name.clone());
        check_one_def_new(
          &mut mctx,
          &mut ctx,
          &structs,
          &def,
          &config,
          &global_atom_paths,
          &known_class_methods,
          &known_instances,
          core_out.as_deref_mut(),
          &capture_path,
        )
        .map(Decl::Def)
      }
      Decl::Type(ref ind) => check_strict_positivity(ind).map(|()| decl.clone()),
      Decl::Ins(ref instance) => {
        // `Module`'s own `instances` field (`term/module.rs`'s `module()`
        // constructor) is built by a plain top-level filter over these
        // checked decls for `Decl::Ins` — the OLD checker's runtime
        // class-dispatch fallback (`eval.rs`'s `resolve_class_method_instance`)
        // and `find_instance` both depend on finding it there. So the
        // original `Decl::Ins` MUST keep passing through unchanged (never
        // replaced by the dictionary `Decl::Def` below) — the dictionary is
        // pushed as an ADDITIONAL, separate top-level decl instead.
        match check_one_instance_new(
          &mut mctx,
          &mut ctx,
          &structs,
          instance,
          &config,
          &global_atom_paths,
          &known_class_methods,
          &known_instances,
          &class_method_order,
          core_out.as_deref_mut(),
        ) {
          Ok(Some(dict_def)) => {
            checked.push(decl_ctx.with(Decl::Def(dict_def)));
            Ok(decl.clone())
          }
          // The instance doesn't fit the single-param-class dictionary
          // model this phase handles (e.g. its class isn't in
          // `class_method_order`, or an expected method is missing from
          // `impls_map` — a default-method override, out of scope for
          // now) — fall back to the pre-existing unchecked pass-through
          // rather than erroring on cases this phase doesn't cover yet.
          Ok(None) => Ok(decl.clone()),
          Err(e) => Err(e),
        }
      }
      Decl::ScopedOpen {
        ref module_path,
        ref filter,
        ref decl,
        ..
      } => {
        // Widen `unqualified_aliases` with names the scoped `open` makes
        // reachable, but ONLY for checking this one wrapped declaration —
        // `config`/`opens` outside this arm are left untouched, so the
        // widening never leaks to sibling decls. Re-wrap the checked inner
        // decl back into `ScopedOpen` (rather than unwrapping it here) so
        // this function's `Vec<SourceContext<Decl>> -> Vec<SourceContext<Decl>>`
        // contract stays intact; `Module::add_decl` unwraps it later.
        let scoped_open_val = Open {
          source_location: SourceRange::default(),
          module_path: module_path.clone(),
          filter: filter.clone(),
          attributes: vec![],
        };
        let mut scoped_opens: Vec<&Open> = owned_opens.iter().collect();
        scoped_opens.push(&scoped_open_val);
        let scoped_aliases = compute_unqualified_aliases(&known_globals, &scoped_opens);
        let mut scoped_config = config.clone();
        scoped_config.unqualified_aliases.extend(scoped_aliases);

        let rewrap = |inner: Decl| Decl::ScopedOpen {
          module_path: module_path.clone(),
          filter: filter.clone(),
          attributes: vec![],
          decl: Box::new(inner),
        };
        match &**decl {
          Decl::Def(def) => {
            // Module-qualified -- see the identical comment at the
            // ordinary `Decl::Def` arm above.
            let capture_path = path.clone().extend(def.name.clone());
            check_one_def_new(
              &mut mctx,
              &mut ctx,
              &structs,
              def,
              &scoped_config,
              &global_atom_paths,
              &known_class_methods,
              &known_instances,
              core_out.as_deref_mut(),
              &capture_path,
            )
            .map(|d| rewrap(Decl::Def(d)))
          }
          other_inner => Ok(rewrap(other_inner.clone())),
        }
      }
      Decl::Generated(inner) => {
        // Mirrors the OLD checker's own `Decl::Generated` handling
        // (`type_check_decl`'s `Generated` arm): check each nested decl
        // the same way, stopping at the first error.
        let mut checked_inner = Vec::with_capacity(inner.len());
        let mut first_err = None;
        for d in inner {
          match d {
            Decl::Def(def) => {
              // Module-qualified -- see the identical comment at the
              // ordinary `Decl::Def` arm above.
              let capture_path = path.clone().extend(def.name.clone());
              match check_one_def_new(
                &mut mctx,
                &mut ctx,
                &structs,
                &def,
                &config,
                &global_atom_paths,
                &known_class_methods,
                &known_instances,
                core_out.as_deref_mut(),
                &capture_path,
              ) {
                Ok(nd) => checked_inner.push(Decl::Def(nd)),
                Err(e) => {
                  first_err = Some(e);
                  break;
                }
              }
            }
            other => checked_inner.push(other),
          }
        }
        match first_err {
          Some(e) => Err(e),
          None => Ok(Decl::Generated(checked_inner)),
        }
      }
      // `Decl::Ins`/`DefMacro`/`DeclGen`/`MacroCall`/`Infix`/`Open` all
      // pass through unchecked — see this function's doc comment.
      other => Ok(other),
    };
    match result {
      Ok(d) => checked.push(decl_ctx.with(d)),
      Err(e) => errors.push(TypeError::Context {
        name: Some(decl_ctx.value().to_ref().clone()),
        loc: decl_ctx.loc.clone(),
        err: Box::new(e),
        module: module_context.clone(),
      }),
    }
  }

  if !errors.is_empty() {
    return Err(TypeError::Many(errors));
  }

  let defs: Vec<&Def> = checked
    .iter()
    .filter_map(|ctx| match ctx.value() {
      Decl::Def(d) => Some(d),
      _ => None,
    })
    .collect();
  if !defs.is_empty() {
    check_termination_all(&defs).map_err(TypeError::Termination)?;
  }

  Ok(checked)
}

/// Build a whole-program `CoreProgram` by checking `modules` (each an
/// already-parsed, unchecked module's own `(path, decls)`) against
/// `loaded` — Phase 0's driver.
///
/// `loaded` must already be a fully-loaded `LoadedModules` (built via the
/// normal `default_modules()`/`load_module_from_text`/`load_module_files`
/// pipeline, unmodified — this driver does not mutate it) so every
/// module's own `check_one_def_new`/`check_one_instance_new` calls can
/// resolve names against the complete set of already-checked siblings.
/// Deliberately does NOT read `loaded.modules()`'s own stored decls —
/// those are already the CHECKED, raised `Term`-based output of the
/// normal loading pipeline, not the unchecked surface syntax this
/// function's `type_check_module_decls_new_inner` calls need as input.
/// Callers supply each module's raw decls directly (e.g. via
/// `term::module::load_decls`/`load_decls_from_text_with_path`), which
/// they already had in hand before the normal pipeline consumed and
/// replaced them.
///
/// Modules can be checked in any order: each call only reads `loaded`
/// (already fully populated, order-independent) for name resolution and
/// writes its own independent output into `program` — there's no
/// cross-call ordering dependency the way the real loading pipeline has
/// via `load_decl_uses_modules`.
pub fn check_all_modules_capturing_core(
  modules: &[(ModulePath, Vec<SourceContext<Decl>>)],
  loaded: &LoadedModules,
) -> Result<CoreProgram, TypeError> {
  let mut program = CoreProgram::new();
  for (path, decls) in modules {
    type_check_module_decls_new_inner(path, decls.clone(), loaded, Some(&mut program))?;
  }
  Ok(program)
}

#[cfg(test)]
mod test {
  use super::*;

  fn print_report(file: &str, report: &ModuleReport) {
    eprintln!(
      "== {file}: {}/{} defs checked, {} skipped decls ==",
      report.passed(),
      report.defs.len(),
      report.skipped.len()
    );
    if let Some(e) = &report.parse_error {
      eprintln!("  PARSE/LOAD ERROR: {e}");
    }
    for outcome in &report.defs {
      match &outcome.result {
        Ok(()) => eprintln!("  PASS {}", outcome.name),
        Err(e) => eprintln!("  FAIL {} — {:?}", outcome.name, e),
      }
    }
  }

  // -------------------------------------------------------------------
  // Small, controlled fixtures first — confirm the harness itself
  // works before pointing it at real files with unknown content.
  // -------------------------------------------------------------------

  #[test]
  fn test_harness_checks_simple_monomorphic_def() {
    let env = ModuleCheckEnv::new();
    let report = check_module_source(&env, "def one : I64 := 1\n");
    assert_eq!(report.defs.len(), 1);
    assert!(
      report.defs[0].result.is_ok(),
      "expected pass, got {:?}",
      report.defs[0].result
    );
  }

  #[test]
  fn test_harness_supports_cross_def_reference() {
    let env = ModuleCheckEnv::new();
    let report = check_module_source(&env, "def one : I64 := 1\ndef two : I64 := one\n");
    assert_eq!(report.passed(), 2, "report: {report:?}");
  }

  #[test]
  fn test_harness_supports_forward_reference_to_later_sibling_def() {
    // `first` (checked FIRST, in file order) calls `second`, declared
    // AFTER it — matches std/list.mo's real list_show/show_body shape
    // exactly (list_show, defined first, calls show_body, defined
    // after it). Both are explicitly typed, so `ctx`'s pre-registration
    // pass covers this regardless of processing order.
    let env = ModuleCheckEnv::new();
    let report = check_module_source(&env, "def first : I64 := second\ndef second : I64 := 1\n");
    assert_eq!(report.passed(), 2, "report: {report:?}");
  }

  #[test]
  fn test_harness_catches_real_type_error() {
    let env = ModuleCheckEnv::new();
    let report = check_module_source(&env, "def bad : I64 := \"not a number\"\n");
    assert_eq!(report.defs.len(), 1);
    assert!(report.defs[0].result.is_err());
  }

  #[test]
  fn test_harness_skips_non_def_decls() {
    let env = ModuleCheckEnv::new();
    let report = check_module_source(&env, "type Foo { bar }\ndef ok : I64 := 1\n");
    assert_eq!(report.skipped, vec!["type"]);
    assert_eq!(report.passed(), 1);
  }

  #[test]
  fn test_harness_supports_recursive_def() {
    // A def whose body calls itself (matches the shape of most real
    // recursive functions, e.g. std/list.mo's List.any) must resolve the
    // self-reference to the SAME atom the def is registered under.
    let env = ModuleCheckEnv::new();
    let report = check_module_source(&env, "def loop : I64 := loop\n");
    assert_eq!(report.defs.len(), 1);
    assert!(
      report.defs[0].result.is_ok(),
      "expected pass, got {:?}",
      report.defs[0].result
    );
  }

  #[test]
  fn test_harness_resolves_prelude_constructors_by_qualified_path() {
    // `Bool.true`/`Bool.false` are ordinary constructors from
    // default_modules()'s prelude — resolve via the real ground truth
    // (ModuleCheckEnv, built from default_modules()'s loaded modules),
    // not a hardcoded name list.
    let env = ModuleCheckEnv::new();
    let report = check_module_source(&env, "def t : Bool := Bool.true\n");
    assert_eq!(report.defs.len(), 1);
    assert!(
      report.defs[0].result.is_ok(),
      "expected pass, got {:?}",
      report.defs[0].result
    );
  }

  #[test]
  fn test_harness_resolves_prelude_constructors_unqualified_via_open() {
    // Bare `true` relies on prelude.mo's own internal `open Bool` — the
    // real `GlobalScope` always chains prelude's opens into every
    // module's resolution, so this file (which itself declares no
    // `open`) still sees `true` as `Bool.true` via
    // `compute_unqualified_aliases`'s prelude-opens handling.
    let env = ModuleCheckEnv::new();
    let report = check_module_source(&env, "def t : Bool := true\n");
    assert_eq!(report.defs.len(), 1);
    assert!(
      report.defs[0].result.is_ok(),
      "expected pass, got {:?}",
      report.defs[0].result
    );
  }

  #[test]
  fn test_harness_resolves_via_own_open_decl() {
    // The file's OWN `open` (not just prelude's ambient ones) must also
    // widen what a bare name can resolve to — `Nat.zero`/`Nat.succ`
    // opened here, referenced unqualified.
    let env = ModuleCheckEnv::new();
    let report = check_module_source(
      &env,
      "open Nat\ndef z : Nat := zero\ndef one : Nat := succ zero\n",
    );
    assert_eq!(report.passed(), 2, "report: {report:?}");
  }

  #[test]
  fn test_harness_scoped_open_applies_only_to_its_own_decl() {
    let env = ModuleCheckEnv::new();
    let report = check_module_source(&env, "open Nat in def z : Nat := zero\n");
    assert_eq!(report.passed(), 1, "report: {report:?}");
  }

  #[test]
  fn test_harness_scoped_open_does_not_leak_to_sibling_defs() {
    // `zero`/`succ` are only reachable inside the scoped-open'd `z` — the
    // sibling `bad` def (outside the scope) must NOT see them unqualified.
    let env = ModuleCheckEnv::new();
    let report = check_module_source(
      &env,
      "open Nat in def z : Nat := zero\ndef bad : Nat := succ zero\n",
    );
    assert_eq!(report.passed(), 1, "report: {report:?}");
    assert_eq!(report.failed(), 1, "report: {report:?}");
  }

  #[test]
  fn test_harness_scoped_open_with_filter() {
    let env = ModuleCheckEnv::new();
    let report = check_module_source(&env, "open Nat {zero} in def z : Nat := zero\n");
    assert_eq!(report.passed(), 1, "report: {report:?}");
  }

  #[test]
  fn test_harness_resolves_class_method_by_qualified_path() {
    // `BEq.beq` is a class method (from `class BEq A { def beq : A -> A
    // -> Bool }` in init/prelude.mo), not an ordinary def or constructor
    // — must resolve via register_inductive's class-method handling.
    let env = ModuleCheckEnv::new();
    let report = check_module_source(&env, "def eq_two : Bool := BEq.beq 1 2\n");
    assert_eq!(report.defs.len(), 1);
    assert!(
      report.defs[0].result.is_ok(),
      "expected pass, got {:?}",
      report.defs[0].result
    );
  }

  #[test]
  fn test_harness_class_method_instantiates_independently_per_call() {
    // Two calls to the same class method at different concrete types
    // (I64 vs String) must resolve independently — the actual bug class
    // this whole redesign targets, now exercised through a real
    // typeclass method reference rather than an ordinary generic def.
    let env = ModuleCheckEnv::new();
    let report = check_module_source(
      &env,
      "def a : Bool := BEq.beq 1 2\ndef b : Bool := BEq.beq \"x\" \"y\"\n",
    );
    assert_eq!(report.passed(), 2, "report: {report:?}");
  }

  // -------------------------------------------------------------------
  // Real files. These are a MEASUREMENT, not a pass/fail gate — per the
  // module doc, some failure here is still expected (native-op
  // signatures, cross-module `use` beyond default_modules()'s fixed set)
  // and the point is to see and record exactly where real coverage
  // currently stands.
  // -------------------------------------------------------------------

  #[test]
  fn test_real_file_init_process() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../init/process.mo");
    let report = check_module_source(&env, source);
    print_report("init/process.mo", &report);
  }

  #[test]
  fn test_real_file_init_id() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../init/id.mo");
    let report = check_module_source(&env, source);
    print_report("init/id.mo", &report);
  }

  #[test]
  fn test_real_file_init_io() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../init/io.mo");
    let report = check_module_source(&env, source);
    print_report("init/io.mo", &report);
  }

  #[test]
  fn test_real_file_init_prelude() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../init/prelude.mo");
    let report = check_module_source(&env, source);
    print_report("init/prelude.mo", &report);
  }

  #[test]
  fn test_real_file_std_list() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../std/list.mo");
    let report = check_module_source(&env, source);
    print_report("std/list.mo", &report);
  }

  // -------------------------------------------------------------------
  // Expanding real-file coverage further (no known gap left to chase —
  // see if a wider sample of std/ finds the next one).
  // -------------------------------------------------------------------

  #[test]
  fn test_real_file_std_base() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../std/base.mo");
    let report = check_module_source(&env, source);
    print_report("std/base.mo", &report);
  }

  #[test]
  fn test_real_file_std_show() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../std/show.mo");
    let report = check_module_source(&env, source);
    print_report("std/show.mo", &report);
  }

  #[test]
  fn test_real_file_std_map() {
    // The file at the center of this whole session's original
    // BTreeMap.with_node regression, fixed in the OLD checker via a
    // narrow concreteness guard — a meaningful real test of whether the
    // new checker handles the same recursive-generic-function shape
    // correctly without needing that patch at all.
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../std/map.mo");
    let report = check_module_source(&env, source);
    print_report("std/map.mo", &report);
  }

  #[test]
  fn test_real_file_std_test() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../std/test.mo");
    let report = check_module_source(&env, source);
    print_report("std/test.mo", &report);
  }

  #[test]
  fn test_real_file_std_list_tests1() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../std/list_tests1.mo");
    let report = check_module_source(&env, source);
    print_report("std/list_tests1.mo", &report);
  }

  #[test]
  fn test_real_file_examples_hello() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../examples/hello.mo");
    let report = check_module_source(&env, source);
    print_report("examples/hello.mo", &report);
  }

  #[test]
  fn test_real_file_examples_factorial() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../examples/factorial.mo");
    let report = check_module_source(&env, source);
    print_report("examples/factorial.mo", &report);
  }

  #[test]
  fn test_real_file_examples_do_block() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../examples/do_block.mo");
    let report = check_module_source(&env, source);
    print_report("examples/do_block.mo", &report);
  }

  #[test]
  fn test_real_file_examples_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../examples/tests.mo");
    let report = check_module_source(&env, source);
    print_report("examples/tests.mo", &report);
  }

  #[test]
  fn test_real_file_examples_indexed_monads() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../examples/indexed_monads.mo");
    let report = check_module_source(&env, source);
    print_report("examples/indexed_monads.mo", &report);
  }

  #[test]
  fn test_real_file_examples_pattern_matching() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../examples/pattern_matching.mo");
    let report = check_module_source(&env, source);
    print_report("examples/pattern_matching.mo", &report);
  }

  #[test]
  fn test_real_file_examples_iteration() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../examples/iteration.mo");
    let report = check_module_source(&env, source);
    print_report("examples/iteration.mo", &report);
  }

  #[test]
  fn test_real_file_examples_iteration_advanced() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../examples/iteration_advanced.mo");
    let report = check_module_source(&env, source);
    print_report("examples/iteration_advanced.mo", &report);
  }

  #[test]
  fn test_real_file_examples_structs() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../examples/structs.mo");
    let report = check_module_source(&env, source);
    print_report("examples/structs.mo", &report);
  }

  #[test]
  fn test_real_file_examples_optics() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../examples/optics.mo");
    let report = check_module_source(&env, source);
    print_report("examples/optics.mo", &report);
  }

  #[test]
  fn test_real_file_lang_types() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/types.mo");
    let report = check_module_source(&env, source);
    print_report("lang/types.mo", &report);
  }

  #[test]
  fn test_real_file_lang_eval_term() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/eval_term.mo");
    let report = check_module_source(&env, source);
    print_report("lang/eval_term.mo", &report);
  }

  #[test]
  fn test_real_file_lang_eval() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/eval.mo");
    let report = check_module_source(&env, source);
    print_report("lang/eval.mo", &report);
  }

  #[test]
  fn test_real_file_lang_eval_t2() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/eval_t2.mo");
    let report = check_module_source(&env, source);
    print_report("lang/eval_t2.mo", &report);
  }

  #[test]
  fn test_real_file_lang_elaborate() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/elaborate.mo");
    let report = check_module_source(&env, source);
    print_report("lang/elaborate.mo", &report);
  }

  #[test]
  fn test_real_file_lang_lower() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/lower.mo");
    let report = check_module_source(&env, source);
    print_report("lang/lower.mo", &report);
  }

  #[test]
  fn test_real_file_lang_pretty() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/pretty.mo");
    let report = check_module_source(&env, source);
    print_report("lang/pretty.mo", &report);
  }

  #[test]
  fn test_real_file_lang_scope() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/scope.mo");
    let report = check_module_source(&env, source);
    print_report("lang/scope.mo", &report);
  }

  #[test]
  fn test_real_file_lang_parser() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/parser.mo");
    let report = check_module_source(&env, source);
    print_report("lang/parser.mo", &report);
  }

  #[test]
  fn test_real_file_lang_module() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/module.mo");
    let report = check_module_source(&env, source);
    print_report("lang/module.mo", &report);
  }

  #[test]
  fn test_real_file_lang_main() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/main.mo");
    let report = check_module_source(&env, source);
    print_report("lang/main.mo", &report);
  }

  #[test]
  fn test_real_file_lang_codegen_emit() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/codegen/emit.mo");
    let report = check_module_source(&env, source);
    print_report("lang/codegen/emit.mo", &report);
  }

  #[test]
  fn test_real_file_lang_codegen_ir() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/codegen/ir.mo");
    let report = check_module_source(&env, source);
    print_report("lang/codegen/ir.mo", &report);
  }

  #[test]
  fn test_real_file_lang_codegen_link() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/codegen/link.mo");
    let report = check_module_source(&env, source);
    print_report("lang/codegen/link.mo", &report);
  }

  #[test]
  fn test_real_file_lang_codegen_test_compile_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/codegen/test/compile_tests.mo");
    let report = check_module_source(&env, source);
    print_report("lang/codegen/test/compile_tests.mo", &report);
  }

  #[test]
  fn test_real_file_lang_codegen_test_e2e_typecheck_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/codegen/test/e2e_typecheck_tests.mo");
    let report = check_module_source(&env, source);
    print_report("lang/codegen/test/e2e_typecheck_tests.mo", &report);
  }

  #[test]
  fn test_real_file_lang_codegen_test_ir_emission_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/codegen/test/ir_emission_tests.mo");
    let report = check_module_source(&env, source);
    print_report("lang/codegen/test/ir_emission_tests.mo", &report);
  }

  #[test]
  fn test_real_file_lang_codegen_test_test_e2e() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/codegen/test/test_e2e.mo");
    let report = check_module_source(&env, source);
    print_report("lang/codegen/test/test_e2e.mo", &report);
  }

  #[test]
  fn test_real_file_lang_codegen_test_test_link_e2e() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/codegen/test/test_link_e2e.mo");
    let report = check_module_source(&env, source);
    print_report("lang/codegen/test/test_link_e2e.mo", &report);
  }

  #[test]
  fn test_real_file_lang_parser_char_preds() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/parser/char_preds.mo");
    let report = check_module_source(&env, source);
    print_report("lang/parser/char_preds.mo", &report);
  }

  #[test]
  fn test_real_file_lang_parser_combinators() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/parser/combinators.mo");
    let report = check_module_source(&env, source);
    print_report("lang/parser/combinators.mo", &report);
  }

  #[test]
  fn test_real_file_lang_parser_core() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/parser/core.mo");
    let report = check_module_source(&env, source);
    print_report("lang/parser/core.mo", &report);
  }

  #[test]
  fn test_real_file_lang_parser_identifier() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/parser/identifier.mo");
    let report = check_module_source(&env, source);
    print_report("lang/parser/identifier.mo", &report);
  }

  #[test]
  fn test_real_file_lang_parser_number() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/parser/number.mo");
    let report = check_module_source(&env, source);
    print_report("lang/parser/number.mo", &report);
  }

  #[test]
  fn test_real_file_lang_parser_position() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/parser/position.mo");
    let report = check_module_source(&env, source);
    print_report("lang/parser/position.mo", &report);
  }

  #[test]
  fn test_real_file_lang_parser_string() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/parser/string.mo");
    let report = check_module_source(&env, source);
    print_report("lang/parser/string.mo", &report);
  }

  #[test]
  fn test_real_file_lang_parser_tests_test_string_get() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/parser/tests/test_string_get.mo");
    let report = check_module_source(&env, source);
    print_report("lang/parser/tests/test_string_get.mo", &report);
  }

  #[test]
  fn test_real_file_lang_parser_whitespace() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/parser/whitespace.mo");
    let report = check_module_source(&env, source);
    print_report("lang/parser/whitespace.mo", &report);
  }

  #[test]
  fn test_real_file_lang_tests_elaborate_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/tests/elaborate_tests.mo");
    let report = check_module_source(&env, source);
    print_report("lang/tests/elaborate_tests.mo", &report);
  }

  #[test]
  fn test_real_file_lang_tests_infer_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/tests/infer_tests.mo");
    let report = check_module_source(&env, source);
    print_report("lang/tests/infer_tests.mo", &report);
  }

  #[test]
  fn test_real_file_lang_tests_module_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/tests/module_tests.mo");
    let report = check_module_source(&env, source);
    print_report("lang/tests/module_tests.mo", &report);
  }

  #[test]
  fn test_real_file_lang_tests_parser_file_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/tests/parser_file_tests.mo");
    let report = check_module_source(&env, source);
    print_report("lang/tests/parser_file_tests.mo", &report);
  }

  #[test]
  fn test_real_file_lang_tests_pretty_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/tests/pretty_tests.mo");
    let report = check_module_source(&env, source);
    print_report("lang/tests/pretty_tests.mo", &report);
  }

  #[test]
  fn test_real_file_lang_tests_scope_all_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/tests/scope_all_tests.mo");
    let report = check_module_source(&env, source);
    print_report("lang/tests/scope_all_tests.mo", &report);
  }

  #[test]
  fn test_real_file_lang_tests_scope_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/tests/scope_tests.mo");
    let report = check_module_source(&env, source);
    print_report("lang/tests/scope_tests.mo", &report);
  }

  #[test]
  fn test_real_file_lang_tests_typecheck_examples_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/tests/typecheck_examples_tests.mo");
    let report = check_module_source(&env, source);
    print_report("lang/tests/typecheck_examples_tests.mo", &report);
  }

  #[test]
  fn test_real_file_slow_tests_typecheck_init_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../slow_tests/typecheck_init_tests.mo");
    let report = check_module_source(&env, source);
    print_report("slow_tests/typecheck_init_tests.mo", &report);
  }

  #[test]
  fn test_real_file_lang_tests_typecheck_lang_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/tests/typecheck_lang_tests.mo");
    let report = check_module_source(&env, source);
    print_report("lang/tests/typecheck_lang_tests.mo", &report);
  }

  #[test]
  fn test_real_file_slow_tests_typecheck_std_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../slow_tests/typecheck_std_tests.mo");
    let report = check_module_source(&env, source);
    print_report("slow_tests/typecheck_std_tests.mo", &report);
  }

  #[test]
  fn test_real_file_lang_tests_types_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/tests/types_tests.mo");
    let report = check_module_source(&env, source);
    print_report("lang/tests/types_tests.mo", &report);
  }

  #[test]
  fn test_real_file_lang_tests_unify_tests() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/tests/unify_tests.mo");
    let report = check_module_source(&env, source);
    print_report("lang/tests/unify_tests.mo", &report);
  }

  #[test]
  fn test_real_file_lang_typecheck_infer() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/typecheck/infer.mo");
    let report = check_module_source(&env, source);
    print_report("lang/typecheck/infer.mo", &report);
  }

  #[test]
  fn test_real_file_lang_typecheck_unify() {
    let env = ModuleCheckEnv::new();
    let source = include_str!("../../lang/typecheck/unify.mo");
    let report = check_module_source(&env, source);
    print_report("lang/typecheck/unify.mo", &report);
  }
}
