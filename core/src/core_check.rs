//! Bidirectional `infer`/`check` on `CoreTerm` — the second half of Phase 2
//! of `plans/implementations/typechecker-de-bruijn-core.md`.
//!
//! Replaces `core/src/eval/type.rs`'s single `type_check_with_env` (which
//! branches internally on whether `expected_type.is_known()`) with the
//! standard explicit two-mode split: `check` is used wherever an expected
//! type is already known, `infer` at the leaves/heads of an application
//! spine. Built entirely on Phase 0/1's `core_term`/`core_unify` — no new
//! variable-identity machinery here, just the control flow that decides
//! when to call `unify`/`instantiate`/`generalize`.
//!
//! Tested here against hand-built and lowered `CoreTerm` fixtures only
//! (Phases 0/1's style) — running this side by side against real `.mo`
//! files (the plan's parity-testing step) needs `CoreTerm`/the lowering
//! pass to cover `Lit`/`Con`/`Match` first (currently out of scope, see
//! `core_term.rs`'s and `lower_core.rs`'s doc comments), so is deferred to
//! a follow-up increment rather than attempted prematurely here.

use crate::Map;
use crate::core_term::{
  Atom, CoreConstructor, CoreLit, CoreMatchCase, CoreNative, CoreTerm, DebugName, MetaId, close,
  close_n, open_with,
};
use crate::core_unify::{MetaContext, UnifyError, force, instantiate, open_n, unify};
use crate::term::{Identifier, ModulePath, Multiplicity, TypeConstraint};

/// Typing context: which type each currently-open `Free` atom has. Bound
/// variables are never looked up directly — `infer`/`check` always open a
/// binder (assigning it a fresh atom and an entry here) before recursing
/// into its body, so by the time a variable occurrence could need a type
/// lookup, it's always a `Free` with an entry, never a raw `Bound`.
///
/// Structured as a shared, immutable BASE (every globally-registered
/// def/inductive/instance/etc., built up once via `insert` before checking
/// begins) plus a small OVERLAY of locally-opened binders (`Lam` params,
/// match-case field bindings, ...) added via `extend` during checking
/// itself — mirrors `core_value::Env`/`EnvRef`'s own shared-tail,
/// O(1)-extend design (this module's own `core_unify` sibling), adapted
/// for atom-keyed (not de-Bruijn-indexed) lookup instead of a plain
/// index. `extend` never touches `base` at all — one `Arc` refcount bump
/// for the tail, one new overlay-cons allocation — unlike the plain
/// `BTreeMap` this type used to be, whose every binder-open cloned the
/// ENTIRE base (confirmed, on one real corpus file alone: ~9700 such
/// clones of a ~2300-entry map over the course of checking it, ~17.5M
/// total element-clones — the dominant cost behind the checker's
/// real-world runtime, well beyond anything in `try_resolve_class_method`
/// itself). `Atom`s are minted fresh (`Atom::fresh()`) and never reused,
/// so an overlay entry can never collide with a base entry — overlay is
/// simply checked first (fast path for the common case: a just-opened
/// local binder), falling back to `base` (an ordinary `BTreeMap` lookup)
/// for anything registered globally.
#[derive(Debug, Clone)]
pub struct TyCtx {
  base: std::sync::Arc<Map<Atom, CoreTerm>>,
  overlay: TyCtxOverlayRef,
}

#[derive(Debug)]
enum TyCtxOverlay {
  Nil,
  Cons(Atom, CoreTerm, TyCtxOverlayRef),
}

type TyCtxOverlayRef = std::sync::Arc<TyCtxOverlay>;

impl Default for TyCtx {
  fn default() -> Self {
    Self::new()
  }
}

impl TyCtx {
  pub fn new() -> Self {
    Self {
      base: std::sync::Arc::new(Map::new()),
      overlay: std::sync::Arc::new(TyCtxOverlay::Nil),
    }
  }

  pub fn get(&self, atom: &Atom) -> Option<&CoreTerm> {
    let mut cur = &self.overlay;
    loop {
      match cur.as_ref() {
        TyCtxOverlay::Nil => return self.base.get(atom),
        TyCtxOverlay::Cons(a, t, tail) => {
          if a == atom {
            return Some(t);
          }
          cur = tail;
        }
      }
    }
  }

  /// Registration-time insert — copy-on-write into `base` (an O(1) `Arc`
  /// refcount bump if this `TyCtx`'s base isn't currently shared with any
  /// other clone, the common case during the one-time, sequential
  /// "register every def/inductive/instance" phase this is meant for; a
  /// real O(n) copy only the first time after a `.clone()` shared it, not
  /// once per insert). NOT used for per-binder-open during type CHECKING
  /// itself — see `extend` for that, the actual hot path this type
  /// exists to make cheap.
  pub fn insert(&mut self, atom: Atom, typ: CoreTerm) {
    std::sync::Arc::make_mut(&mut self.base).insert(atom, typ);
  }

  /// O(1): the hot path. One `Arc` allocation for the new overlay frame,
  /// `base` just `Arc::clone`d (refcount bump, no copy) — never touches
  /// `base`'s own contents. Returns a NEW `TyCtx` rather than mutating in
  /// place, matching every call site's own "open a binder into a fresh,
  /// scoped ctx2" usage.
  pub fn extend(&self, atom: Atom, typ: CoreTerm) -> Self {
    Self {
      base: self.base.clone(),
      overlay: std::sync::Arc::new(TyCtxOverlay::Cons(atom, typ, self.overlay.clone())),
    }
  }
}

/// Whether a `StructInfo` entry describes an ordinary struct-like inductive
/// or a `class` (registered the same way, one field per method — see
/// `core_check_module.rs`'s `register_inductive`, D1). Lets
/// `is_class_atom` distinguish the two from `structs` alone — the
/// parameter already threaded through every one of `infer`/`check`/
/// `desugar_struct_literals`'s recursive call sites — instead of a
/// separate side table or process-wide registry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StructKind {
  Struct,
  Class,
}

/// One registered struct-like inductive or class's field names and
/// (already-elaborated) declared types, in constructor-parameter order.
#[derive(Debug, Clone)]
pub struct StructInfo {
  pub kind: StructKind,
  pub fields: Vec<(Identifier, CoreTerm)>,
  /// E5: a struct field's own default value (`h: I64 := 100`), lowered —
  /// keyed separately from `fields` (rather than folded into its tuple
  /// shape) purely so the handful of existing `fields`-only consumers
  /// don't all need updating for a field this specific struct-literal
  /// gap needs. A struct literal omitting a field present here gets the
  /// default filled in instead of an `IncompleteConstructor` error.
  pub defaults: Map<Identifier, CoreTerm>,
}

/// One ordinary (possibly multi-constructor, e.g. `List`/`Option`)
/// inductive's declared param atoms and, per constructor, its field types
/// — still referencing the inductive's OWN param atoms freely (NOT yet
/// substituted with any specific use site's concrete type arguments; see
/// `match_case_field_types`, which does that substitution using
/// `param_atoms` to know which atom is which position). Lets a `match`
/// expression's pattern-bound variables get their real field types (E2)
/// instead of `Hole` — needed for a class-method call inside a match arm
/// on a pattern-bound variable (`cons a tail => ... Foldable.foldr f z
/// tail ...`) to resolve at all, since `Hole` unifies with anything
/// without binding any metavariable.
#[derive(Debug, Clone)]
pub struct ConstructorInfo {
  pub param_atoms: Vec<Atom>,
  pub fields: Vec<CoreTerm>,
}

/// Every known struct-like inductive's (or class's, see `StructKind`)
/// field names and (already-elaborated) declared types, in constructor-
/// parameter order, keyed by the inductive's OWN atom
/// (`global_atom(ind.name().clone())` — the atom a `Point`-typed
/// `expected` type carries, NOT the `Point.mk` constructor's atom) —
/// alongside every ordinary inductive's own per-constructor field types
/// (`constructors`, keyed by `(inductive_atom, constructor_name)`), a
/// second table bundled onto the SAME struct (rather than threaded as a
/// separate parameter) purely so every one of `infer`/`check`/
/// `desugar_struct_literals`'s existing recursive call sites — already
/// passing `structs` straight through — don't need touching just to reach
/// this new information too. Lets `check`'s `Lit(StructLit)` arm resolve a
/// struct literal's fields the same way the real checker does — by
/// reading the struct name off the *expected* type, then looking up its
/// constructor's params — without `core_check.rs` needing any module/
/// `Scope` access of its own: callers (`core_check_module`, which already
/// builds an equivalent per-constructor table for `register_inductive`)
/// build and pass this in explicitly, the same explicit-parameter pattern
/// `ModuleCheckEnv` and `LowerConfig` already use elsewhere in this
/// redesign.
#[derive(Debug, Clone, Default)]
pub struct StructFields {
  pub structs: Map<Atom, StructInfo>,
  pub constructors: Map<(Atom, Identifier), ConstructorInfo>,
  /// Every ORDINARY (non-Class) inductive's own bare-name atom
  /// (`List`/`Option`, as opposed to their constructors' own atoms) mapped
  /// back to its `ModulePath` — deliberately kept SEPARATE from
  /// `known_globals`/`compute_unqualified_aliases`'s own forward-name
  /// table, rather than inserted there directly: an ordinary inductive's
  /// bare name is never itself a VALUE a program references by that name
  /// (only its constructors are), so registering it as a `known_globals`
  /// entry would make it eligible for `open`-based unqualified aliasing
  /// alongside every OTHER known global — surprisingly, this can silently
  /// change which of two same-named-but-different globals wins an
  /// `open`-introduced short-form collision elsewhere in the same file
  /// (confirmed: doing this for `lang/json.mo`'s `Json` type flipped an
  /// unrelated `open Json`-introduced "ParseError" short-form collision
  /// against `lang/parser/core.mo`'s OWN unrelated `ParseError` type,
  /// breaking compilation). This table exists purely so
  /// `try_resolve_class_method`/`resolve_instance_dict_args`/
  /// `try_insert_dict_args` can turn a class param's resolved CONCRETE
  /// type atom (e.g. `Foldable T` unifying `T := Option`) back into a
  /// `ModulePath` to key `known_instances` with — checked as a fallback
  /// after `atom_paths` proper, never feeding into alias computation.
  pub inductive_paths: Map<Atom, ModulePath>,
}

impl StructFields {
  pub fn new() -> Self {
    Self::default()
  }
}

/// Whether `atom` names a `class` (as opposed to an ordinary struct-like
/// inductive) — used to recognize a dictionary parameter's type (`BOrd
/// A`, `App(Free(class_atom), _)`) from just its head atom, everywhere
/// `structs` is already available (`instantiate_foralls`'s dict-Pi
/// auto-skip, `try_insert_dict_args`, the `Lam`-arm dictionary-detection
/// in `desugar_struct_literals`).
pub fn is_class_atom(structs: &StructFields, atom: Atom) -> bool {
  structs
    .structs
    .get(&atom)
    .is_some_and(|info| info.kind == StructKind::Class)
}

/// The inductive `Atom` a `Match`/`if` node's scrutinee resolves to, given
/// the scrutinee's own (already-known) type — the same
/// `instantiate_foralls` + `head_atom_of` pair `match_case_field_types`
/// uses internally, factored out so callers can capture it once per
/// `Match` node (Phase 0 of
/// `plans/implementations/core-term-closure-evaluator.md`) instead of
/// only implicitly, per-case, inside that function. Returns `None` under
/// the same conditions `match_case_field_types` would fall back to `Hole`
/// typing for.
pub(crate) fn resolve_match_inductive_atom(
  mctx: &mut MetaContext,
  structs: &StructFields,
  scrutinee_ty: &CoreTerm,
) -> Option<Atom> {
  let forced = instantiate_foralls(mctx, structs, scrutinee_ty);
  head_atom_of(mctx, &forced)
}

/// E2: the real field types for `case_name`'s pattern variables, given the
/// scrutinee's own (already-known) type — substituting the constructor's
/// declared param atoms with the scrutinee's own concrete type arguments
/// (`List I64`'s `cons` fields, declared over `List`'s own "A", become
/// `I64`-typed once substituted) via `close`+`open_with` (turn each
/// `Free(param_atom)` into a `Bound`, then immediately re-open it with the
/// concrete argument — the standard locally-nameless substitution
/// composition). Returns `None` (falling back to the caller's own `Hole`
/// typing, unchanged) whenever the scrutinee's type isn't a registered,
/// ordinary inductive, `case_name` isn't one of its constructors, or its
/// declared arity doesn't match the number of concrete type arguments the
/// scrutinee's own type actually carries (a genuinely malformed program,
/// or a shape this narrow lookup doesn't cover).
fn match_case_field_types(
  mctx: &mut MetaContext,
  structs: &StructFields,
  scrutinee_ty: &CoreTerm,
  case_name: &Identifier,
) -> Option<Vec<CoreTerm>> {
  // A scrutinee that's itself a still-generic instance's own dictionary
  // value (`project_dict_field` on `instance {A:Type} Append (List A)`,
  // as opposed to a fully concrete/ground instance like `FromListLiteral
  // List`) has a `Forall`-wrapped type (`Forall(A, App(Append, App(List,
  // A)))`) — `head_atom_of` only ever sees `Free`/`App`, so without
  // instantiating any leading `Forall`s (with fresh metas, same as every
  // other auto-instantiation site in this checker) first, it always
  // returns `None` here, silently falling back to `Hole` field types for
  // EVERY field and losing the concrete type entirely the moment a
  // generic instance's own field value (not just a class's own method)
  // gets `infer`red as part of some OUTER expression (e.g. `xs ++ ys`
  // used as an argument to `BEq.beq`, needing the concatenation's own
  // concrete `List I64` result type to pin down `BEq`'s class param).
  let forced = instantiate_foralls(mctx, structs, scrutinee_ty);
  let inductive_atom = head_atom_of(mctx, &forced)?;
  let info = structs
    .constructors
    .get(&(inductive_atom, case_name.clone()))?;
  let (_, concrete_args) = spine_of(&forced);
  if concrete_args.len() != info.param_atoms.len() {
    return None;
  }
  Some(
    info
      .fields
      .iter()
      .map(|field_ty| {
        let mut substituted = field_ty.clone();
        for (param_atom, &concrete_arg) in info.param_atoms.iter().zip(concrete_args.iter()) {
          substituted = open_with(&close(&substituted, *param_atom), concrete_arg);
        }
        substituted
      })
      .collect(),
  )
}

/// What a class method's own atom needs, to resolve a call site to a
/// concrete instance: which class it belongs to, the (single, for now —
/// see `desugar_struct_literals`'s class-method arm) class-level type
/// parameter's name (so the right `Forall` layer of the method's own
/// already-elaborated signature can be identified when instantiating it
/// with metas), and the method's own bare name (the last segment used to
/// build a concrete instance's mangled method path,
/// `instance.name().extend(method_name)` — the same convention
/// `term/module.rs`'s `resolve_class_method_instance`/`eval.rs`'s own
/// runtime dispatch already use).
#[derive(Debug, Clone)]
pub struct ClassMethodInfo {
  pub class_path: ModulePath,
  pub class_param_name: Identifier,
  pub method_name: Identifier,
  /// The class param's own declared default (`class FromListLiteral (L :
  /// Type -> Type := List) {...}`'s `List`), if any — used by
  /// `try_resolve_class_method` as a last-resort fallback when the class
  /// param is still a bare, unresolved meta after checking every spine
  /// arg (e.g. `[1, 2, 3]`, desugared to `FromListLiteral.cons`/`.empty`,
  /// checked with no surrounding annotation to pin `L` down to a concrete
  /// type any other way).
  pub default_type: Option<ModulePath>,
}

/// Every class method's atom, keyed the same way `register_inductive`
/// mints it (`global_atom(class_path.extend(method_name))`) — built once
/// per file from every loaded module's classes plus the file's own (see
/// `core_check_module::collect_known_class_methods`).
pub type KnownClassMethods = Map<Atom, ClassMethodInfo>;

/// `(class_path, concrete_type_path) -> instance_name_prefix` — e.g.
/// `(Foldable, List) -> instance-Foldable-List`, from which a concrete
/// method's mangled path is `instance_name_prefix.extend(method_name)`.
/// An instance's own mangled name (`instance-BEq-List`), plus its OWN
/// `type_constraints` (`[BEq A]` in `instance [BEq A] BEq (List A) {...}`)
/// — an instance is a def which is a value instance of the class, so a
/// still-generic instance's dictionary methods need one leading argument
/// per instance-level constraint, resolved at each call site the same way
/// D3/D4 resolve an ordinary constrained def's own dictionary parameters
/// (see `try_resolve_class_method`'s use of this).
#[derive(Debug, Clone)]
pub struct KnownInstanceInfo {
  pub prefix: ModulePath,
  pub constraints: Vec<TypeConstraint>,
}

/// Built once per file from every loaded module's `instance` declarations
/// plus the file's own (see `core_check_module::collect_known_instances`).
/// Deliberately narrower than the real `InstanceKey`/`find_instance`
/// matching (`term/module.rs`): keyed on just the instance's *first* type
/// argument's own head path, not general structural unification — covers
/// ordinary single-param classes (`Foldable`, `BEq`, `Show`, ...)
/// instantiated at a plain named type (`List`, `String`, ...), not
/// multi-param classes or instances matched via nested/constrained type
/// shapes. A documented, narrower stepping stone toward real dictionary
/// passing, not a competing design — see this module's sibling
/// `desugar_struct_literals` doc comment and
/// `plans/implementations/dictionary-passing-instance-resolution.md`.
pub type KnownInstances = Map<(ModulePath, ModulePath), KnownInstanceInfo>;

#[derive(Debug, Clone, PartialEq)]
pub enum InferError {
  Unify(UnifyError),
  UnboundVariable(Atom),
  UnknownMeta(crate::core_term::MetaId),
  /// A raw `Bound` reached `infer`/`check` directly — every caller must
  /// open a binder before recursing into its body, so this indicates a
  /// bug in the checker itself, not a user-facing type error.
  UnexpectedBound(u32),
  /// `infer` was called on a `Hole` — a hole carries no information to
  /// infer a type *from*; it must be checked against a known expected
  /// type instead (`check` handles `Hole` directly, trivially).
  CannotInferHole,
  ExpectedFunctionType(CoreTerm),
  /// `infer` was asked for the type of a term that genuinely can't be
  /// inferred without module/global metadata this increment doesn't have
  /// wired in yet (a struct literal's declared type, or a native
  /// operation's signature) — a real limitation of this phase, not a bug;
  /// see `infer`'s `Lit`/`Ntv` handling. Needs the module/`Scope` system
  /// integration the plan's Phase 3/4 (real-file parity testing) already
  /// calls for.
  CannotInfer(CoreTerm),
}

impl From<UnifyError> for InferError {
  fn from(e: UnifyError) -> Self {
    InferError::Unify(e)
  }
}

fn open_ctx(ctx: &TyCtx, atom: Atom, typ: CoreTerm) -> TyCtx {
  ctx.extend(atom, typ)
}

/// Instantiate every leading `Forall` of `typ` with a fresh metavariable
/// (`core_unify::instantiate`), stopping at the first non-`Forall` layer —
/// PLUS every leading dictionary `Pi` right after (a constrained def's
/// elaborated type is `Forall A . Pi(dict: BOrd A) . Pi(x: A) . ...`, see
/// `core_check_module.rs`'s `check_one_def_new`/D3 doc comment): a `Pi`
/// whose argument type's head atom is a known class (`is_class_atom`, not
/// an ordinary explicit parameter) is auto-instantiated with a fresh meta
/// too, exactly like a `Forall`. This is the auto-instantiation step at
/// every use of a polymorphic (or constrained) value — the direct
/// replacement for the old checker's `pi_of_forall_types_with_mult` merge
/// trick, now applied uniformly wherever a type needs to be "used" rather
/// than "checked against literally."
///
/// Doing this here means `check`/`infer`'s ordinary `App`/`expect_pi`
/// handling never has to know dictionaries exist at all — a call site
/// simply "sees" a def's constrained parameters vanish from its Pi-chain,
/// the same way it already never sees a `Forall`. Type-checking a call
/// this way alone is *not* enough on its own for the resulting term to
/// evaluate correctly though — the term itself still has no argument
/// applied at the dictionary's position; a separate pass
/// (`insert_dict_args`) rewrites the checked term afterward to actually
/// supply it, mirroring how `try_resolve_class_method`/
/// `desugar_struct_literals` already handle class-method call sites.
pub fn instantiate_foralls(
  mctx: &mut MetaContext,
  structs: &StructFields,
  typ: &CoreTerm,
) -> CoreTerm {
  let mut current = force(mctx, typ.clone()).into_stripped_ctx();
  loop {
    current = match current {
      CoreTerm::Forall {
        typ: inner_typ,
        body,
        ..
      } => {
        let instantiated = instantiate(mctx, &inner_typ, &body);
        force(mctx, instantiated).into_stripped_ctx()
      }
      CoreTerm::Pi { arg, ret, .. }
        if head_atom_of(mctx, &arg).is_some_and(|a| is_class_atom(structs, a)) =>
      {
        let m = mctx.fresh_meta(*arg);
        force(mctx, open_with(&ret, &CoreTerm::Meta(m))).into_stripped_ctx()
      }
      other => return other,
    };
  }
}

/// E7: applying an explicit argument to a term whose type is *entirely*
/// `Forall`-quantified (no `Pi` at all once every leading `Forall` is
/// peeled) — e.g. `Eq.refl : {A : Sort 1} -> {a : A} -> Eq A a a`, an
/// indexed constructor with only implicit params. `Eq.refl 1` isn't
/// ordinary function application (there's no `Pi` for `1` to fill) —
/// it's providing one of the implicit params EXPLICITLY, exactly as the
/// old checker's own `match_resolve_type`-based "the explicit argument
/// was absorbed by one of the Foralls" mechanism did (`eval/type.rs`'s
/// `type_check_with_env`'s `App` arm, `fun_vars.is_empty()` branch).
///
/// Only ever tried as a FALLBACK, after the ordinary `instantiate_foralls`
/// and `expect_pi` path already failed with `ExpectedFunctionType` — never
/// changes behavior for a normal `Pi`-typed application (the loop below
/// returns `None` the moment it hits a `Pi`, before absorbing anything).
///
/// Peels every leading `Forall` with a fresh meta (same as
/// `instantiate_foralls`, just tracking each one), then — since the
/// result isn't a `Pi` — tries each peeled meta, MOST-recently-peeled
/// first (the one "closest" to where a real argument position would be),
/// unifying `arg`'s own inferred type against that meta's declared type;
/// the first one that unifies gets bound directly to `arg` itself (not
/// just its type — `unify` handles solving a meta to an arbitrary term
/// uniformly). Returns the (now more-resolved) instantiated type with
/// that binding applied, or `None` if no peeled meta matches (a genuine
/// type error — the caller should surface the original `ExpectedFunctionType`).
fn try_absorb_into_forall(
  mctx: &mut MetaContext,
  ctx: &TyCtx,
  structs: &StructFields,
  fun_ty: &CoreTerm,
  arg: &CoreTerm,
) -> Option<CoreTerm> {
  let mut current = force(mctx, fun_ty.clone()).into_stripped_ctx();
  let mut peeled: Vec<MetaId> = Vec::new();
  loop {
    current = match current {
      CoreTerm::Forall {
        typ: inner_typ,
        body,
        ..
      } => {
        let m = mctx.fresh_meta((*inner_typ).clone());
        peeled.push(m);
        force(mctx, open_with(&body, &CoreTerm::Meta(m))).into_stripped_ctx()
      }
      CoreTerm::Pi { .. } => return None,
      _ => break,
    };
  }
  if peeled.is_empty() {
    return None;
  }
  let arg_ty = infer(mctx, ctx, structs, arg).ok()?;
  for &m in peeled.iter().rev() {
    let declared = mctx.meta_type(m)?.clone();
    if unify(mctx, &arg_ty, &declared).is_ok() && unify(mctx, &CoreTerm::Meta(m), arg).is_ok() {
      return Some(current);
    }
  }
  None
}

/// Resolve `expected` (forcing through any solved metavariable chain) to a
/// `Pi` shape, synthesizing one via fresh metavariables and binding it if
/// `expected` is itself still an unresolved metavariable — needed to check
/// a lambda against a not-yet-known type (e.g. an unannotated `let`).
///
/// Known simplification: when synthesizing from a bare metavariable, the
/// return type is modeled as a *non-dependent* fresh meta (a meta that
/// cannot itself mention the bound parameter) — a fully general "unknown
/// dependent Pi" would need a higher-order metavariable (a meta standing
/// for a function of the bound variable), which is the Miller-pattern
/// extension point the plan explicitly defers, not implemented here.
fn expect_pi(
  mctx: &mut MetaContext,
  expected: &CoreTerm,
) -> Result<(CoreTerm, CoreTerm, Multiplicity), InferError> {
  // `.into_stripped_ctx()`: this match's final arm is a wildcard
  // (`other => Err(InferError::ExpectedFunctionType(other))`), which the
  // compiler can't flag as missing a `Ctx` case — without stripping, a
  // `Ctx`-wrapped `Pi` would be spuriously reported as "not a function
  // type" instead of being recognized.
  match force(mctx, expected.clone()).into_stripped_ctx() {
    CoreTerm::Pi { arg, ret, mult, .. } => Ok((*arg, *ret, mult)),
    CoreTerm::Meta(m) => {
      let arg_meta = mctx.fresh_meta(CoreTerm::Sort { level: 1 });
      let ret_meta = mctx.fresh_meta(CoreTerm::Sort { level: 1 });
      let arg = CoreTerm::Meta(arg_meta);
      let ret = CoreTerm::Meta(ret_meta);
      let synthesized = CoreTerm::Pi {
        dbg: DebugName::Anonymous,
        arg: Box::new(arg.clone()),
        ret: Box::new(ret.clone()),
        mult: Multiplicity::Many,
      };
      unify(mctx, &CoreTerm::Meta(m), &synthesized)?;
      Ok((arg, ret, Multiplicity::Many))
    }
    // A pattern-bound variable (`Lit::Match`'s "Known simplification":
    // its real per-field type isn't tracked, so it's typed `Hole`) being
    // *applied* as a function — there's no metavariable to bind here
    // (unlike the `Meta` case above), but `Hole` is already treated as
    // "unknown, accept anything" everywhere else in this checker (see
    // `check`'s own `Hole` short-circuits), so synthesizing a fresh,
    // unconstrained Pi shape — with nothing to unify it against — is the
    // same move, just without a meta on the left to bind.
    CoreTerm::Hole => {
      let arg_meta = mctx.fresh_meta(CoreTerm::Sort { level: 1 });
      let ret_meta = mctx.fresh_meta(CoreTerm::Sort { level: 1 });
      Ok((
        CoreTerm::Meta(arg_meta),
        CoreTerm::Meta(ret_meta),
        Multiplicity::Many,
      ))
    }
    other => Err(InferError::ExpectedFunctionType(other)),
  }
}

/// Infer `term`'s type from its own structure, with no ambient
/// expectation — used at the leaves/heads of an application spine
/// (`Free`/`Meta` occurrences, `App`'s function position, `Sort`,
/// `Forall`/`Pi` as type-formers, and `Lam` since our `CoreTerm::Lam`
/// always carries an explicit parameter type).
pub fn infer(
  mctx: &mut MetaContext,
  ctx: &TyCtx,
  structs: &StructFields,
  term: &CoreTerm,
) -> Result<CoreTerm, InferError> {
  match term {
    // Transparent: strip the location wrapper and re-dispatch on the
    // real shape. `infer`'s own signature has no location to attribute
    // an error to yet (that's threaded in by callers via `Ctx`'s own
    // presence further up the term, not by `infer` itself), so this is a
    // pure pass-through for now.
    CoreTerm::Ctx { term, .. } => infer(mctx, ctx, structs, term),
    CoreTerm::Bound(i) => Err(InferError::UnexpectedBound(*i)),
    CoreTerm::Hole => Err(InferError::CannotInferHole),

    CoreTerm::Free(a) => ctx.get(a).cloned().ok_or(InferError::UnboundVariable(*a)),
    CoreTerm::Meta(m) => mctx
      .meta_type(*m)
      .cloned()
      .ok_or(InferError::UnknownMeta(*m)),

    // Universe rule kept deliberately simple (no stratified/predicative
    // universe hierarchy enforcement) — matches this codebase's existing
    // pervasive single-`Type`-sort usage; not the concern this redesign
    // is about, and out of scope to overhaul here.
    CoreTerm::Sort { level } => Ok(CoreTerm::Sort { level: level + 1 }),

    CoreTerm::Forall { typ, body, .. } => {
      infer(mctx, ctx, structs, typ)?;
      let atom = Atom::fresh();
      let ctx2 = open_ctx(ctx, atom, (**typ).clone());
      let opened_body = open_with(body, &CoreTerm::Free(atom));
      infer(mctx, &ctx2, structs, &opened_body)
    }
    CoreTerm::Pi { arg, ret, .. } => {
      infer(mctx, ctx, structs, arg)?;
      let atom = Atom::fresh();
      let ctx2 = open_ctx(ctx, atom, (**arg).clone());
      let opened_ret = open_with(ret, &CoreTerm::Free(atom));
      infer(mctx, &ctx2, structs, &opened_ret)
    }

    CoreTerm::Lam {
      dbg,
      param_typ,
      body,
    } => {
      let atom = Atom::fresh();
      let ctx2 = open_ctx(ctx, atom, (**param_typ).clone());
      let opened_body = open_with(body, &CoreTerm::Free(atom));
      let body_ty = infer(mctx, &ctx2, structs, &opened_body)?;
      let ret = close(&body_ty, atom);
      Ok(CoreTerm::Pi {
        dbg: dbg.clone(),
        arg: param_typ.clone(),
        ret: Box::new(ret),
        mult: Multiplicity::Many,
      })
    }

    // `let x := value in body` desugars (see `term::lets`/`let_term`) to
    // `App(Lam{param_typ: <declared type, or Hole>, body}, value)`. When
    // unannotated, `param_typ` is `Hole` — a plain `infer` on the `Lam`
    // would trust that `Hole` as-is (nothing corrects it), and
    // `expect_pi` can't turn a `Hole` into a function type the way it can
    // a `Meta`, so applying it always failed with `ExpectedFunctionType`.
    // Handle this shape directly, the way a `let` should be inferred:
    // infer `value`'s own type and use *that* as the bound variable's
    // type when inferring `body`, rather than routing through
    // `expect_pi`/`unify` at all.
    // `.strip_ctx()` on both the function position and its param type: a
    // `Ctx`-wrapped `Lam`/`Hole` here would otherwise silently miss this
    // guard (falling through to the generic `App` arm below) and hit
    // `expect_pi`'s known `Hole`-can't-become-a-function-type failure
    // this arm exists specifically to avoid.
    CoreTerm::App { fun, arg } if matches!(fun.as_ref().strip_ctx(), CoreTerm::Lam { param_typ, .. } if matches!(param_typ.as_ref().strip_ctx(), CoreTerm::Hole)) =>
    {
      let CoreTerm::Lam { body, .. } = fun.as_ref().strip_ctx() else {
        unreachable!()
      };
      let arg_ty = infer(mctx, ctx, structs, arg)?;
      let atom = Atom::fresh();
      let ctx2 = open_ctx(ctx, atom, arg_ty);
      let opened_body = open_with(body, &CoreTerm::Free(atom));
      infer(mctx, &ctx2, structs, &opened_body)
    }

    CoreTerm::App { fun, arg } => {
      let fun_ty_raw = infer(mctx, ctx, structs, fun)?;
      let fun_ty = instantiate_foralls(mctx, structs, &fun_ty_raw);
      match expect_pi(mctx, &fun_ty) {
        Ok((arg_ty, ret_ty, _mult)) => {
          check(mctx, ctx, structs, arg, &arg_ty)?;
          Ok(open_with(&ret_ty, arg))
        }
        // E7: not an ordinary Pi-application at all — `fun`'s type may be
        // entirely `Forall`-quantified (an indexed constructor like
        // `Eq.refl`, only implicit params), with `arg` explicitly
        // providing one of those implicits instead of filling a real Pi
        // argument. See `try_absorb_into_forall`'s own doc comment.
        Err(e) => try_absorb_into_forall(mctx, ctx, structs, &fun_ty_raw, arg).ok_or(e),
      }
    }

    CoreTerm::Lit(lit) => infer_lit(mctx, ctx, structs, lit),

    // E2b: when this constructor is registered (`structs.constructors`,
    // built alongside E2's own match-pattern field types), recover its
    // type argument(s) — instead of the bare, parameter-less approximation
    // below — by instantiating its own declared params with fresh metas
    // and unifying each present arg's own inferred type against the
    // correspondingly-substituted declared field type (the mirror image
    // of `match_case_field_types`'s SUBSTITUTE-then-compare: here it's
    // INFER-then-unify, recovering the param instead of consuming it).
    // `List.cons 1 (List.cons 2 List.empty)`'s "1" pins the element-type
    // meta to `I64` this way, so `BEq.beq [1,2,3] [1,2,3]`'s own class
    // param can resolve to the concrete `List I64` — without this, EVERY
    // list literal's inferred type was just a bare `Free(List)`, with no
    // way to recover the element type from the literal itself at all.
    // Still just an approximation: a zero-arg case (`List.empty`) has
    // nothing to unify against, so its own type argument stays an
    // unresolved meta — exactly the pre-existing "bare Free" limitation,
    // just for one case fewer than before.
    CoreTerm::Con(c) => {
      let inductive_atom = mctx.intern(c.typ_name.clone());
      if let Some(info) = structs.constructors.get(&(inductive_atom, c.name.clone())) {
        let param_metas: Vec<MetaId> = info
          .param_atoms
          .iter()
          .map(|_| mctx.fresh_meta(CoreTerm::Sort { level: 1 }))
          .collect();
        for (i, arg) in c.args.iter().enumerate() {
          let Some(arg) = arg else { continue };
          let arg_ty = infer(mctx, ctx, structs, arg)?;
          if let Some(field_ty) = info.fields.get(i) {
            let mut expected_field_ty = field_ty.clone();
            for (param_atom, meta_id) in info.param_atoms.iter().zip(param_metas.iter()) {
              expected_field_ty = open_with(
                &close(&expected_field_ty, *param_atom),
                &CoreTerm::Meta(*meta_id),
              );
            }
            let _ = unify(mctx, &arg_ty, &expected_field_ty);
          }
        }
        let mut result_ty = CoreTerm::Free(inductive_atom);
        for meta_id in &param_metas {
          result_ty = CoreTerm::App {
            fun: Box::new(result_ty),
            arg: Box::new(CoreTerm::Meta(*meta_id)),
          };
        }
        return Ok(result_ty);
      }
      // Known simplification (needs the module/`Scope` system integration
      // that real-file parity testing, Phase 3/4, already calls for): an
      // unregistered constructor's actual declared (possibly
      // `Forall`-quantified) type isn't available here, so its inferred
      // type is approximated as a bare reference to its inductive type's
      // global atom, ignoring any type parameters. Each present argument
      // is still individually inferred, so ill-typed arguments are still
      // caught.
      for arg in c.args.iter().flatten() {
        infer(mctx, ctx, structs, arg)?;
      }
      Ok(CoreTerm::Free(primitive_type(
        mctx,
        &c.typ_name.to_string(),
      )))
    }

    // Mirrors the real checker's OWN native-op handling exactly (see
    // `eval/type.rs`'s `type_check_with_env`, the `Ntv` arm:
    // `Ntv { native: _ } => Ok(typed_term(term.clone(),
    // expected_type.clone()))`) — natives are opaque to the type checker
    // by design, entirely deferring to whatever type is expected at the
    // use site (there is no native-signature registry to consult, even
    // in the real checker). `Hole` here plays the same role
    // `expected_type` plays there when it's itself unknown: `unify`'s
    // `(Hole, _) | (_, Hole) => Ok(())` case means a `Hole` always
    // succeeds against whatever `check`'s fallback (`infer` +
    // `instantiate_foralls` + `unify`) compares it against, so this
    // isn't a special case elsewhere — just an honest "no information"
    // inferred type, not a guess.
    CoreTerm::Ntv(_) => Ok(CoreTerm::Hole),
  }
}

fn primitive_type(mctx: &mut MetaContext, name: &str) -> Atom {
  mctx.intern(crate::term::ModulePath::top(name))
}

fn infer_lit(
  mctx: &mut MetaContext,
  ctx: &TyCtx,
  structs: &StructFields,
  lit: &CoreLit,
) -> Result<CoreTerm, InferError> {
  match lit {
    CoreLit::Str { .. } => Ok(CoreTerm::Free(primitive_type(mctx, "String"))),
    CoreLit::Char { .. } => Ok(CoreTerm::Free(primitive_type(mctx, "Char"))),
    CoreLit::Num { suffix, .. } => Ok(CoreTerm::Free(primitive_type(mctx, suffix.type_name()))),
    CoreLit::Float { suffix, .. } => Ok(CoreTerm::Free(primitive_type(mctx, suffix.type_name()))),

    CoreLit::If { cond, then, els } => {
      let bool_ty = CoreTerm::Free(primitive_type(mctx, "Bool"));
      check(mctx, ctx, structs, cond, &bool_ty)?;
      let then_ty = infer(mctx, ctx, structs, then)?;
      let els_ty = infer(mctx, ctx, structs, els)?;
      unify(mctx, &then_ty, &els_ty)?;
      Ok(then_ty)
    }

    // An explicit `{ ... : StructType }` annotation (lowered to
    // `type_name`, see `term::Literal::StructLit`/`lower_core.rs`) makes
    // a struct literal inferable on its own, without needing an ambient
    // expected type — check its fields against `structs`' registered
    // field types (same helper `check`'s dedicated `StructLit` arm uses)
    // and return the struct's own type. With no annotation there's
    // genuinely nothing to infer *from* (field names alone don't
    // determine a unique struct — several structs can share field
    // names) — report the gap rather than guess; `check`ing a bare
    // struct literal against an already-known expected type still works
    // via `check`'s own dedicated arm below.
    CoreLit::StructLit { fields, type_name } => match type_name {
      Some(atom) => {
        check_struct_fields(mctx, ctx, structs, *atom, fields, lit)?;
        Ok(CoreTerm::Free(*atom))
      }
      None => Err(InferError::CannotInfer(CoreTerm::Lit(lit.clone()))),
    },

    // `base`'s type IS knowable (it's an ordinary variable/term), so the
    // struct-update's overall type is approximated as base's type
    // unchanged; field values are still individually inferred (to catch
    // ill-typed updates) even though they aren't checked against the
    // specific field's declared type (same missing-registry limitation
    // `StructLit` without an annotation has).
    CoreLit::StructUpdate { base, fields } => {
      let base_ty = infer(mctx, ctx, structs, base)?;
      for v in fields.values() {
        infer(mctx, ctx, structs, v)?;
      }
      Ok(base_ty)
    }

    // E2: pattern-bound variables get their real field types (via
    // `match_case_field_types`, substituting the scrutinee's own concrete
    // type arguments into the matched constructor's declared field types)
    // whenever the scrutinee's type is a registered ordinary inductive and
    // its arity matches — falling back to `Hole` (as before) whenever it
    // isn't: a struct/class field type this checker doesn't have
    // constructor metadata for, or a scrutinee whose type isn't known
    // this precisely. Still catches most real errors (e.g. branches
    // disagreeing on result type) either way.
    CoreLit::Match { scrutinee, cases } => {
      let scrutinee_ty = infer(mctx, ctx, structs, scrutinee)?;
      // Phase 0 capture happens in `desugar_struct_literals`'s own
      // `Match` arm, not here — see that function's doc comment on why:
      // it's the pass that produces the FINAL term structure (including
      // dictionary-projection `Match` nodes it injects via
      // `project_dict_field`), so its traversal order is what actually
      // needs to line up with a lowering pass's, not `check`/`infer`'s
      // (which run on the PRE-desugar term and would record resolutions
      // in the wrong relative order once desugar-injected nodes are
      // interleaved in).
      let mut common_ty: Option<CoreTerm> = None;
      for case in cases {
        let arity = case.dbgs.len() as u32;
        let (atoms, opened_value) = crate::core_unify::open_n(&case.value, 0, arity);
        let field_tys = match_case_field_types(mctx, structs, &scrutinee_ty, &case.name);
        let mut ctx2 = ctx.clone();
        for (i, atom) in atoms.iter().enumerate() {
          let field_ty = field_tys
            .as_ref()
            .and_then(|f| f.get(atoms.len() - 1 - i))
            .cloned()
            .unwrap_or(CoreTerm::Hole);
          ctx2 = ctx2.extend(*atom, field_ty);
        }
        let case_ty = infer(mctx, &ctx2, structs, &opened_value)?;
        match &common_ty {
          Some(t) => unify(mctx, t, &case_ty)?,
          None => common_ty = Some(case_ty),
        }
      }
      common_ty.ok_or_else(|| InferError::CannotInfer(CoreTerm::Lit(lit.clone())))
    }
  }
}

/// Check a struct literal's present fields against `struct_atom`'s
/// registered field types. Missing fields (e.g. ones with a default
/// value, which this simplified checker doesn't track) and extra fields
/// are not validated — see `StructFields`' doc comment; this catches the
/// common case (present fields typed correctly) without the
/// module/`Scope` access needed for full field-set validation. Errors
/// with `CannotInfer` if `struct_atom` isn't a registered struct at all
/// (an unannotated/unknown expected type reached this point, or the
/// annotation named something that isn't a struct).
fn check_struct_fields(
  mctx: &mut MetaContext,
  ctx: &TyCtx,
  structs: &StructFields,
  struct_atom: Atom,
  fields: &Map<Identifier, CoreTerm>,
  lit: &CoreLit,
) -> Result<(), InferError> {
  let field_defs = &structs
    .structs
    .get(&struct_atom)
    .ok_or_else(|| InferError::CannotInfer(CoreTerm::Lit(lit.clone())))?
    .fields;
  for (name, field_ty) in field_defs {
    if let Some(value) = fields.get(name) {
      check(mctx, ctx, structs, value, field_ty)?;
    }
  }
  Ok(())
}

/// Check `term` against `expected`. Handles `Hole` (either side) and
/// polymorphic (`Forall`-wrapped) expected types directly; falls back to
/// `infer` + `unify` (after auto-instantiating any leading `Forall`s on
/// the inferred side) for everything else — the standard bidirectional
/// split (Pierce & Turner).
pub fn check(
  mctx: &mut MetaContext,
  ctx: &TyCtx,
  structs: &StructFields,
  term: &CoreTerm,
  expected: &CoreTerm,
) -> Result<(), InferError> {
  // Keep the un-stripped `term` around for the generic fallback below: a
  // `UnifyError::Mismatch` compares TYPES (`term`'s inferred type vs.
  // `expected`), and a type is almost always synthesized/looked-up
  // (`ctx.get(atom)`, a class registry, ...) rather than parsed at this
  // position — so it essentially never carries a `Ctx` location of its
  // own, even though `term` (the actual written expression) usually
  // does. Attaching `term`'s location to a location-less `Mismatch`
  // there is what makes "type mismatch" diagnostics point at the
  // expression that's actually wrong instead of falling back to the
  // enclosing def's start line.
  let original_term = term;
  // Strip once, up front, and shadow both parameters for everything
  // else — `check` is a long chain of `if let CoreTerm::X = term`/
  // `expected` special cases (not a single top-level `match`), so
  // patching each individually is exactly the kind of "333 sites, easy
  // to miss one" situation the `Ctx` design is meant to avoid.
  // `strip_ctx` is a zero-cost reference walk (no clone), so shadowing
  // costs nothing and every check below sees the real shape regardless
  // of how many `Ctx` layers wrapped it.
  let term = term.strip_ctx();
  let expected = expected.strip_ctx();
  if matches!(term, CoreTerm::Hole) {
    return Ok(());
  }
  if matches!(expected, CoreTerm::Hole) {
    infer(mctx, ctx, structs, term)?;
    return Ok(());
  }

  // Checking against a universally-quantified expected type: open with a
  // RIGID (Free, not Meta) atom. The term must be well-typed for an
  // arbitrary instantiation of the quantified variable, not merely
  // solvable for *one* — using a metavariable here (as `infer`'s
  // auto-instantiation does for *using* a polymorphic value) would be
  // wrong in the opposite direction.
  if let CoreTerm::Forall { typ, body, .. } = expected {
    let atom = Atom::fresh();
    let ctx2 = open_ctx(ctx, atom, (**typ).clone());
    let opened_expected = open_with(body, &CoreTerm::Free(atom));
    return check(mctx, &ctx2, structs, term, &opened_expected);
  }

  if let CoreTerm::Lam {
    param_typ, body, ..
  } = term
  {
    let (exp_arg, exp_ret, _mult) = expect_pi(mctx, expected)?;
    unify(mctx, param_typ, &exp_arg)?;
    let atom = Atom::fresh();
    let ctx2 = open_ctx(ctx, atom, exp_arg);
    let opened_body = open_with(body, &CoreTerm::Free(atom));
    let opened_ret = open_with(&exp_ret, &CoreTerm::Free(atom));
    return check(mctx, &ctx2, structs, &opened_body, &opened_ret);
  }

  // `let x := value in body` desugars to `App(Lam{param_typ, body},
  // value)` (see `term::lets`/`let_term`, and the identical comment on
  // `infer`'s own let-desugaring arm above). `check` had NO special
  // handling for `App` at all before this — the generic fallback below
  // would `infer` the whole `App` (which, per `infer`'s own `Lam` arm,
  // always INFERS the body's type from scratch) and only `unify` against
  // `expected` afterward, so `expected` never reaches anything inside
  // `body` that itself needs an expected type to be checkable at all
  // (the motivating case, once again: an unannotated struct literal as a
  // `let`'s final expression). Handle it directly: check/infer `value`
  // against/from `param_typ` as appropriate, then CHECK `body` against
  // `expected` — not infer it. This subsumes both the annotated-`let`
  // and unannotated-`let` cases (unlike `infer`'s arm above, which only
  // needed to handle the unannotated/`Hole` case, since infer-mode's
  // generic `App` arm already handles a known `param_typ` correctly).
  if let CoreTerm::App { fun, arg } = term
    && let CoreTerm::Lam {
      param_typ, body, ..
    } = fun.as_ref().strip_ctx()
  {
    let arg_ty = if matches!(param_typ.as_ref().strip_ctx(), CoreTerm::Hole) {
      infer(mctx, ctx, structs, arg)?
    } else {
      check(mctx, ctx, structs, arg, param_typ)?;
      (**param_typ).clone()
    };
    let atom = Atom::fresh();
    let ctx2 = open_ctx(ctx, atom, arg_ty);
    let opened_body = open_with(body, &CoreTerm::Free(atom));
    return check(mctx, &ctx2, structs, &opened_body, expected);
  }

  // `if`/`match` need to push `expected` DOWN into their branches/cases
  // rather than `infer` each one and `unify` afterward (the generic
  // fallback below) — otherwise a branch that itself needs an expected
  // type to be checkable at all (the motivating case: an unannotated
  // struct literal, `CannotInfer` in `infer` mode but perfectly checkable
  // once `expected` reaches it) never gets one, even though the
  // surrounding `if`/`match` DOES already know what type the whole
  // expression must have. This mirrors `Lam`'s special-casing just above
  // — both are "this shape needs `expected` threaded inward, not used
  // only after the fact."
  if let CoreTerm::Lit(CoreLit::If { cond, then, els }) = term {
    let bool_ty = CoreTerm::Free(primitive_type(mctx, "Bool"));
    check(mctx, ctx, structs, cond, &bool_ty)?;
    check(mctx, ctx, structs, then, expected)?;
    check(mctx, ctx, structs, els, expected)?;
    return Ok(());
  }

  if let CoreTerm::Lit(CoreLit::Match { scrutinee, cases }) = term {
    let scrutinee_ty = infer(mctx, ctx, structs, scrutinee)?;
    // Phase 0 capture happens in `desugar_struct_literals`'s own `Match`
    // arm, not here — see `infer`'s own `Match` arm for the rationale.
    for case in cases {
      let arity = case.dbgs.len() as u32;
      let (atoms, opened_value) = crate::core_unify::open_n(&case.value, 0, arity);
      // E2: see `infer`'s own `Match` arm for the full rationale — same
      // real-field-types-instead-of-`Hole` substitution here too.
      let field_tys = match_case_field_types(mctx, structs, &scrutinee_ty, &case.name);
      let mut ctx2 = ctx.clone();
      for (i, atom) in atoms.iter().enumerate() {
        let field_ty = field_tys
          .as_ref()
          .and_then(|f| f.get(atoms.len() - 1 - i))
          .cloned()
          .unwrap_or(CoreTerm::Hole);
        ctx2 = ctx2.extend(*atom, field_ty);
      }
      check(mctx, &ctx2, structs, &opened_value, expected)?;
    }
    return Ok(());
  }

  // A struct literal with NO explicit `: StructType` annotation (an
  // annotated one is already fully handled by `infer_lit`'s `StructLit`
  // arm, reached via the fallback below) resolves its struct name from
  // `expected` instead — the same "read the struct name off the expected
  // type" approach the real checker (`eval/type.rs`'s `Lit`/`StructLit`
  // arm) uses, and the whole reason this is a dedicated `check`-only
  // arm rather than something `infer` could ever handle unaided.
  if let CoreTerm::Lit(CoreLit::StructLit {
    fields,
    type_name: None,
  }) = term.strip_ctx()
    && let CoreTerm::Free(atom) = force(mctx, expected.clone()).into_stripped_ctx()
  {
    return check_struct_fields(
      mctx,
      ctx,
      structs,
      atom,
      fields,
      &CoreLit::StructLit {
        fields: fields.clone(),
        type_name: None,
      },
    );
  }

  // A generic application (`fun` not itself a `Lam` — that shape is
  // handled above) whose `fun` is still polymorphic, e.g. calling a
  // generic constructor like `ok : {E A} -> A -> Result E A` with the
  // caller already knowing the desired result type. The plain fallback
  // below would `infer(App)`, which checks `arg` against `fun`'s
  // still-unresolved argument type (a bare `Meta`, since nothing has
  // pinned `A` down yet) BEFORE ever consulting `expected` — so an
  // argument that itself needs a known expected type to be checkable
  // (once again, the recurring case: an unannotated struct literal, e.g.
  // `ok ({ term := ..., typ := ... })` where `expected = Result E
  // TypedTerm` already determines `A = TypedTerm`) fails even though the
  // caller's `expected` would have resolved it immediately. Try
  // unifying the *return* type against `expected` first — this can only
  // pin down `fun`'s own leading metavariables (`A`/`E` here), it cannot
  // spuriously succeed by "guessing" `arg`'s value, since `arg` hasn't
  // been substituted into `ret_ty` yet (any `Bound(0)` in `ret_ty` from a
  // genuinely dependent Pi stays an inert index, never unified against
  // `arg` itself) — best-effort and silently ignored on failure (e.g. a
  // genuinely dependent Pi, where this doesn't apply) since the ordinary
  // `check(arg, arg_ty)` below plus the final `unify` still catch any
  // real mismatch on their own, exactly as the fallback already would.
  if let CoreTerm::App { fun, arg } = term {
    let fun_ty_raw = infer(mctx, ctx, structs, fun)?;
    let fun_ty = instantiate_foralls(mctx, structs, &fun_ty_raw);
    let (arg_ty, ret_ty, _mult) = match expect_pi(mctx, &fun_ty) {
      Ok(triple) => triple,
      // E7: see `try_absorb_into_forall`'s own doc comment — `arg` may be
      // explicitly providing one of `fun`'s own implicit params (e.g.
      // `Eq.refl 1`), not filling a real Pi argument at all.
      Err(e) => {
        let result_ty = try_absorb_into_forall(mctx, ctx, structs, &fun_ty_raw, arg).ok_or(e)?;
        unify(mctx, &result_ty, expected)?;
        return Ok(());
      }
    };
    let _ = unify(mctx, &ret_ty, expected);
    check(mctx, ctx, structs, arg, &arg_ty)?;
    let final_ty = open_with(&ret_ty, arg);
    unify(mctx, &final_ty, expected)?;
    return Ok(());
  }

  let inferred = infer(mctx, ctx, structs, term)?;
  let inferred = instantiate_foralls(mctx, structs, &inferred);
  unify(mctx, &inferred, expected)
    .map_err(|e| attach_location(InferError::Unify(e), original_term))?;
  Ok(())
}

/// If `e` is a `Mismatch`/`UnsupportedPattern` whose sides have no
/// location of their own (the common case — see `check`'s generic
/// fallback, which is this function's only caller), attach `term`'s own
/// location (the actual written expression `check` was called on) to its
/// `left` side, so the eventual `Diagnostic` points at the expression
/// that's wrong instead of falling back to the enclosing def's start
/// line. A no-op if `term` itself has no location, or if the error
/// already does (e.g. a nested unify failure inside `left`/`right`'s own
/// structure that already found a more specific position).
fn attach_location(e: InferError, term: &CoreTerm) -> InferError {
  let Some(loc) = term.strip_ctx_loc().1 else {
    return e;
  };
  let wrap = |t: CoreTerm| -> CoreTerm {
    if t.strip_ctx_loc().1.is_some() {
      t
    } else {
      CoreTerm::Ctx {
        loc: loc.clone(),
        term: Box::new(t),
      }
    }
  };
  match e {
    InferError::Unify(UnifyError::Mismatch { left, right }) => {
      InferError::Unify(UnifyError::Mismatch {
        left: wrap(left),
        right,
      })
    }
    InferError::Unify(UnifyError::UnsupportedPattern { left, right }) => {
      InferError::Unify(UnifyError::UnsupportedPattern {
        left: wrap(left),
        right,
      })
    }
    other => other,
  }
}

/// Peel `App(App(App(head, a0), a1), a2)` into `(head, [a0, a1, a2])` —
/// application order, outermost `App`'s `arg` last.
fn spine_of(term: &CoreTerm) -> (&CoreTerm, Vec<&CoreTerm>) {
  let mut args = Vec::new();
  let mut current = term.strip_ctx();
  while let CoreTerm::App { fun, arg } = current {
    args.push(arg.as_ref());
    current = fun.as_ref().strip_ctx();
  }
  args.reverse();
  (current, args)
}

/// Force `term` and extract the **head** atom of whatever it resolved to —
/// a bare `Free(atom)` directly, or (unlike a plain `let CoreTerm::Free(a)
/// = force(...) else { ... }` match) the head of an **applied** type like
/// `List I64` (`App(Free(List), Free(I64))`), walking down `fun` to its
/// own `Free`. A class's own type parameter unifies against the *whole*
/// concrete type at a call site (e.g. `BEq A` used at `List I64` binds
/// `A := List I64`, not just `List`) — so resolving `A` to a concrete
/// instance needs the type's own *head* (`List`), the same way
/// `core_check_module.rs`'s `term_head_path` already extracts a head from
/// an instance's own declared type argument on the registration side.
/// Returns `None` if `term` doesn't resolve to a `Free`/`App`-of-`Free`
/// shape at all (still a `Meta`, a `Pi`, etc.).
pub(crate) fn head_atom_of(mctx: &mut MetaContext, term: &CoreTerm) -> Option<Atom> {
  match force(mctx, term.clone()).into_stripped_ctx() {
    CoreTerm::Free(atom) => Some(atom),
    CoreTerm::App { fun, .. } => head_atom_of(mctx, &fun),
    _ => None,
  }
}

/// Like `instantiate_foralls`, but also returns which fresh `MetaId` each
/// *named* `Forall` layer got instantiated with — needed to later ask
/// "what did the class's own declared type parameter resolve to?" by
/// name, not just get back an opaque instantiated type with no way to
/// tell which meta was which.
fn instantiate_foralls_tracked(
  mctx: &mut MetaContext,
  typ: &CoreTerm,
) -> (CoreTerm, Map<Identifier, MetaId>) {
  let mut named = Map::new();
  let mut current = force(mctx, typ.clone()).into_stripped_ctx();
  while let CoreTerm::Forall {
    dbg,
    typ: inner_typ,
    body,
  } = current
  {
    let m = mctx.fresh_meta((*inner_typ).clone());
    if let DebugName::Named(name) = &dbg {
      named.insert(name.clone(), m);
    }
    current = force(mctx, open_with(&body, &CoreTerm::Meta(m))).into_stripped_ctx();
  }
  (current, named)
}

/// Attempt to resolve a class-method call site (`head`'s spine,
/// `spine_args` in application order) to a concrete instance — the
/// `CoreTerm`-level analogue of the OLD checker's own
/// `Scope::resolve_class_method_with_constraints`
/// (`term/module.rs`), minus its full `InstanceKey` structural matching
/// (see `KnownInstances`'s doc comment for the narrower scope this
/// covers). Manually instantiates the method's own (already-elaborated)
/// `Forall`-wrapped signature with fresh metas (tracking which meta
/// belongs to the class's own declared type parameter via
/// `instantiate_foralls_tracked`), then `check`s each spine argument
/// against its corresponding `Pi`-arg type in turn — binding metas,
/// including the class-param one, exactly as real application checking
/// would (this is genuinely redundant work — `check_one_def_new` already
/// checked this whole term once — but the metas that binding produced
/// were never persisted anywhere this pass can read, so redoing it is
/// the only way to recover which concrete type the call resolved to).
/// Once every argument's consumed, reads back what the class-param meta
/// resolved to and looks up the matching instance.
///
/// After the last spine argument is consumed, if the class-param meta is
/// STILL unbound, this also tries unifying whatever's left of the
/// method's own (possibly further-instantiated) type against `expected`
/// — needed for a class method with NO explicit parameters at all (e.g.
/// `Map.empty : M K V`, a bare value, not a function) where the
/// constraint is only ever determined by the ambient expected type (a
/// `let x : HashMap I64 String := Map.empty in ...`'s own annotation),
/// never by any argument.
///
/// Returns `None` (leaving the call site unresolved, exactly as if this
/// pass didn't exist) whenever: fewer arguments are applied here than
/// the method's own arity (nothing to read the class param off yet —
/// `eval.rs`'s own runtime dispatch may still resolve it once more
/// arguments are supplied, or it's genuinely a still-polymorphic use
/// needing a real runtime dictionary, out of scope here); the class-param
/// meta stays unbound even after that (same reason); or `known_instances`
/// has no matching entry (no known instance for the concrete type, or its
/// narrower single-arg-head matching didn't cover this instance's own
/// shape).
#[allow(clippy::too_many_arguments)]
fn try_resolve_class_method(
  mctx: &mut MetaContext,
  ctx: &TyCtx,
  structs: &StructFields,
  atom_paths: &mut Map<Atom, ModulePath>,
  known_class_methods: &KnownClassMethods,
  known_instances: &KnownInstances,
  dict_scope: &DictScope,
  info: &ClassMethodInfo,
  method_typ: &CoreTerm,
  spine_args: &[&CoreTerm],
  expected: Option<&CoreTerm>,
) -> Option<CoreTerm> {
  // Recorded before ANY of this call's own processing -- the position
  // this call's own captures (both directly-captured non-speculative
  // args and the redone-speculative-prefix splice below) belong
  // relative to, regardless of how much a preceding SIBLING call (e.g.
  // another class-method call earlier in the same `let` chain) already
  // added to the very same live queue. See `splice_match_resolutions`'s
  // own doc comment for the bug this fixes.
  let queue_len_at_entry = mctx.match_resolutions_len();
  let (mut residual, named_metas) = instantiate_foralls_tracked(mctx, method_typ);
  let class_meta = *named_metas.get(&info.class_param_name)?;
  // Peek at the method's final return type (peeling exactly `spine_args.len()`
  // Pi layers with placeholder metas, NOT the real args — class methods'
  // types are non-dependent on their term arguments, only on the type-level
  // metas already fixed above, so this is safe) and unify it against
  // `expected` (when known) BEFORE processing any args below. This mirrors
  // ordinary bidirectional checking pushing an expected type in from the
  // return type first: for `op_table : List OpEntry := [e1, ..., en]`,
  // `expected` (`List OpEntry`) pins `class_meta` (`FromListLiteral`'s `L`)
  // to `List` immediately, so EVERY arg below sees an already-resolved
  // `class_meta` and the "was it unresolved when this arg was desugared"
  // check further down correctly finds nothing left to redo. Without this,
  // `class_meta` would only ever get pinned from `expected` AFTER the loop
  // (see below) — always "too late" from every arg's own point of view —
  // forcing a full, unconditional re-desugar of every arg regardless of
  // whether anything actually changed (the O(2^n) list-literal blowup this
  // function's `arg_ds` cache exists to avoid).
  if let Some(expected) = expected {
    let mut peek = residual.clone().into_stripped_ctx();
    for _ in spine_args {
      let CoreTerm::Pi { ret, .. } = peek else {
        break;
      };
      let placeholder = mctx.fresh_meta(CoreTerm::Hole);
      peek = force(mctx, open_with(&ret, &CoreTerm::Meta(placeholder))).into_stripped_ctx();
    }
    let _ = unify(mctx, &peek, expected);
  }
  let mut arg_tys: Vec<CoreTerm> = Vec::with_capacity(spine_args.len());
  let mut arg_ds: Vec<CoreTerm> = Vec::with_capacity(spine_args.len());
  // Indices of args processed while `class_meta` was still unresolved —
  // desugared below with capture SUPPRESSED (a dry run, for type
  // information only; see the loop) and redone for real, in order,
  // once `class_meta` is as resolved as it'll ever be (right after this
  // loop). Always a PREFIX of `0..spine_args.len()`: unification only
  // ever moves a meta from unresolved to resolved, never back, so once
  // some arg's own `check` pins `class_meta`, every later arg sees it
  // already resolved — never captured normally.
  //
  // Why a dry run at all, rather than just doing every arg for real
  // once and living with a possibly-stale result: for `Default.default
  // == 0i64` (`BEq.beq Default.default 0i64`), `class_meta` (`BEq`'s
  // `A`) is still bare while `Default.default` (arg 1) is desugared —
  // nothing pins it down until `0i64` (arg 2) is checked a moment
  // later. Only arg 2's processing gives `class_meta` a concrete value;
  // re-desugaring arg 1 with that now-known type is what lets
  // `Default.default` resolve to `Default I64`, not a bare, unresolved
  // dictionary reference. Suppressing capture during the dry run (via
  // `without_match_capture`) rather than just letting it capture
  // normally matters because a dry-run arg can itself be a nested
  // class-method call (a list literal's own `cons`/`cons`/.../`empty`
  // chain, or — the concrete bug this fixes — `fn acc x => acc + x`'s
  // own `HAdd.add`) whose resolution would otherwise land in the queue
  // at the WRONG point (and, if the redo below re-captured it too, a
  // second time) — see `speculative`'s own redo-and-splice, right after
  // this loop, for where the REAL capture happens instead.
  let mut speculative: Vec<usize> = Vec::new();
  for (i, &arg) in spine_args.iter().enumerate() {
    let CoreTerm::Pi {
      arg: arg_ty, ret, ..
    } = residual.into_stripped_ctx()
    else {
      return None;
    };
    let class_meta_unresolved_before = head_atom_of(mctx, &CoreTerm::Meta(class_meta)).is_none();
    // Two-tier: try the cheap path first (just `check` the RAW,
    // undesugared `arg` — sufficient to pin `class_meta` whenever `arg`
    // is already a concretely-typed value with no nested class-method
    // call of its own needing resolution, the overwhelmingly common case
    // for an ordinary chain like `Show.show`/`Append.append`). Only fall
    // back to the full recursive `desugar_struct_literals` dry run when
    // that's NOT enough — this is what avoids the O(2^depth) blowup a
    // previous version of this function had (recursively, redundantly
    // re-desugaring every nested class-method call inside every
    // speculative argument, purely to throw the result away): `check`
    // alone costs O(|arg|) and, critically, never re-enters this whole
    // class-method-resolution machinery the way a full desugar does.
    //
    // The fallback exists because `check` (which never resolves class
    // methods, only `desugar_struct_literals` does) can leave `arg`'s
    // inferred type built from a still-bare, never-defaulted meta when
    // `arg` itself contains a nested, still-unresolved class-method call
    // — e.g. `[1, 2, 3]` parses straight to `FromListLiteral.cons`/
    // `.empty` (`parser.rs`'s list-literal grammar), and `FromListLiteral`'s
    // own type param (`L`, defaulting to `List`) only gets defaulted via
    // `try_resolve_class_method`'s own "last resort" step below, which
    // only runs when `desugar_struct_literals` actually visits that call.
    // Skipping the fallback entirely for such cases would leave `class_meta`
    // bound to a type containing that live, unresolved nested meta instead
    // of a concrete one (`List I64` rather than `Meta(L) I64`) — the exact
    // bug behind `BEq.beq [1, 2, 3] [1, 2, 3]` needing this fallback path
    // to reach the real `List` instance rather than the evaluator's
    // runtime dispatch fallback.
    let arg_d = if class_meta_unresolved_before {
      speculative.push(i);
      check(mctx, ctx, structs, arg, &arg_ty).ok()?;
      if head_atom_of(mctx, &CoreTerm::Meta(class_meta)).is_none() {
        // Cheap path didn't pin `class_meta` — fall back to the full
        // recursive desugar (captures still suppressed: this is still a
        // dry run whose VALUE gets thrown away, overwritten by the real
        // redo below once `class_meta` is resolved).
        mctx.without_match_capture(|mctx| {
          desugar_struct_literals(
            mctx,
            ctx,
            structs,
            atom_paths,
            known_class_methods,
            known_instances,
            dict_scope,
            arg,
            Some(&arg_ty),
          )
        })
      } else {
        // Inert placeholder — unconditionally overwritten by the redo
        // below for every index in `speculative`; only used in the
        // meantime for `open_with(&ret, &arg_d)` just below, which is
        // safe since no class method actually declared in this codebase
        // has a return type depending on an earlier argument's runtime
        // VALUE, only on type-level metas (see this function's own doc
        // comment).
        (*arg).clone()
      }
    } else {
      let arg_d = desugar_struct_literals(
        mctx,
        ctx,
        structs,
        atom_paths,
        known_class_methods,
        known_instances,
        dict_scope,
        arg,
        Some(&arg_ty),
      );
      check(mctx, ctx, structs, &arg_d, &arg_ty).ok()?;
      arg_d
    };
    residual = force(mctx, open_with(&ret, &arg_d)).into_stripped_ctx();
    arg_tys.push(*arg_ty);
    arg_ds.push(arg_d);
  }
  if head_atom_of(mctx, &CoreTerm::Meta(class_meta)).is_none()
    && let Some(expected) = expected
  {
    let _ = unify(mctx, &residual, expected);
  }
  // Last resort: the class param is still a bare, unresolved meta (no
  // argument's own inferred type pinned it down, and no surrounding
  // `expected` did either — the common shape for `[1, 2, 3]`, desugared
  // to `FromListLiteral.cons`/`.empty` with nothing around it annotating
  // which `L` to use) — fall back to the class's own declared default
  // (`class FromListLiteral (L : Type -> Type := List)`), exactly as an
  // unspecified generic parameter with a default is meant to resolve.
  if head_atom_of(mctx, &CoreTerm::Meta(class_meta)).is_none()
    && let Some(default_path) = info.default_type.clone()
  {
    let default_atom = mctx.intern(default_path);
    let _ = unify(
      mctx,
      &CoreTerm::Meta(class_meta),
      &CoreTerm::Free(default_atom),
    );
  }
  // Redo every speculatively-desugared (dry-run, capture-suppressed) arg
  // for real, now that `class_meta` is as resolved as it'll ever be —
  // capturing into a scratch buffer rather than the live queue directly,
  // since these captures belong BEFORE this call's own dictionary
  // projection (captured below, via `project_dict_field`) and before
  // any later, already-resolved sibling arg's own (already correctly
  // positioned) captures — appending them to the live queue here, after
  // the fact, would put them in exactly the wrong place. Spliced at
  // `queue_len_at_entry`, not the queue's front — a PRECEDING sibling
  // class-method call (e.g. an earlier `let`-bound call in the same
  // chain) may already have added its own, correctly-positioned entries
  // before this call ever started; splicing at 0 would incorrectly shove
  // this call's own entries ahead of that unrelated, already-settled
  // work. See `splice_match_resolutions`'s own doc comment.
  if !speculative.is_empty() {
    let (redone, buffer) = mctx.capture_match_resolutions_into_buffer(|mctx| {
      speculative
        .iter()
        .map(|&i| {
          desugar_struct_literals(
            mctx,
            ctx,
            structs,
            atom_paths,
            known_class_methods,
            known_instances,
            dict_scope,
            spine_args[i],
            Some(&arg_tys[i]),
          )
        })
        .collect::<Vec<_>>()
    });
    for (&i, arg_d) in speculative.iter().zip(redone) {
      arg_ds[i] = arg_d;
    }
    mctx.splice_match_resolutions(queue_len_at_entry, buffer);
  }
  let forced_class_meta = force(mctx, CoreTerm::Meta(class_meta)).into_stripped_ctx();
  // A class-method reference no longer gets rewritten to a different
  // global (`instance-BEq-List.beq`, resolved through the OLD, entirely
  // separate `Module::get_def_refs` per-instance-method registration,
  // which never runs through this checker's own `Con`-based dictionaries
  // at all) — it resolves via ordinary struct-field projection on a
  // dictionary `Con` instead: either one already bound in scope (D5 —
  // ONLY when the class param resolved to a still-abstract, BARE type
  // variable, e.g. `BEq A` inside `BEq (List A)`'s own `beq` — a bare
  // `Free` never has instance-level constraints of its own to thread, so
  // `dict_scope`'s entry is used as-is), or one resolved to a concrete
  // instance (below — when the class param resolved to a CONCRETE or
  // APPLIED type, e.g. `BEq (List I64)` at a monomorphic call site, or
  // `BEq (List A)` recursing into itself from inside its own `beq`, where
  // `A` is bare but the class param here is `List A`, not `A` itself —
  // critically NOT the same shape as `BEq A` even though both mention
  // "A", so it must NOT reuse `beq`'s own bound dictionary — that bug is
  // exactly why this distinguishes "class param is a bare Free" from
  // "class param is anything else" instead of keying purely on class
  // name the way an earlier, incorrect version of this function did).
  let mut result = if let CoreTerm::Free(_) = forced_class_meta
    && let Some(&dict_atom) = dict_scope.get(&info.class_path)
  {
    project_dict_field(
      mctx,
      structs,
      &info.class_path,
      &info.method_name,
      dict_atom,
    )?
  } else {
    let concrete_atom = head_atom_of(mctx, &forced_class_meta)?;
    let concrete_path = atom_paths
      .get(&concrete_atom)
      .or_else(|| structs.inductive_paths.get(&concrete_atom))?
      .clone();
    let instance_info = known_instances.get(&(info.class_path.clone(), concrete_path))?;
    let instance_atom = mctx.intern(instance_info.prefix.clone());
    let dict_args = resolve_instance_dict_args(
      mctx,
      structs,
      atom_paths,
      known_instances,
      dict_scope,
      &instance_info.constraints,
      &forced_class_meta,
      &named_metas,
      class_meta,
    )?;
    let mut result = project_dict_field(
      mctx,
      structs,
      &info.class_path,
      &info.method_name,
      instance_atom,
    )?;
    for dict_arg in dict_args {
      result = CoreTerm::App {
        fun: Box::new(result),
        arg: Box::new(dict_arg),
      };
    }
    result
  };
  // Every arg's final, correctly-captured desugared form is already
  // settled (either captured directly in the main loop, or redone and
  // spliced in above) — just apply them, in order.
  for arg_d in arg_ds {
    result = CoreTerm::App {
      fun: Box::new(result),
      arg: Box::new(arg_d),
    };
  }
  Some(result)
}

/// D4: call-site dictionary auto-insertion — the `CoreTerm`-level analogue
/// of `try_resolve_class_method`, but for an ordinary constrained def
/// (`def foo [BOrd A] (x y z : A) : Bool := ...`) rather than a class
/// method reference. `instantiate_foralls` (this file) already knows how
/// to auto-skip `head_atom`'s leading dictionary `Pi`(s) — inserted by
/// `core_check_module.rs`'s D3 elaboration — with fresh metas so
/// type-checking succeeds without the caller supplying them; this
/// function does the OTHER half: recover which concrete instance each
/// skipped dict meta should have resolved to (redoing the instantiate+
/// check-args work, same justification as `try_resolve_class_method` —
/// the metas `check` bound while originally checking this call site were
/// never persisted anywhere this pass can read back) and REWRITE the
/// term, inserting a real `Free(instance_atom)` argument at each
/// dictionary's position — `foo x y z` becomes `foo dict x y z`, an
/// ordinary curried application the evaluator can run as-is; nothing
/// downstream needs to know dictionaries are a distinct kind of
/// parameter.
///
/// Returns `None` (leaving the call site unresolved, exactly as if this
/// pass didn't exist) whenever: `head_atom`'s own type has no leading
/// dictionary `Pi` at all (an ordinary, unconstrained def — the common
/// case); fewer arguments are applied here than needed to pin down a
/// dictionary's own class-param meta (a partial/point-free use — the
/// evaluator's own runtime dispatch has no fallback for this case either,
/// unlike a class method's OLD-checker runtime dispatch, so this is a
/// real, documented gap, not a shortcut); or `known_instances` has no
/// matching entry for the concrete type this call resolved to.
#[allow(clippy::too_many_arguments)]
fn try_insert_dict_args(
  mctx: &mut MetaContext,
  ctx: &TyCtx,
  structs: &StructFields,
  atom_paths: &mut Map<Atom, ModulePath>,
  known_class_methods: &KnownClassMethods,
  known_instances: &KnownInstances,
  dict_scope: &DictScope,
  head_atom: Atom,
  head_typ: &CoreTerm,
  spine_args: &[&CoreTerm],
) -> Option<CoreTerm> {
  let mut residual = instantiate_foralls_only(mctx, head_typ);
  let mut dict_slots: Vec<(ModulePath, CoreTerm)> = Vec::new();
  loop {
    let CoreTerm::Pi { arg, ret, .. } = residual.clone() else {
      break;
    };
    let Some(class_atom) = head_atom_of(mctx, &arg) else {
      break;
    };
    if !is_class_atom(structs, class_atom) {
      break;
    }
    let class_path = atom_paths.get(&class_atom)?.clone();
    dict_slots.push((class_path, *arg.clone()));
    let placeholder = mctx.fresh_meta(*arg);
    residual = force(mctx, open_with(&ret, &CoreTerm::Meta(placeholder))).into_stripped_ctx();
  }
  if dict_slots.is_empty() {
    return None;
  }
  let mut arg_tys: Vec<CoreTerm> = Vec::with_capacity(spine_args.len());
  for &arg in spine_args {
    let CoreTerm::Pi {
      arg: arg_ty, ret, ..
    } = residual.into_stripped_ctx()
    else {
      return None;
    };
    check(mctx, ctx, structs, arg, &arg_ty).ok()?;
    residual = force(mctx, open_with(&ret, arg)).into_stripped_ctx();
    arg_tys.push(*arg_ty);
  }
  let mut result = CoreTerm::Free(head_atom);
  for (class_path, dict_arg_typ) in &dict_slots {
    // D5: a still-polymorphic caller (itself constrained on this SAME
    // class) already has its own bound dictionary in scope — thread that
    // through unchanged rather than trying (and failing) to resolve a
    // concrete instance for a type that's still abstract here. Only when
    // nothing's bound does this fall back to D4's own "resolve the now-
    // concrete type to a registered instance" path.
    let dict_atom = match dict_scope.get(class_path) {
      Some(&bound) => bound,
      None => {
        let concrete_atom = head_atom_of(mctx, dict_arg_typ)?;
        let concrete_path = atom_paths
          .get(&concrete_atom)
          .or_else(|| structs.inductive_paths.get(&concrete_atom))?
          .clone();
        let instance_info = known_instances.get(&(class_path.clone(), concrete_path))?;
        mctx.intern(instance_info.prefix.clone())
      }
    };
    result = CoreTerm::App {
      fun: Box::new(result),
      arg: Box::new(CoreTerm::Free(dict_atom)),
    };
  }
  for (&arg, arg_ty) in spine_args.iter().zip(arg_tys.iter()) {
    let arg_d = desugar_struct_literals(
      mctx,
      ctx,
      structs,
      atom_paths,
      known_class_methods,
      known_instances,
      dict_scope,
      arg,
      Some(arg_ty),
    );
    result = CoreTerm::App {
      fun: Box::new(result),
      arg: Box::new(arg_d),
    };
  }
  Some(result)
}

/// Like `instantiate_foralls`, but stops at the FIRST leading dictionary
/// `Pi` instead of skipping past it too — `try_insert_dict_args` needs to
/// inspect those `Pi`s itself (to know how many dictionaries to resolve
/// and in which order), not have them silently consumed the way an
/// ordinary call site wants.
fn instantiate_foralls_only(mctx: &mut MetaContext, typ: &CoreTerm) -> CoreTerm {
  let mut current = force(mctx, typ.clone()).into_stripped_ctx();
  while let CoreTerm::Forall {
    typ: inner_typ,
    body,
    ..
  } = current
  {
    let instantiated = instantiate(mctx, &inner_typ, &body);
    current = force(mctx, instantiated).into_stripped_ctx();
  }
  current
}

// ---------------------------------------------------------------------------
// D5 — bound-dictionary-parameter resolution for still-polymorphic bodies
// ---------------------------------------------------------------------------

/// Which dictionary atom is currently bound, for each class, while
/// `desugar_struct_literals` is recursing through a constrained def's OWN
/// body — an explicit, immutable map extended (never mutated in place) by
/// `desugar_struct_literals`'s own `Lam` arm each time it opens a
/// dictionary parameter, and threaded through every recursive call from
/// there exactly like `ctx`/`atom_paths` already are. A per-def-body-scoped
/// parameter rather than a shared/global table specifically so two
/// unrelated defs in the same module — one constrained on a class, one not
/// — can never see each other's dictionaries: unlike `ctx` (which keeps
/// every atom the whole module has ever registered, since nothing removes
/// an entry once a def's own checking finishes), a `DictScope` starts
/// empty at each def's own top-level `desugar_struct_literals` call and
/// only ever grows by cloning-and-inserting on the way IN to a dictionary
/// `Lam`'s own body — never by mutating a shared instance — so it can't
/// leak entries between sibling defs the way a mutable/global table would.
pub type DictScope = Map<ModulePath, Atom>;

/// Resolve a class-method reference (`BOrd.lt`) to a field projection on
/// whichever dictionary is currently bound in `dict_scope` for its class —
/// the real "still-polymorphic body" case D3/D4 alone can't handle
/// (there's no concrete instance to look up: the constrained type variable
/// is still abstract here, e.g. inside `def foo {A} [BOrd A] ... := ...
/// BOrd.lt x y ...`). `structs`' field order (declaration order, same order
/// D2 builds an instance's `Con` in) determines which `Bound` index the
/// projection reads — see `lower_core.rs`'s `Literal::Match` lowering
/// (`ctx.push`ing each pattern var in order means the LAST-declared field
/// ends up `Bound(0)`, the innermost/most-recently-opened) for why it's
/// `fields.len() - 1 - idx`, not `idx`, that the projection reads. Returns
/// `None` (letting the caller fall back to `try_resolve_class_method`'s
/// global instance lookup) whenever no dictionary for this class is bound
/// in `dict_scope` at all — the common, fully-monomorphic case.
fn try_resolve_via_bound_dict(
  mctx: &mut MetaContext,
  structs: &StructFields,
  dict_scope: &DictScope,
  info: &ClassMethodInfo,
) -> Option<CoreTerm> {
  let dict_atom = *dict_scope.get(&info.class_path)?;
  project_dict_field(
    mctx,
    structs,
    &info.class_path,
    &info.method_name,
    dict_atom,
  )
}

/// Project `method_name` out of whichever dictionary value `dict_atom`
/// names — a `Match` reading the corresponding field position straight
/// back out, the same shape a dictionary's own `Con` (D2) was built in.
/// `structs`' field order (declaration order, same order D2 builds an
/// instance's `Con` in) determines which `Bound` index the projection
/// reads — see `lower_core.rs`'s `Literal::Match` lowering (`ctx.push`ing
/// each pattern var in order means the LAST-declared field ends up
/// `Bound(0)`, the innermost/most-recently-opened) for why it's
/// `fields.len() - 1 - idx`, not `idx`. Shared by `try_resolve_via_bound_dict`
/// (D5, a dictionary already bound in scope) and `try_resolve_class_method`
/// (below, a dictionary resolved to a concrete instance's own `Con`) — both
/// ultimately need the exact same field-position lookup, whichever atom the
/// dictionary value itself lives under.
fn project_dict_field(
  mctx: &mut MetaContext,
  structs: &StructFields,
  class_path: &ModulePath,
  method_name: &Identifier,
  dict_atom: Atom,
) -> Option<CoreTerm> {
  let class_atom = mctx.intern(class_path.clone());
  let fields = &structs.structs.get(&class_atom)?.fields;
  let idx = fields.iter().position(|(name, _)| name == method_name)?;
  let bound_index = (fields.len() - 1 - idx) as u32;
  let case_name = class_path.last().clone();
  // Phase 0 capture: this Match's "constructor" name is the class's own
  // name, and the inductive it dispatches on is the class-as-single-
  // constructor-inductive registered under `class_atom` — both already
  // in hand here, no scrutinee-type inference needed (unlike an ordinary
  // `match`/`if`). Captured here rather than in `check`/`infer` since
  // this function *creates* the Match node — see `desugar_struct_literals`'s
  // doc comment for why capture lives in this pass, not the earlier one.
  mctx.record_match_resolution(vec![case_name.clone()], class_atom);
  Some(CoreTerm::Lit(CoreLit::Match {
    scrutinee: Box::new(CoreTerm::Free(dict_atom)),
    cases: vec![CoreMatchCase {
      name: case_name,
      dbgs: vec![DebugName::Anonymous; fields.len()],
      value: Box::new(CoreTerm::Bound(bound_index)),
    }],
  }))
}

/// Resolve one constraint (`[SomeClass var]`) once its own concrete type
/// (`var_ty`) is known — a bound dictionary already in scope (recursive
/// self-call, e.g. `BEq (List A)`'s own `beq` calling itself on the tail,
/// still needing "BEq A" for the element type — same "bare Free means
/// still-abstract, check what's already bound" logic as
/// `try_resolve_class_method`'s own top-level check), or a registered
/// `known_instances` entry for `var_ty`'s own head. Shared by both of
/// `resolve_instance_dict_args`'s two ways of finding `var_ty` below.
fn resolve_constraint_dict(
  mctx: &mut MetaContext,
  structs: &StructFields,
  atom_paths: &Map<Atom, ModulePath>,
  known_instances: &KnownInstances,
  dict_scope: &DictScope,
  constraint: &TypeConstraint,
  var_ty: &CoreTerm,
) -> Option<CoreTerm> {
  if let CoreTerm::Free(_) = force(mctx, var_ty.clone()).into_stripped_ctx()
    && let Some(&bound) = dict_scope.get(constraint.class())
  {
    return Some(CoreTerm::Free(bound));
  }
  let atom = head_atom_of(mctx, var_ty)?;
  let path = atom_paths
    .get(&atom)
    .or_else(|| structs.inductive_paths.get(&atom))?
    .clone();
  let instance = known_instances.get(&(constraint.class().clone(), path))?;
  Some(CoreTerm::Free(mctx.intern(instance.prefix.clone())))
}

/// An instance is a def which is a value instance of the class — so a
/// still-generic instance (`instance [BEq A] BEq (List A) {...}`) is a
/// dictionary whose OWN methods each need one leading argument per
/// instance-level constraint, resolved here exactly the way D4's
/// `try_insert_dict_args` resolves an ordinary constrained def's own
/// dictionary parameters. `concrete_meta` is the class param's fully
/// resolved (forced) type, e.g. `List I64`.
///
/// Two different shapes of constrained var, tried in order:
/// 1. A genuinely separate method-level implicit, distinct from the
///    class's own param — e.g. `class Map (M : (K:Type) -> (V:Type) ->
///    Type)` declares `K`/`V` as their own named foralls on `Map.empty`'s
///    type (`M K V`), so `instance [BOrd K] Map BTreeMap`'s `K` has its
///    OWN meta in `named_metas`, already pinned by this call site's own
///    unification against `expected`/its args — completely independent
///    of `concrete_meta` (`BTreeMap`'s own value has no `K`/`V` nested in
///    it at all, unlike case 2 below, so this is the ONLY way `Map`-shaped
///    constraints can ever resolve). Guarded by `var_meta != class_meta`:
///    an instance constraint can (and often does, e.g. `instance [Show A]
///    Show (List A)`) reuse the CLASS's own param name for its own,
///    unrelated, INSTANCE-scoped variable — `named_metas` has only ONE
///    entry per name, so a naive lookup would silently return the class
///    param's own meta (`List I64` as a whole) instead of failing, badly
///    mis-resolving case 2's shape. That's exactly the collision this
///    guard exists to detect and fall through past.
/// 2. Nested inside `concrete_meta`'s own application arguments (`List
///    I64`'s `I64`; `BTreeMap K V`'s `K`/`V` for `instance [BEq K, BEq V]
///    BEq BTreeMap K V`) — the original, narrower mechanism (matching
///    `KnownInstances`' own documented narrower-than-`InstanceKey` scope),
///    for a constraint whose var has no separate method-level meta of its
///    own (the `Show (List A)` shape above). `concrete_meta`'s FULL
///    application spine is unwound once, left to right (`BTreeMap K V` ->
///    `[K, V]`, via `spine_of`), and each constraint takes its OWN
///    positional argument when the counts line up — constraint `i` is
///    declared to constrain the instance template's `i`-th own type
///    argument, so `[BEq K, BEq V]` must resolve `K`'s dict from
///    `args[0]` and `V`'s from `args[1]`, NOT both from the single
///    outermost one (`args.last()`, `V`) an earlier, single-constraint-
///    only version of this function did — that mismatch silently
///    resolved `K`'s own dict using `V`'s concrete type instead, a real
///    bug found running `std/map_tests.mo`'s `BTreeMap`-keyed `BEq`/`Map`
///    instances (2+ constraints on a class param with 2+ own template
///    arguments) through the corpus. Falls back to always using the
///    single outermost argument when the counts DON'T line up (fewer
///    template args than constraints, or vice versa) — safer than
///    guessing a mapping.
///
/// Returns `None` if a constraint resolves via neither shape (no matching
/// registered instance, ...) — same "approximate, don't guess" fallback
/// style as everywhere else in this checker.
#[allow(clippy::too_many_arguments)]
fn resolve_instance_dict_args(
  mctx: &mut MetaContext,
  structs: &StructFields,
  atom_paths: &Map<Atom, ModulePath>,
  known_instances: &KnownInstances,
  dict_scope: &DictScope,
  constraints: &[TypeConstraint],
  concrete_meta: &CoreTerm,
  named_metas: &Map<Identifier, MetaId>,
  class_meta: MetaId,
) -> Option<Vec<CoreTerm>> {
  if constraints.is_empty() {
    return Some(Vec::new());
  }
  // Unwind `concrete_meta`'s own application spine once, left to right —
  // `App(App(BTreeMap, K), V)` -> `[K, V]` (`spine_of` is defined above
  // in this same file, already used by `try_resolve_class_method`).
  let (_, template_args) = spine_of(concrete_meta);
  let positional = template_args.len() == constraints.len();
  let mut dict_args = Vec::with_capacity(constraints.len());
  for (i, constraint) in constraints.iter().enumerate() {
    let [var_name] = constraint.vars().as_slice() else {
      return None;
    };
    if let Some(&var_meta) = named_metas.get(var_name)
      && var_meta != class_meta
    {
      let var_ty = CoreTerm::Meta(var_meta);
      dict_args.push(resolve_constraint_dict(
        mctx,
        structs,
        atom_paths,
        known_instances,
        dict_scope,
        constraint,
        &var_ty,
      )?);
      continue;
    }
    let elem_ty = if positional {
      template_args[i]
    } else {
      *template_args.last()?
    };
    dict_args.push(resolve_constraint_dict(
      mctx,
      structs,
      atom_paths,
      known_instances,
      dict_scope,
      constraint,
      elem_ty,
    )?);
  }
  Some(dict_args)
}

/// Companion to `check`, run *after* a successful `check(term, expected)`
/// call — rebuilds `term` with every `Lit(StructLit)` desugared into a
/// `Con`, and every resolvable class-method call site (see
/// `try_resolve_class_method`) rewritten to point at its concrete
/// instance. The evaluator refuses to run a bare `StructLit` (see
/// `eval.rs`'s `StructLiteralNotDesugared`); the OLD checker
/// (`eval/type.rs`'s `type_check_with_env`) does both of these as a
/// side effect of checking, replacing the term it returns, but THIS
/// checker's `check` deliberately never mutates the term it validates
/// (see `raise_core`'s module doc) — so it has to be a separate, explicit
/// pass instead. Mirrors `check`'s own "push expected type inward" shapes
/// (`Lam`, the `App(Lam, _)` let-desugar, `If`, `Match`) closely enough
/// that an un-annotated struct literal (`type_name: None`) resolves its
/// struct exactly the way `check` already resolved it (from `expected`),
/// just not persisted there — while an *explicitly annotated*
/// (`Some(atom)`) struct literal desugars unconditionally, wherever it's
/// found, no `expected` needed. Never errors: `check` already validated
/// `term`, so any struct literal or class-method call this pass can't
/// resolve either wasn't reachable from `check`'s own expected-type
/// threading (a documented known-simplification gap, not new) or
/// genuinely didn't need resolving — left as-is either way, matching
/// this checker's existing "approximate, don't guess" style elsewhere.
#[allow(clippy::too_many_arguments)]
pub fn desugar_struct_literals(
  mctx: &mut MetaContext,
  ctx: &TyCtx,
  structs: &StructFields,
  atom_paths: &mut Map<Atom, ModulePath>,
  known_class_methods: &KnownClassMethods,
  known_instances: &KnownInstances,
  dict_scope: &DictScope,
  term: &CoreTerm,
  expected: Option<&CoreTerm>,
) -> CoreTerm {
  match term {
    // A *bare* class-method reference with no arguments at all (e.g.
    // `Map.empty : M K V` — a value, not a function) — the `App`-spine
    // arm below never sees this shape (it's not wrapped in any `App`),
    // so it needs its own attempt here: the class param can only be
    // determined from `expected` (an empty argument spine), which
    // `try_resolve_class_method` already knows how to do.
    CoreTerm::Free(atom) => {
      let resolved = known_class_methods.get(atom).and_then(|info| {
        try_resolve_via_bound_dict(mctx, structs, dict_scope, info).or_else(|| {
          let method_typ = ctx.get(atom)?;
          try_resolve_class_method(
            mctx,
            ctx,
            structs,
            atom_paths,
            known_class_methods,
            known_instances,
            dict_scope,
            info,
            method_typ,
            &[],
            expected,
          )
        })
      });
      resolved.unwrap_or_else(|| term.clone())
    }
    CoreTerm::Bound(_) | CoreTerm::Meta(_) | CoreTerm::Sort { .. } | CoreTerm::Hole => term.clone(),

    CoreTerm::Forall { dbg, typ, body } => CoreTerm::Forall {
      dbg: dbg.clone(),
      typ: Box::new(desugar_struct_literals(
        mctx,
        ctx,
        structs,
        atom_paths,
        known_class_methods,
        known_instances,
        dict_scope,
        typ,
        None,
      )),
      body: Box::new(desugar_struct_literals(
        mctx,
        ctx,
        structs,
        atom_paths,
        known_class_methods,
        known_instances,
        dict_scope,
        body,
        None,
      )),
    },
    CoreTerm::Pi {
      dbg,
      arg,
      ret,
      mult,
    } => CoreTerm::Pi {
      dbg: dbg.clone(),
      arg: Box::new(desugar_struct_literals(
        mctx,
        ctx,
        structs,
        atom_paths,
        known_class_methods,
        known_instances,
        dict_scope,
        arg,
        None,
      )),
      ret: Box::new(desugar_struct_literals(
        mctx,
        ctx,
        structs,
        atom_paths,
        known_class_methods,
        known_instances,
        dict_scope,
        ret,
        None,
      )),
      mult: mult.clone(),
    },

    CoreTerm::Lam {
      dbg,
      param_typ,
      body,
    } => {
      let param_typ_d = desugar_struct_literals(
        mctx,
        ctx,
        structs,
        atom_paths,
        known_class_methods,
        known_instances,
        dict_scope,
        param_typ,
        None,
      );
      // Mirrors `check`'s `Lam` arm: open `body` (and, when known, its
      // return type) with a fresh atom before recursing, then close back
      // over that atom to reconstruct a proper `Lam` body. Previously
      // this only happened when `expected` was a known Pi (`ret_hint`) —
      // leaving `body` desugared in its raw, unopened `Bound`-form
      // whenever it wasn't, with NO ctx entry at all for this lambda's
      // own parameter, silently failing to resolve any class-method call
      // inside that needed it. Concretely: an unannotated `let`-bound
      // closure (`let f := fn (x : I64) => x == 3 in ...` — `expected` is
      // `None` at the closure's OWN desugar site, since the enclosing
      // `let` has no type annotation on `f`) always took the unopened
      // path, leaving `x == 3`'s `BEq.beq` call unresolved even though
      // `x`'s OWN annotation (`I64`) was right there — a real bug found
      // running `examples/iteration_advanced.mo`'s own `test_all`/
      // `test_any` through Phase 8's parity harness. Fixed narrowly: also
      // open whenever `param_typ_d` itself is a real (non-`Hole`) type —
      // an explicit annotation is exactly as good a reason to open as a
      // `ret_hint` derived from `expected`, and costs nothing extra when
      // it's available. Left UNCHANGED (still unopened) when BOTH
      // `ret_hint` and `param_typ_d` are unknown -- genuinely nothing to
      // open with, and (confirmed empirically: an earlier, broader
      // "always open, even with `Hole`" version of this fix regressed
      // std/map_tests.mo's `Map.empty`/`Map.insert` resolution, 34 tests)
      // opening with a `Hole` type is NOT safely equivalent to not
      // opening at all for every caller of this function — some
      // downstream resolution genuinely depends on the previous
      // behavior in that specific case, not yet root-caused, so left
      // alone rather than risking a wrong guess.
      let (ret_hint, arg_hint) = match expected.map(|e| force(mctx, e.clone()).into_stripped_ctx())
      {
        Some(CoreTerm::Pi { arg, ret, .. }) => {
          (Some(*ret), Some(force(mctx, *arg).into_stripped_ctx()))
        }
        _ => (None, None),
      };
      let should_open = ret_hint.is_some() || !matches!(param_typ_d.strip_ctx(), CoreTerm::Hole);
      // The type to open this binder with: the lambda's own declared
      // annotation when it has one, else (a bare `fn x => ...`/do-notation
      // `<-` bind, whose `param_typ` desugars to `Hole`) the surrounding
      // Pi's own argument type, when known from `expected` — e.g. `Monad.
      // bind`'s `A -> M B` continuation parameter, whose `A` is exactly
      // this lambda's real parameter type even though the lambda's own
      // syntax never wrote it down. Without this, an unannotated
      // do-notation `let x <- ...; match x {...}` opens `x` at `Hole`
      // instead — `infer` on `x` then trivially succeeds (type `Hole`),
      // but `resolve_match_inductive_atom` can't find a head atom on
      // `Hole`, so the nested `match`'s own resolution silently never
      // gets captured, desyncing every later capture in the same def
      // relative to `lower_core_ir.rs`'s traversal (surfaces as
      // `MatchTraversalMismatch`). Falls back to `param_typ_d` (`Hole`)
      // unchanged when `arg_hint` isn't known either, same as before this
      // fix.
      let open_typ = if !matches!(param_typ_d.strip_ctx(), CoreTerm::Hole) {
        param_typ_d.clone()
      } else {
        arg_hint.clone().unwrap_or_else(|| param_typ_d.clone())
      };
      let body_d = if should_open {
        let atom = Atom::fresh();
        let ctx2 = open_ctx(ctx, atom, open_typ.clone());
        let opened_body = open_with(body, &CoreTerm::Free(atom));
        let opened_ret = ret_hint.map(|ret| open_with(&ret, &CoreTerm::Free(atom)));
        // D5: this `Lam`'s own parameter is a dictionary (D3 elaboration
        // gave it a class-applied type, e.g. `BOrd A`) iff its type's
        // head atom is a known class — extend a LOCAL copy of
        // `dict_scope` (never mutating the caller's) so any class-method
        // reference for THIS class, anywhere in `opened_body` (including
        // inside further-nested, non-dictionary lambdas), resolves via
        // this bound atom instead of a global instance lookup; an
        // ordinary (non-dictionary) `Lam` just passes `dict_scope`
        // through unchanged.
        let dict_class = head_atom_of(mctx, &open_typ)
          .filter(|a| is_class_atom(structs, *a))
          .and_then(|a| atom_paths.get(&a).cloned());
        let extended_scope;
        let scope_for_body = if let Some(class_path) = dict_class {
          extended_scope = {
            let mut s = dict_scope.clone();
            s.insert(class_path, atom);
            s
          };
          &extended_scope
        } else {
          dict_scope
        };
        let d = desugar_struct_literals(
          mctx,
          &ctx2,
          structs,
          atom_paths,
          known_class_methods,
          known_instances,
          scope_for_body,
          &opened_body,
          opened_ret.as_ref(),
        );
        close(&d, atom)
      } else {
        desugar_struct_literals(
          mctx,
          ctx,
          structs,
          atom_paths,
          known_class_methods,
          known_instances,
          dict_scope,
          body,
          None,
        )
      };
      CoreTerm::Lam {
        dbg: dbg.clone(),
        param_typ: Box::new(param_typ_d),
        body: Box::new(body_d),
      }
    }

    CoreTerm::App { fun, arg } => {
      // `let x := value in body` shape (see `check`'s identical arm):
      // push `param_typ` into `value`, and thread `expected` through
      // into `body` unchanged (the let's own bound var can't appear in
      // the outer `expected` — it isn't in scope yet where `expected`
      // was determined).
      if let CoreTerm::Lam {
        dbg,
        param_typ,
        body,
      } = fun.as_ref().strip_ctx()
      {
        let arg_expected = if matches!(param_typ.as_ref().strip_ctx(), CoreTerm::Hole) {
          None
        } else {
          Some(param_typ.as_ref())
        };
        let arg_d = desugar_struct_literals(
          mctx,
          ctx,
          structs,
          atom_paths,
          known_class_methods,
          known_instances,
          dict_scope,
          arg,
          arg_expected,
        );
        let arg_ty = if matches!(param_typ.as_ref().strip_ctx(), CoreTerm::Hole) {
          infer(mctx, ctx, structs, arg).unwrap_or_else(|_| (**param_typ).clone())
        } else {
          (**param_typ).clone()
        };
        let atom = Atom::fresh();
        let ctx2 = open_ctx(ctx, atom, arg_ty);
        let opened_body = open_with(body, &CoreTerm::Free(atom));
        let body_d = desugar_struct_literals(
          mctx,
          &ctx2,
          structs,
          atom_paths,
          known_class_methods,
          known_instances,
          dict_scope,
          &opened_body,
          expected,
        );
        let body_d = close(&body_d, atom);
        return CoreTerm::App {
          fun: Box::new(CoreTerm::Lam {
            dbg: dbg.clone(),
            param_typ: param_typ.clone(),
            body: Box::new(body_d),
          }),
          arg: Box::new(arg_d),
        };
      }
      // Class-method call site: if this App-spine's head is a known
      // class method (`Foldable.foldr`, `BEq.beq`, ...), try to resolve
      // it to a concrete instance now — see `try_resolve_class_method`.
      // Checked BEFORE the generic fallback below (which only recurses
      // into `fun`/`arg` one level at a time and would never see the
      // whole spine's arguments together).
      let (head, spine_args) = spine_of(term);
      // D5/E1: `try_resolve_class_method` itself now checks `dict_scope`
      // (only when the class param resolves to a still-abstract, BARE
      // type variable — see its own doc comment) — no separate pre-check
      // needed here the way the bare-`Free` arm above still needs one
      // (with no spine at all, there's no other way to even attempt
      // resolution). An earlier version of this arm called
      // `try_resolve_via_bound_dict` directly, keyed purely on class
      // name — which incorrectly reused a still-generic instance's OWN
      // bound dictionary (`BEq A`, `beq`'s own dict parameter) for a
      // recursive self-call needing a DIFFERENT dictionary (`BEq (List
      // A)`, the same class but an entirely different, applied type).
      if let CoreTerm::Free(head_atom) = head
        && let Some(info) = known_class_methods.get(head_atom)
        && let Some(method_typ) = ctx.get(head_atom)
        && let Some(resolved) = try_resolve_class_method(
          mctx,
          ctx,
          structs,
          atom_paths,
          known_class_methods,
          known_instances,
          dict_scope,
          info,
          method_typ,
          &spine_args,
          expected,
        )
      {
        return resolved;
      }
      // D4: call-site dictionary auto-insertion — this App-spine's head
      // isn't a class method, but might be an ordinary constrained def
      // (`def foo [BOrd A] ...`) whose D3-elaborated type starts with a
      // dictionary `Pi` — see `try_insert_dict_args`. Checked before the
      // generic fallback for the same reason as the class-method case
      // above: the whole spine's real arguments are needed together to
      // pin down which concrete instance each dictionary resolves to.
      if let CoreTerm::Free(head_atom) = head
        && let Some(head_typ) = ctx.get(head_atom)
        && let Some(resolved) = try_insert_dict_args(
          mctx,
          ctx,
          structs,
          atom_paths,
          known_class_methods,
          known_instances,
          dict_scope,
          *head_atom,
          head_typ,
          &spine_args,
        )
      {
        return resolved;
      }

      // Generic application: mirrors `check`'s own generic-`App` arm —
      // re-`infer` `fun`'s type (cheap: `check` already fully solved
      // every metavariable this touches, so this just reads the same
      // answer back, never re-derives it) to recover `arg`'s expected
      // type, so a struct literal passed directly as a function argument
      // (e.g. `f { x := 1 }`) still gets pushed an `expected` here, not
      // just inside `Lam`/let/`If`/`Match` bodies.
      //
      // E4: `fun` may still be POLYMORPHIC in the very type variable
      // `arg`'s own struct literal needs resolved (e.g. `ok ({ term :=
      // ..., typ := ... })` — `ok`'s own `A` is a bare, fresh meta right
      // after instantiating its Forall, pinned down only by THIS call's
      // own return type, e.g. `Result TypeError TypedTerm`). `check`'s own
      // App-arm handles this by unifying the (still-open) return type
      // against `expected` BEFORE checking `arg` — do the same here,
      // best-effort/silently-ignored on failure exactly like `check`'s
      // own version, so `arg_ty` reflects whatever `expected` already
      // pins down instead of staying a bare, unresolved meta.
      let arg_ty = infer(mctx, ctx, structs, fun).ok().and_then(|fun_ty| {
        let fun_ty = instantiate_foralls(mctx, structs, &fun_ty);
        let (arg_ty, ret_ty, _mult) = expect_pi(mctx, &fun_ty).ok()?;
        if let Some(expected) = expected {
          let _ = unify(mctx, &ret_ty, expected);
        }
        Some(arg_ty)
      });
      CoreTerm::App {
        fun: Box::new(desugar_struct_literals(
          mctx,
          ctx,
          structs,
          atom_paths,
          known_class_methods,
          known_instances,
          dict_scope,
          fun,
          None,
        )),
        arg: Box::new(desugar_struct_literals(
          mctx,
          ctx,
          structs,
          atom_paths,
          known_class_methods,
          known_instances,
          dict_scope,
          arg,
          arg_ty.as_ref(),
        )),
      }
    }

    CoreTerm::Lit(CoreLit::If { cond, then, els }) => CoreTerm::Lit(CoreLit::If {
      cond: Box::new(desugar_struct_literals(
        mctx,
        ctx,
        structs,
        atom_paths,
        known_class_methods,
        known_instances,
        dict_scope,
        cond,
        None,
      )),
      then: Box::new(desugar_struct_literals(
        mctx,
        ctx,
        structs,
        atom_paths,
        known_class_methods,
        known_instances,
        dict_scope,
        then,
        expected,
      )),
      els: Box::new(desugar_struct_literals(
        mctx,
        ctx,
        structs,
        atom_paths,
        known_class_methods,
        known_instances,
        dict_scope,
        els,
        expected,
      )),
    }),

    CoreTerm::Lit(CoreLit::Match { scrutinee, cases }) => {
      let scrutinee_d = desugar_struct_literals(
        mctx,
        ctx,
        structs,
        atom_paths,
        known_class_methods,
        known_instances,
        dict_scope,
        scrutinee,
        None,
      );
      // Phase 0 capture — this is the pass that produces the FINAL term
      // structure (it's also what injects dictionary-projection `Match`
      // nodes elsewhere, via `project_dict_field`), so capturing here
      // (rather than in `check`/`infer`, which run on the pre-desugar
      // term) is what keeps traversal order consistent for a later
      // lowering pass. Recurses into `scrutinee` first (above), matching
      // `infer`'s own order, before recording this node's own
      // resolution — a nested match inside the scrutinee pushes its
      // resolution first, exactly as a single unified left-to-right walk
      // would.
      if let Ok(ty) = infer(mctx, ctx, structs, scrutinee)
        && let Some(atom) = resolve_match_inductive_atom(mctx, structs, &ty)
      {
        mctx.record_match_resolution(cases.iter().map(|c| c.name.clone()).collect(), atom);
        // The resolved inductive atom is captured into `match_resolutions`
        // above, but nothing guarantees it also appears as a literal
        // `Free(atom)` node anywhere else in this def's own body — a
        // `match` scrutinizing a value of some inductive type never
        // itself mentions that type by name (only bare constructor case
        // names survive into `CoreMatchCase`, see its own doc comment),
        // so `atom_paths` (built by walking `Free` nodes elsewhere in the
        // term) can genuinely end up never containing it, even though
        // `lower_core_ir.rs`'s `lower_match` needs to resolve exactly
        // this atom via that same def's own `atom_paths` map. A real
        // case this bites: `match some_fn args { T.a .. => .., T.b .. =>
        // .. }` where `T` is never otherwise named in the def (confirmed
        // via `chain`'s `match step n s { Step.ok .., Step.stop .. }` in
        // `core/benches/core_eval_bench.rs`'s `PARSER_COMBINATOR_SHAPED`
        // workload — `chain`'s signature/body never mentions `Step` by
        // name, so nothing else ever adds it). Insert it directly here,
        // at the one point this atom is actually resolved.
        if let Some(path) = mctx.atoms().path_of(atom) {
          atom_paths.insert(atom, path.clone());
        }
      }
      CoreTerm::Lit(CoreLit::Match {
        scrutinee: Box::new(scrutinee_d),
        cases: cases
          .iter()
          .map(|case| {
            let arity = case.dbgs.len() as u32;
            let (atoms, opened_value) = open_n(&case.value, 0, arity);
            // E2: same real-field-types-instead-of-`Hole` substitution as
            // `infer`/`check`'s own `Match` arms — this pass re-derives
            // types independently (see this function's own doc comment on
            // why: class-method resolution happens HERE, not during the
            // earlier `check` pass, so class-method calls on a
            // pattern-bound variable — e.g. a recursive
            // `Foldable.foldr`/`BEq.beq` self-call on a list's own tail —
            // need the SAME real typing here too, or the class param can
            // never be pinned down and the call is left unresolved
            // (E2's whole point) even though `check` already succeeded.
            let scrutinee_ty = infer(mctx, ctx, structs, scrutinee).ok();
            let field_tys = scrutinee_ty
              .as_ref()
              .and_then(|ty| match_case_field_types(mctx, structs, ty, &case.name));
            let mut ctx2 = ctx.clone();
            for (i, atom) in atoms.iter().enumerate() {
              let field_ty = field_tys
                .as_ref()
                .and_then(|f| f.get(atoms.len() - 1 - i))
                .cloned()
                .unwrap_or(CoreTerm::Hole);
              ctx2 = ctx2.extend(*atom, field_ty);
            }
            let d = desugar_struct_literals(
              mctx,
              &ctx2,
              structs,
              atom_paths,
              known_class_methods,
              known_instances,
              dict_scope,
              &opened_value,
              expected,
            );
            CoreMatchCase {
              name: case.name.clone(),
              dbgs: case.dbgs.clone(),
              value: Box::new(close_n(&d, 0, &atoms)),
            }
          })
          .collect(),
      })
    }

    CoreTerm::Lit(CoreLit::StructLit { fields, type_name }) => {
      let atom = type_name.or_else(|| {
        expected.and_then(|e| match force(mctx, e.clone()).into_stripped_ctx() {
          CoreTerm::Free(a) => Some(a),
          _ => None,
        })
      });
      let Some(atom) = atom else {
        return CoreTerm::Lit(CoreLit::StructLit {
          fields: fields
            .iter()
            .map(|(k, v)| {
              (
                k.clone(),
                desugar_struct_literals(
                  mctx,
                  ctx,
                  structs,
                  atom_paths,
                  known_class_methods,
                  known_instances,
                  dict_scope,
                  v,
                  None,
                ),
              )
            })
            .collect(),
          type_name: *type_name,
        });
      };
      let field_defs = structs
        .structs
        .get(&atom)
        .map(|info| info.fields.clone())
        .unwrap_or_default();
      let defaults = structs
        .structs
        .get(&atom)
        .map(|info| info.defaults.clone())
        .unwrap_or_default();
      let typ_name = atom_paths
        .get(&atom)
        .cloned()
        .unwrap_or_else(|| Identifier::new(format!("<unresolved-struct-{atom:?}>")).to_path());
      let args: Vec<Option<CoreTerm>> = field_defs
        .iter()
        .map(|(name, field_ty)| {
          // E5: a field the literal itself doesn't mention falls back to
          // its own registered default value (`h: I64 := 100`), if any,
          // instead of leaving this slot `None` (an
          // `IncompleteConstructor` error at evaluation time).
          match fields.get(name) {
            Some(v) => Some(desugar_struct_literals(
              mctx,
              ctx,
              structs,
              atom_paths,
              known_class_methods,
              known_instances,
              dict_scope,
              v,
              Some(field_ty),
            )),
            None => defaults.get(name).cloned(),
          }
        })
        .collect();
      CoreTerm::Con(CoreConstructor {
        name: Identifier::new("mk".to_string()),
        typ_name,
        num_args: args.len(),
        args,
      })
    }

    // E5: `{ base with x := v, ... }` — build a real `Con` (mirroring the
    // `StructLit` arm just above): read off `base`'s own type to find its
    // registered fields, then for each declared field, use the update's
    // own override if present (desugared with the field's own type as
    // `expected`, same as `StructLit`), otherwise project it straight out
    // of `base` via a `Match` (the same field-projection shape
    // `project_dict_field`/D5 already use for a dictionary's own
    // methods, inlined here since the scrutinee is an arbitrary
    // already-desugared TERM, not just an atom reference). Falls back to
    // leaving a `StructUpdate` literal in place (unchanged from before)
    // if `base`'s type can't be determined — the evaluator's own
    // `StructUpdateNotDesugared` error is the same failure this arm
    // used to guarantee unconditionally.
    CoreTerm::Lit(CoreLit::StructUpdate { base, fields }) => {
      let base_d = desugar_struct_literals(
        mctx,
        ctx,
        structs,
        atom_paths,
        known_class_methods,
        known_instances,
        dict_scope,
        base,
        None,
      );
      let atom = infer(mctx, ctx, structs, &base_d)
        .ok()
        .and_then(|ty| head_atom_of(mctx, &ty));
      let Some(atom) = atom else {
        return CoreTerm::Lit(CoreLit::StructUpdate {
          base: Box::new(base_d),
          fields: fields
            .iter()
            .map(|(k, v)| {
              (
                k.clone(),
                desugar_struct_literals(
                  mctx,
                  ctx,
                  structs,
                  atom_paths,
                  known_class_methods,
                  known_instances,
                  dict_scope,
                  v,
                  None,
                ),
              )
            })
            .collect(),
        });
      };
      let field_defs = structs
        .structs
        .get(&atom)
        .map(|info| info.fields.clone())
        .unwrap_or_default();
      let typ_name = atom_paths
        .get(&atom)
        .cloned()
        .unwrap_or_else(|| Identifier::new(format!("<unresolved-struct-{atom:?}>")).to_path());
      let n = field_defs.len();
      let args: Vec<Option<CoreTerm>> = field_defs
        .iter()
        .enumerate()
        .map(|(idx, (name, field_ty))| {
          Some(match fields.get(name) {
            Some(v) => desugar_struct_literals(
              mctx,
              ctx,
              structs,
              atom_paths,
              known_class_methods,
              known_instances,
              dict_scope,
              v,
              Some(field_ty),
            ),
            None => {
              // Phase 0 capture: this inline field-projection `Match`
              // (one per un-overridden field) is built directly here,
              // the same way `project_dict_field` builds its own
              // single-case dict-projection `Match` -- and, like that
              // one, needs its own `record_match_resolution` call, or
              // every OTHER `Match` node lowered later in this same def
              // (an explicit `match` on the updated struct, a nested
              // class-method call, ...) consumes the wrong queue entry
              // once traversal reaches it. Concretely: `{ p1 with x :=
              // 10 }` followed by `match p2 { mk x y => x == 10 }`
              // desugars to N of these un-overridden-field Matches (one
              // per field, here `y`) PLUS the explicit match's own "mk"
              // PLUS `==`'s own "BEq" dict-projection Match; skipping
              // this capture left the explicit match consuming "BEq"
              // instead of "mk" (`MatchTraversalMismatch { expected:
              // [mk], found: [BEq] }`), a real bug found running
              // `init/tests.mo`'s own `test_struct_update_syntax`
              // through Phase 8's parity harness.
              mctx.record_match_resolution(vec![Identifier::new("mk".to_string())], atom);
              CoreTerm::Lit(CoreLit::Match {
                scrutinee: Box::new(base_d.clone()),
                cases: vec![CoreMatchCase {
                  name: Identifier::new("mk".to_string()),
                  dbgs: vec![DebugName::Anonymous; n],
                  value: Box::new(CoreTerm::Bound((n - 1 - idx) as u32)),
                }],
              })
            }
          })
        })
        .collect();
      CoreTerm::Con(CoreConstructor {
        name: Identifier::new("mk".to_string()),
        typ_name,
        num_args: args.len(),
        args,
      })
    }

    CoreTerm::Lit(lit @ (CoreLit::Str { .. } | CoreLit::Char { .. })) => CoreTerm::Lit(lit.clone()),
    CoreTerm::Lit(lit @ (CoreLit::Num { .. } | CoreLit::Float { .. })) => {
      CoreTerm::Lit(lit.clone())
    }

    CoreTerm::Con(c) => {
      // E4: a constructor argument that's itself an unannotated struct
      // literal (e.g. `ok ({ term := ..., typ := ... })`, `Result`'s "ok"
      // wrapping a bare `TypedTerm` literal) needs `expected` to resolve
      // its own struct identity — same as any other position this pass
      // threads `expected` into. Unlike a `Lam`/`If`/`Match` body (this
      // def's OWN control-flow shapes), the field type isn't syntactically
      // adjacent — it has to come from this constructor's OWN declared
      // field types (`structs.constructors`, E2), substituted with
      // whatever concrete type args THIS Con's own `expected` (its overall
      // type, e.g. `Result TypeError TypedTerm`) carries — exactly
      // `match_case_field_types`'s own substitution, just keyed off
      // `expected` instead of a scrutinee's inferred type.
      let field_tys = expected.and_then(|e| match_case_field_types(mctx, structs, e, &c.name));
      CoreTerm::Con(CoreConstructor {
        name: c.name.clone(),
        typ_name: c.typ_name.clone(),
        num_args: c.num_args,
        args: c
          .args
          .iter()
          .enumerate()
          .map(|(i, a)| {
            a.as_ref().map(|t| {
              let arg_expected = field_tys.as_ref().and_then(|f| f.get(i));
              desugar_struct_literals(
                mctx,
                ctx,
                structs,
                atom_paths,
                known_class_methods,
                known_instances,
                dict_scope,
                t,
                arg_expected,
              )
            })
          })
          .collect(),
      })
    }
    CoreTerm::Ntv(n) => CoreTerm::Ntv(CoreNative {
      native_name: n.native_name.clone(),
      num_args: n.num_args,
      args: n
        .args
        .iter()
        .map(|a| {
          a.as_ref().map(|t| {
            desugar_struct_literals(
              mctx,
              ctx,
              structs,
              atom_paths,
              known_class_methods,
              known_instances,
              dict_scope,
              t,
              None,
            )
          })
        })
        .collect(),
    }),
    CoreTerm::Ctx { loc, term } => CoreTerm::Ctx {
      loc: loc.clone(),
      term: Box::new(desugar_struct_literals(
        mctx,
        ctx,
        structs,
        atom_paths,
        known_class_methods,
        known_instances,
        dict_scope,
        term,
        expected,
      )),
    },
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use crate::core_unify::zonk;
  use crate::lower_core::{LowerContext, lower_term};
  use crate::term::{forall, id, lam, param, pi, sort1, var};

  fn sort0() -> CoreTerm {
    CoreTerm::Sort { level: 0 }
  }

  fn empty_ctx() -> TyCtx {
    TyCtx::new()
  }

  #[test]
  fn test_tyctx_extend_is_visible_and_does_not_mutate_original() {
    let ctx = empty_ctx();
    let a = Atom::fresh();
    let ctx2 = ctx.extend(a, sort0());
    assert_eq!(ctx2.get(&a), Some(&sort0()));
    // The original `ctx` must be untouched -- `extend` returns a NEW
    // `TyCtx` sharing the old one's base/overlay, never mutates in place
    // (every real call site relies on this: opening a binder into a
    // fresh `ctx2` while the caller keeps using its own `ctx` unchanged).
    assert_eq!(ctx.get(&a), None);
  }

  #[test]
  fn test_tyctx_extend_shadows_but_overlay_entries_do_not_collide() {
    // Atoms are minted fresh and never reused, so this isn't really
    // "shadowing" in the name-collision sense -- just confirming a chain
    // of `extend` calls each remains independently visible and findable,
    // most-recent-first, the same left-to-right order `Env::extend`
    // guarantees for the evaluator's own environment.
    let ctx = empty_ctx();
    let a = Atom::fresh();
    let b = Atom::fresh();
    let ctx = ctx.extend(a, sort0());
    let ctx = ctx.extend(b, CoreTerm::Sort { level: 1 });
    assert_eq!(ctx.get(&a), Some(&sort0()));
    assert_eq!(ctx.get(&b), Some(&CoreTerm::Sort { level: 1 }));
  }

  #[test]
  fn test_tyctx_insert_visible_via_clone() {
    // `insert` (the registration-time, copy-on-write path) must still
    // make its entry visible on every existing clone that shared the
    // same base at the time of the call... actually the opposite: once
    // `insert` triggers its own copy-on-write, EARLIER clones must NOT
    // observe the new entry (this is what makes it safe to treat as an
    // ordinary mutation from the caller's own point of view) -- confirmed
    // here the same way `open_ctx`'s doc comment describes: `insert`'s
    // COW is only ever meant to be observed by the `TyCtx` it was called
    // through, not any earlier sibling clone.
    let mut ctx = empty_ctx();
    let clone_before = ctx.clone();
    let a = Atom::fresh();
    ctx.insert(a, sort0());
    assert_eq!(ctx.get(&a), Some(&sort0()));
    assert_eq!(clone_before.get(&a), None);
  }

  #[test]
  fn test_tyctx_extend_after_insert_sees_base_entries_too() {
    // The overlay/base split must be transparent to lookups -- an atom
    // registered via `insert` (base) must resolve exactly like one added
    // via `extend` (overlay), from the SAME `TyCtx`.
    let mut ctx = empty_ctx();
    let a = Atom::fresh();
    ctx.insert(a, sort0());
    let b = Atom::fresh();
    let ctx2 = ctx.extend(b, CoreTerm::Sort { level: 1 });
    assert_eq!(ctx2.get(&a), Some(&sort0()));
    assert_eq!(ctx2.get(&b), Some(&CoreTerm::Sort { level: 1 }));
  }

  fn empty_structs() -> StructFields {
    StructFields::new()
  }

  fn lower(mctx: &mut MetaContext, t: &crate::term::Term) -> CoreTerm {
    lower_term(&mut LowerContext::new(mctx.atoms_mut()), t).expect("lowering should succeed")
  }

  // -------------------------------------------------------------------
  // infer: basic leaves
  // -------------------------------------------------------------------

  #[test]
  fn test_infer_sort() {
    let mut mctx = MetaContext::new();
    assert_eq!(
      infer(
        &mut mctx,
        &empty_ctx(),
        &empty_structs(),
        &CoreTerm::Sort { level: 1 }
      )
      .unwrap(),
      CoreTerm::Sort { level: 2 }
    );
  }

  #[test]
  fn test_infer_free_looks_up_ctx() {
    let mut mctx = MetaContext::new();
    let a = Atom::fresh();
    let mut ctx = empty_ctx();
    ctx.insert(a, sort0());
    assert_eq!(
      infer(&mut mctx, &ctx, &empty_structs(), &CoreTerm::Free(a)).unwrap(),
      sort0()
    );
  }

  #[test]
  fn test_infer_unbound_free_errors() {
    let mut mctx = MetaContext::new();
    let a = Atom::fresh();
    assert_eq!(
      infer(
        &mut mctx,
        &empty_ctx(),
        &empty_structs(),
        &CoreTerm::Free(a)
      ),
      Err(InferError::UnboundVariable(a))
    );
  }

  #[test]
  fn test_infer_hole_errors_but_check_hole_succeeds() {
    let mut mctx = MetaContext::new();
    assert_eq!(
      infer(&mut mctx, &empty_ctx(), &empty_structs(), &CoreTerm::Hole),
      Err(InferError::CannotInferHole)
    );
    assert!(
      check(
        &mut mctx,
        &empty_ctx(),
        &empty_structs(),
        &CoreTerm::Hole,
        &sort0()
      )
      .is_ok()
    );
    // The other direction (expected = Hole) also trivially succeeds.
    assert!(
      check(
        &mut mctx,
        &empty_ctx(),
        &empty_structs(),
        &sort0(),
        &CoreTerm::Hole
      )
      .is_ok()
    );
  }

  // -------------------------------------------------------------------
  // infer/check Lam, real lowered `id` function
  // -------------------------------------------------------------------

  #[test]
  fn test_infer_lam_identity() {
    // fn a : Sort0 => a   :   Sort0 -> Sort0
    //
    // `ret` is Sort0 here, not Bound(0): the body `a`'s TYPE is the fixed
    // Sort0 (a's declared type), which doesn't depend on *which* value of
    // Sort0 `a` happens to be — Bound(0) would only appear in `ret` if the
    // return TYPE itself referenced the argument (a genuinely dependent
    // Pi), which this non-dependent identity function isn't.
    let mut mctx = MetaContext::new();
    let term = lam(param(id("a"), crate::term::sort0()), var("a"));
    let core = lower(&mut mctx, &term);
    let ty = infer(&mut mctx, &empty_ctx(), &empty_structs(), &core).unwrap();
    match ty {
      CoreTerm::Pi { arg, ret, .. } => {
        assert_eq!(*arg, sort0());
        assert_eq!(*ret, sort0());
      }
      other => panic!("expected Pi, got {other:?}"),
    }
  }

  #[test]
  fn test_check_lam_against_concrete_pi() {
    let mut mctx = MetaContext::new();
    let term = lam(param(id("a"), crate::term::sort0()), var("a"));
    let core = lower(&mut mctx, &term);
    let expected = CoreTerm::Pi {
      dbg: DebugName::Anonymous,
      arg: Box::new(sort0()),
      ret: Box::new(sort0()),
      mult: Multiplicity::Many,
    };
    assert!(check(&mut mctx, &empty_ctx(), &empty_structs(), &core, &expected).is_ok());
  }

  #[test]
  fn test_check_lam_against_mismatched_pi_fails() {
    let mut mctx = MetaContext::new();
    // E7: `Sort` levels are cumulative (`unify`'s own doc comment on its
    // `Sort`/`Sort` case) — a body whose type is `Sort 0` also legitimately
    // has type `Sort 1` (a `Prop` is a `Type` too), so that direction is no
    // longer a genuine mismatch. Use the OTHER direction instead (body type
    // `Sort 1`, expected return `Sort 0`) — cumulativity only ever goes
    // "up", never down, so this one must still fail.
    let term = lam(param(id("a"), crate::term::sort1()), var("a"));
    let core = lower(&mut mctx, &term);
    let expected = CoreTerm::Pi {
      dbg: DebugName::Anonymous,
      arg: Box::new(CoreTerm::Sort { level: 1 }),
      ret: Box::new(sort0()),
      mult: Multiplicity::Many,
    };
    assert!(check(&mut mctx, &empty_ctx(), &empty_structs(), &core, &expected).is_err());
  }

  #[test]
  fn test_check_lam_against_unresolved_meta_synthesizes_pi() {
    // Checking a lambda against a completely unknown type (a bare meta)
    // must succeed by synthesizing a fresh Pi and binding the meta to it
    // — the "unannotated let" scenario.
    let mut mctx = MetaContext::new();
    let term = lam(param(id("a"), crate::term::sort0()), var("a"));
    let core = lower(&mut mctx, &term);
    let m = mctx.fresh_meta(CoreTerm::Sort { level: 1 });
    check(
      &mut mctx,
      &empty_ctx(),
      &empty_structs(),
      &core,
      &CoreTerm::Meta(m),
    )
    .unwrap();
    let solved = zonk(&mctx, &CoreTerm::Meta(m));
    match solved {
      CoreTerm::Pi { arg, .. } => assert_eq!(*arg, sort0()),
      other => panic!("expected Pi, got {other:?}"),
    }
  }

  // -------------------------------------------------------------------
  // The actual bug this whole effort targets: instantiate a polymorphic
  // `id`-like function via a fresh metavariable per call, apply it, and
  // confirm two unrelated calls (both named "A") resolve independently.
  // -------------------------------------------------------------------

  fn poly_id() -> CoreTerm {
    // {A : Type} -> A -> A — no global/free name inside (only the
    // Forall-bound "A"), so a scratch, throwaway `MetaContext` is fine:
    // nothing here needs to share atom identity with a caller's own.
    lower(
      &mut MetaContext::new(),
      &forall(param(id("A"), sort1()), pi(var("A"), var("A"))),
    )
  }

  #[test]
  fn test_infer_app_instantiates_forall_and_solves_argument_type() {
    // `f`'s TYPE (not `f` itself) is the polymorphic Forall — `infer(App)`
    // infers `fun`'s type via `ctx`, then instantiates ITS leading
    // Foralls, so `fun` must be a variable whose registered type is
    // `poly_id()`, not `poly_id()` spliced in directly as the term.
    let mut mctx = MetaContext::new();
    let f_atom = Atom::fresh();
    let arg_atom = Atom::fresh();
    let mut ctx = empty_ctx();
    ctx.insert(f_atom, poly_id());
    ctx.insert(arg_atom, sort0()); // some concrete value of type Sort0

    let app_term = CoreTerm::App {
      fun: Box::new(CoreTerm::Free(f_atom)),
      arg: Box::new(CoreTerm::Free(arg_atom)),
    };
    let result_ty = infer(&mut mctx, &ctx, &empty_structs(), &app_term).unwrap();
    // {A} -> A -> A applied to a value of type Sort0 must return Sort0.
    assert_eq!(zonk(&mctx, &result_ty), sort0());
  }

  #[test]
  fn test_two_calls_to_same_poly_function_instantiate_independently() {
    let mut mctx = MetaContext::new();
    let f_atom = Atom::fresh();
    let atom1 = Atom::fresh();
    let atom2 = Atom::fresh();
    let mut ctx = empty_ctx();
    ctx.insert(f_atom, poly_id());
    ctx.insert(atom1, sort0());
    ctx.insert(atom2, CoreTerm::Sort { level: 1 });

    let app1 = CoreTerm::App {
      fun: Box::new(CoreTerm::Free(f_atom)),
      arg: Box::new(CoreTerm::Free(atom1)),
    };
    let app2 = CoreTerm::App {
      fun: Box::new(CoreTerm::Free(f_atom)),
      arg: Box::new(CoreTerm::Free(atom2)),
    };
    let ty1 = infer(&mut mctx, &ctx, &empty_structs(), &app1).unwrap();
    let ty2 = infer(&mut mctx, &ctx, &empty_structs(), &app2).unwrap();
    // Each call's own instantiation must resolve to ITS OWN argument's
    // type, with no cross-contamination between the two calls' `A`s —
    // even though both calls go through the exact same `f_atom` /
    // `poly_id()` — because each `infer(App)` allocates its OWN fresh
    // metavariable via `instantiate_foralls`.
    assert_eq!(zonk(&mctx, &ty1), sort0());
    assert_eq!(zonk(&mctx, &ty2), CoreTerm::Sort { level: 1 });
  }

  #[test]
  fn test_check_against_forall_opens_with_rigid_not_meta() {
    // Checking the identity function `fn a => a` against its own
    // fully-general polymorphic type `{A : Type} -> A -> A` must succeed
    // WITHOUT solving "A" to anything concrete — it has to stay rigid
    // (the term must work for all A), unlike `infer`'s auto-instantiation
    // of a polymorphic value being *used*, which solves with a Meta.
    // `identity` is `fn a => a` with NO type annotation on `a` (`Hole`) —
    // a bare, self-contained Lam value, exactly how a real unannotated
    // lambda checked against an inferred/expected polymorphic type would
    // look. (A `Bound(0)` here instead of `Hole` would be malformed: this
    // Lam isn't itself nested inside a `Forall` binder, so it has no
    // enclosing binder for such an index to refer to.)
    let mut mctx = MetaContext::new();
    let identity = CoreTerm::Lam {
      dbg: DebugName::Named(id("a")),
      param_typ: Box::new(CoreTerm::Hole),
      body: Box::new(CoreTerm::Bound(0)),
    };
    let expected = poly_id(); // {A : Type} -> A -> A

    // `check` should strip the expected Forall by opening with a rigid
    // atom and recurse — succeeding with no metavariables ever created.
    assert!(
      check(
        &mut mctx,
        &empty_ctx(),
        &empty_structs(),
        &identity,
        &expected
      )
      .is_ok()
    );
  }

  // -------------------------------------------------------------------
  // App against an unresolved function type (synthesizes via expect_pi)
  // -------------------------------------------------------------------

  #[test]
  fn test_app_with_meta_function_type_synthesizes_pi() {
    // `fun` is a variable whose OWN type is unknown (e.g. an unannotated
    // `let f = ... in f x`) — modeled as `f_atom : Meta(fun_ty_meta)`, not
    // as the meta spliced in directly as the applied term.
    let mut mctx = MetaContext::new();
    let fun_ty_meta = mctx.fresh_meta(CoreTerm::Sort { level: 1 });
    let f_atom = Atom::fresh();
    let arg_atom = Atom::fresh();
    let mut ctx = empty_ctx();
    ctx.insert(f_atom, CoreTerm::Meta(fun_ty_meta));
    ctx.insert(arg_atom, sort0());

    let app_term = CoreTerm::App {
      fun: Box::new(CoreTerm::Free(f_atom)),
      arg: Box::new(CoreTerm::Free(arg_atom)),
    };
    infer(&mut mctx, &ctx, &empty_structs(), &app_term).unwrap();
    // fun_ty_meta must have been solved to some Pi taking a Sort0 argument.
    match zonk(&mctx, &CoreTerm::Meta(fun_ty_meta)) {
      CoreTerm::Pi { arg, .. } => assert_eq!(*arg, sort0()),
      other => panic!("expected Pi, got {other:?}"),
    }
  }

  // -------------------------------------------------------------------
  // infer: Lit / Con / Match — the extended scope
  // -------------------------------------------------------------------

  #[test]
  fn test_infer_num_and_str_literals_get_distinct_primitive_types() {
    use crate::term::{num, str};
    let mut mctx = MetaContext::new();
    let num_core = lower(&mut mctx, &num(1));
    let num_ty = infer(&mut mctx, &empty_ctx(), &empty_structs(), &num_core).unwrap();
    let str_core = lower(&mut mctx, &str("x"));
    let str_ty = infer(&mut mctx, &empty_ctx(), &empty_structs(), &str_core).unwrap();
    assert!(matches!(num_ty, CoreTerm::Free(_)));
    assert!(matches!(str_ty, CoreTerm::Free(_)));
    assert_ne!(num_ty, str_ty, "I64 and String must be different types");
    // Same primitive referenced twice must infer to the SAME type — the
    // shared `mctx`'s own atom table makes this automatic.
    let num_core2 = lower(&mut mctx, &num(2));
    let num_ty2 = infer(&mut mctx, &empty_ctx(), &empty_structs(), &num_core2).unwrap();
    assert_eq!(num_ty, num_ty2);
  }

  #[test]
  fn test_infer_if_requires_matching_branch_types() {
    use crate::term::{if_term, num, str};
    let mut mctx = MetaContext::new();
    // `cond`'s declared param type is `var("Bool")` — a bare global
    // reference that lowers to the SAME atom `infer_lit`'s `If` handling
    // checks `cond` against internally (both go through the shared
    // `mctx`'s own atom table), so the check succeeds without needing a
    // real Bool inductive definition.

    // fn cond : Bool => if cond then 1 else 2   (matching I64 branches — ok)
    let matching = lam(
      param(id("cond"), var("Bool")),
      if_term(var("cond"), num(1), num(2)),
    );
    let matching_core = lower(&mut mctx, &matching);
    let ty = infer(&mut mctx, &empty_ctx(), &empty_structs(), &matching_core).unwrap();
    assert!(matches!(ty, CoreTerm::Pi { .. }));

    // fn cond : Bool => if cond then 1 else "two"   (mismatched — must fail)
    let mismatched = lam(
      param(id("cond"), var("Bool")),
      if_term(var("cond"), num(1), str("two")),
    );
    let mismatched_core = lower(&mut mctx, &mismatched);
    assert!(infer(&mut mctx, &empty_ctx(), &empty_structs(), &mismatched_core).is_err());
  }

  #[test]
  fn test_infer_match_unifies_all_branch_types() {
    use crate::term::{case, match_term, num, str};
    let mut mctx = MetaContext::new();
    // fn xs => match xs { a => 1, b => 2 }  (both branches I64 — ok)
    let matching = lam(
      param(id("xs"), sort1()),
      match_term(
        var("xs"),
        vec![case(id("a"), vec![], num(1)), case(id("b"), vec![], num(2))],
      ),
    );
    let matching_core = lower(&mut mctx, &matching);
    assert!(infer(&mut mctx, &empty_ctx(), &empty_structs(), &matching_core).is_ok());

    // fn xs => match xs { a => 1, b => "two" }  (mismatched — must fail)
    let mismatched = lam(
      param(id("xs"), sort1()),
      match_term(
        var("xs"),
        vec![
          case(id("a"), vec![], num(1)),
          case(id("b"), vec![], str("two")),
        ],
      ),
    );
    let mismatched_core = lower(&mut mctx, &mismatched);
    assert!(infer(&mut mctx, &empty_ctx(), &empty_structs(), &mismatched_core).is_err());
  }

  #[test]
  fn test_infer_con_returns_inductive_type_atom() {
    use crate::term::{ModulePath, constructor};
    let mut mctx = MetaContext::new();
    let con = constructor(id("empty"), ModulePath::top("List"), vec![]);
    let ty = infer(
      &mut mctx,
      &empty_ctx(),
      &empty_structs(),
      &CoreTerm::Con(crate::core_term::CoreConstructor {
        name: con.name().clone(),
        typ_name: con.typ_name().clone(),
        num_args: con.num_args(),
        args: vec![],
      }),
    )
    .unwrap();
    assert_eq!(ty, CoreTerm::Free(mctx.intern(ModulePath::top("List"))));
  }
}
