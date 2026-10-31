/// Type-level multiplicity kinds: `#[linear]` and `#[proof]` inductives.
///
/// Part of the view-types milestone (`plans/type-system/view-types.md`)
/// and the QTT `#[linear]` item (`quantitative-types.md` Phase 7). Both
/// are ordinary attributes already carried on `Inductive.attrs`, so this
/// module is a classifier, not a parser change:
///
/// - `#[linear]` — every binder whose type is this inductive is used
///   exactly once. `?x` may relax it to affine at a binding site; `%x` is
///   an error. A `Copy`/`Clone` instance for it is rejected.
/// - `#[proof]` — stronger: every binder is linear, never `Copy`, and the
///   type has no run-time representation (in v1 it is also not
///   constructible, so no value exists).
///
/// Recognition is by ATTRIBUTE, not by name — the `#[shared]` precedent
/// (`usage.mo`'s `shared_inductive`). The sets are built once per module
/// from the scope's inductives, keyed by both the rendered full name and
/// the bare last segment, because an elaborated type head is usually the
/// bare identifier (`Cell`, not `init::view::Cell`).
use lib::types {
  Attribute, DebugName, Identifier, Inductive, ModulePath, NamePath, Scope, ScopeData,
  Term, Visibility, has_attr, show_identifier, show_name_path,
}
use lib::scope {scope_data_empty, scope_globals}
use std::map {HashMap}
use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}

/// The two name sets, built once per module.
pub struct TypeKinds {
    proof : HashMap String Bool,
    linear : HashMap String Bool,
}

/// No `#[linear]`/`#[proof]` type in scope. The affine rule's historical
/// entry points use this so their behaviour is unchanged when no kinds
/// are involved (e.g. the report's unit tests).
pub def type_kinds_empty : TypeKinds :=
    { proof := str_map_empty, linear := str_map_empty }

pub def type_kinds_proof (k : TypeKinds) : HashMap String Bool := k.proof

pub def type_kinds_linear (k : TypeKinds) : HashMap String Bool := k.linear

/// Scan the scope's inductives once. A struct's synthetic inductive is
/// included (its attrs are carried by `build_scope_struct`; see that
/// function's own comment).
///
/// Both spellings an elaborated type head can arrive as are registered:
/// the full rendered name and the bare last segment. The bare key is what
/// makes classification work at all (an elaborated head is usually
/// `Cell`, not `init::view::Cell`).
///
/// **Deliberately over-approximating.** If a user declares an unrelated
/// type also named `Cell` (or `At`), a bare reference is treated as the
/// kinded one too. That is a loud false positive (the affine/view rules
/// may reject valid code) rather than a silent fail-open: dropping
/// ambiguous bare names would disable `#[linear]`/`#[proof]` enforcement
/// for the real type in any module that happens to import a collision.
/// Exact resolution through `scope_resolve_name` is the durable fix.
pub def type_kinds (s : Scope) : TypeKinds :=
    let sd := scope_globals s in
    type_kinds_go (HashMap.to_list sd.inductives) str_map_empty str_map_empty

#[partial]
def type_kinds_go (pairs : List (Pair String Inductive)) (proofs : HashMap String Bool) (linears : HashMap String Bool) : TypeKinds :=
    match pairs {
        List.empty => { proof := proofs, linear := linears },
        List.cons p rest =>
            match p {
                Pair.pair _key ind =>
                    match ind {
                        Inductive.mk name _params _typ _ctors attrs _vis =>
                            if has_attr (Identifier.id "proof") attrs then
                                type_kinds_go rest (insert_kind_names name proofs) linears
                            else if has_attr (Identifier.id "linear") attrs then
                                type_kinds_go rest proofs (insert_kind_names name linears)
                            else type_kinds_go rest proofs linears,
                    },
            },
    }

/// Register both spellings a type head can arrive as: the full rendered
/// name and the bare last segment.
#[partial]
def insert_kind_names (name : NamePath) (m : HashMap String Bool) : HashMap String Bool :=
    let with_full : HashMap String Bool := str_map_insert (show_name_path name) true m in
    match last_segment name.segments {
        Option.some id => str_map_insert (show_identifier id) true with_full,
        Option.none => with_full,
    }

#[partial]
def last_segment (segs : List Identifier) : Option Identifier :=
    match segs {
        List.empty => Option.none,
        List.cons x rest =>
            match rest {
                List.empty => Option.some x,
                List.cons _ _ => last_segment rest,
            },
    }

def name_known (m : HashMap String Bool) (n : String) : Bool :=
    match str_map_lookup n m {
        Option.some b => b,
        Option.none => false,
    }

/// The head name of a type term, peeling `ctx` and the application spine.
/// A bare or qualified `Term.var` is the only shape that names a type.
#[partial]
pub def kind_head_name (t : Term) : Option String :=
    match t {
        Term.ctx _loc inner => kind_head_name inner,
        Term.app callee _arg => kind_head_name callee,
        Term.var _idx dbg =>
            match dbg {
                DebugName.named id => Option.some (show_identifier id),
                DebugName.unnamed => Option.none,
            },
        _ => Option.none,
    }

pub def is_proof_type (k : TypeKinds) (t : Term) : Bool :=
    match kind_head_name t {
        Option.some n => name_known (type_kinds_proof k) n,
        Option.none => false,
    }

pub def is_linear_type (k : TypeKinds) (t : Term) : Bool :=
    match kind_head_name t {
        Option.some n => name_known (type_kinds_linear k) n,
        Option.none => false,
    }

pub def is_linear_or_proof (k : TypeKinds) (t : Term) : Bool :=
    is_linear_type k t || is_proof_type k t

/// Does any type head ANYWHERE in `t` name a linear or proof kind?
/// Used by the container-shape rule: a `Shared`/`Ref`/`Array` wrapping
/// one is unrepresentable because those are re-readable (and `Shared` is
/// `Copy`), so they could hand out two handles to one allocation.
#[partial]
pub def mentions_linear_or_proof (k : TypeKinds) (t : Term) : Bool :=
    match t {
        Term.ctx _loc inner => mentions_linear_or_proof k inner,
        Term.var _idx _dbg => is_linear_or_proof k t,
        Term.app callee arg =>
            mentions_linear_or_proof k callee || mentions_linear_or_proof k arg,
        // A `pi` domain/codomain can also wrap a container.
        Term.pi _b arg ret =>
            mentions_linear_or_proof k arg || mentions_linear_or_proof k ret,
        _ => false,
    }

/// Is this type term a `Shared`/`Ref`/`Array` application? Only the
/// spine head matters; the argument is checked by the caller.
pub def is_container_head (t : Term) : Bool :=
    match kind_head_name t {
        Option.some n =>
            String.beq n "Shared" || String.beq n "Ref" || String.beq n "Array",
        Option.none => false,
    }

/// A container (`Shared`/`Ref`/`Array`) applied to a type that mentions a
/// linear or proof kind, anywhere in the type expression.
#[partial]
pub def container_wraps_linear (k : TypeKinds) (t : Term) : Bool :=
    match t {
        Term.ctx _loc inner => container_wraps_linear k inner,
        Term.app callee arg =>
            if is_container_head callee && mentions_linear_or_proof k arg then true
            else container_wraps_linear k callee || container_wraps_linear k arg,
        Term.pi _b arg ret =>
            container_wraps_linear k arg || container_wraps_linear k ret,
        _ => false,
    }

// ─── Tests ─────────────────────────────────────────────────────────

def dbg (s : String) : DebugName := DebugName.named (Identifier.id s)

def ty (s : String) : Term := Term.var (0 - 1) (dbg s)

def attrs_of (names : List String) : List Attribute :=
    match names {
        List.empty => List.empty,
        List.cons n rest =>
            List.cons (Attribute.mk (Identifier.id n) List.empty) (attrs_of rest),
    }

def ind_named (name : String) (attrs : List Attribute) : Inductive :=
    Inductive.mk (NamePath.mk (List.cons (Identifier.id name) List.empty))
        List.empty Term.hole List.empty attrs Visibility.package_private

def probe_scope_base : Scope :=
    { module_id := ModulePath.mk (List.cons (Identifier.id "probe") List.empty),
      scope := scope_data_empty,
      parent := Option.none,
      incomplete_match_ok := false }

def scope_with_inds (inds : List Inductive) : Scope :=
    let m : HashMap String Inductive := scope_with_inds_go inds str_map_empty in
    { probe_scope_base with scope := { scope_data_empty with inductives := m } }

#[partial]
def scope_with_inds_go (inds : List Inductive) (m : HashMap String Inductive) : HashMap String Inductive :=
    match inds {
        List.empty => m,
        List.cons ind rest =>
            match ind {
                Inductive.mk name _params _typ _ctors _attrs _vis =>
                    scope_with_inds_go rest (str_map_insert (show_name_path name) ind m),
            },
    }

def kinds_probe : TypeKinds :=
    type_kinds (scope_with_inds
        (List.cons (ind_named "Cell" (attrs_of (List.cons "linear" List.empty)))
            (List.cons (ind_named "At" (attrs_of (List.cons "proof" List.empty)))
                List.empty)))

#[test]
def test_linear_kind_is_recognized_by_attribute : Bool :=
    is_linear_type kinds_probe (ty "Cell") && Bool.not (is_proof_type kinds_probe (ty "Cell"))

#[test]
def test_proof_kind_is_recognized_by_attribute : Bool :=
    is_proof_type kinds_probe (ty "At") && Bool.not (is_linear_type kinds_probe (ty "At"))

#[test]
def test_an_unmarked_type_is_neither : Bool :=
    Bool.not (is_linear_type kinds_probe (ty "I64")) &&
        Bool.not (is_proof_type kinds_probe (ty "I64"))

#[test]
def test_an_applied_head_is_classified : Bool :=
    // `Cell I64` -- the spine head carries the kind, not the argument.
    is_linear_type kinds_probe (Term.app (ty "Cell") (ty "I64"))

#[test]
def test_a_shared_of_a_cell_is_a_container_violation : Bool :=
    container_wraps_linear kinds_probe (Term.app (ty "Shared") (ty "Cell"))

#[test]
def test_a_shared_of_a_copy_type_is_fine : Bool :=
    Bool.not (container_wraps_linear kinds_probe (Term.app (ty "Shared") (ty "I64")))

def ind_qualified (segs : List Identifier) (attrs : List Attribute) : Inductive :=
    Inductive.mk (NamePath.mk segs) List.empty Term.hole List.empty attrs Visibility.package_private

#[test]
def test_a_same_named_type_is_over_approximated : Bool :=
    // Two different types whose last segment is `Cell`. A bare `Cell`
    // reference could be either; the classifier deliberately treats it as
    // the kinded one. That is a loud false positive (see `type_kinds`'s
    // own doc) rather than silently disabling enforcement for the real
    // `Cell`. The full names classify too.
    let cell_a : Inductive :=
        ind_qualified (List.cons (Identifier.id "a") (List.cons (Identifier.id "Cell") List.empty))
            (attrs_of (List.cons "linear" List.empty)) in
    let cell_b : Inductive :=
        ind_qualified (List.cons (Identifier.id "b") (List.cons (Identifier.id "Cell") List.empty))
            (attrs_of (List.cons "linear" List.empty)) in
    let kinds : TypeKinds := type_kinds (scope_with_inds (List.cons cell_a (List.cons cell_b List.empty))) in
    is_linear_type kinds (ty "Cell")
        && is_linear_type kinds (ty "a.Cell")
        && is_linear_type kinds (ty "b.Cell")

#[test]
def test_a_nested_container_mentions_the_kind : Bool :=
    // `Ref (List (Cell I64))` -- the linear kind is one level down.
    mentions_linear_or_proof kinds_probe
        (Term.app (ty "Ref") (Term.app (ty "List") (Term.app (ty "Cell") (ty "I64"))))
