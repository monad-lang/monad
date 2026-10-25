// Pins on the `Elim` typing rule (`type_check_elim`, `core-term-
// simplification.md` R4) and its reduction rule (`whnf`'s iota on
// `Elim`, R5) -- the PUBLIC-API counterpart to `lang/src/tests/
// infer_tests.mo`'s/`whnf_tests.mo`'s own (white-box) pins, reached only
// through `type_check`/`whnf` plus `build_scope_from_decls`, the same
// surface `cubical_props.mo`/`sort_props.mo` already use. Filed here
// because R4's own landing (PR #119) added its white-box pins but never
// this file -- a gap the R5 reconnaissance caught and this PR closes.
//
// Deliberately TERM-level for the `Elim` itself, not source-level: the
// parser never produces a `Term.elim` (`elaborate_if_to_elim`/
// `elaborate_match_to_elim`, R3b, are the only builders, and neither is
// wired into `type_check_if`/`type_check_match` yet -- that is R3c), so
// there is no SOURCE SNIPPET that reaches `type_check_elim` today. Every
// pin hand-builds the `Elim` it checks and runs it through the public
// `type_check` dispatcher (`Term.elim e => type_check_elim e ...`)
// rather than the non-`pub` rule directly -- the same `accepted`/
// `rejected`-style indirection `harness.mo` already uses for leaf rules
// it cannot name.
//
// The SCOPE each `Elim` resolves `inductive`/constructors against IS
// source-level, though: this mote cannot reach `Multiplicity.many` /
// `Visibility.package_private` / `Decl.inductive_d` (none of those
// variants are `pub` from outside `lang`), so hand-building an
// `Inductive` the way `infer_tests.mo`'s own fixtures do is not an
// option here. `try_parse_decls` + `build_scope_from_decls` (both
// already `pub`, the exact pair `cubical_props.mo` uses) sidesteps that
// -- real source text registers the same `Inductive`/`InductConstructor`
// values with no new export needed.

use lang::module {try_parse_decls}
use lang::scope {build_scope_from_decls}
use lang::typecheck::infer {empty_locals, type_check}
use lang::typecheck::whnf {whnf}
use lang::types {
  DebugName, Elim, Identifier, ModulePath, NamePath, Scope, ScopeData, Similar, Term,
  binder_anon, sentinel, sort_n,
}

def elim_props_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "elim_props") List.empty)

def named_free_var (name : String) : Term := Term.var sentinel (DebugName.named (Identifier.id name))

/// A scope carrying whatever `source` declares, parsed through the real
/// pipeline -- a parse failure yields an empty scope, which makes a pin
/// fail loudly (every `Elim` below names an inductive by hand) rather
/// than silently passing against an empty one.
def scope_of (source : String) : Scope :=
    let sd : ScopeData :=
        match try_parse_decls source {
            Option.some decl_list => build_scope_from_decls elim_props_path decl_list,
            Option.none => build_scope_from_decls elim_props_path List.empty,
        } in
    {
        module_id := elim_props_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
    }

// ─── Fixtures ──────────────────────────────────────────────────────────

/// Two nullary constructors, `true` before `false` -- the shape
/// `elaborate_if_to_elim`'s own minor order depends on, reused here only
/// for the shape (no dependency on the real prelude `Bool`).
def bool_name : NamePath := NamePath.mk (List.cons (Identifier.id "Bool") List.empty)

def bool_scope : Scope := scope_of "type Bool { true, false }"

/// One field (`r : I64`) per constructor -- enough to pin minor ARITY,
/// which `Bool`'s nullary constructors above cannot exercise. `I64` is
/// a builtin, so the field type needs no further declaration.
def shape_name : NamePath := NamePath.mk (List.cons (Identifier.id "Shape") List.empty)

def shape_scope : Scope := scope_of "type Shape { circle (r : I64), square (r : I64) }"

/// `Bool` plus two more nullary types, used ONLY as two syntactically
/// DISTINCT, resolvable minor values for the iota pins below -- a bare
/// free-var minor that names nothing in scope errors out at `type_check`
/// (`TypeError.unknown_var`), and `Term.hole` (which trivially satisfies
/// any expected type) cannot distinguish "the right minor fired" from
/// "the wrong one did", so neither works here the way they do for the
/// accept/reject pins above, which never inspect the RESULT.
def marker_scope : Scope := scope_of "type Bool { true, false }\ntype Marker1 { m1 }\ntype Marker2 { m2 }"

def bool_local_types : List Term := List.cons (named_free_var "Bool") List.empty

def bool_constant_motive : Term := Term.lam binder_anon Term.hole (sort_n 0)

/// Into `Sort 1`, not `Sort 0`: the two minors below are themselves
/// TYPES (`Marker1`/`Marker2`), so the motive's codomain has to sit one
/// level above them.
def bool_marker_motive : Term := Term.lam binder_anon Term.hole (sort_n 1)

def bool_scrutinee : Term := Term.var 0 DebugName.unnamed

// ─── Accept/reject, through the public `type_check` dispatcher ────────

def elim_accepted (e : Elim) (local_types : List Term) (scope : Scope) : Bool :=
    match type_check (Term.elim e) Term.hole scope local_types empty_locals {
        ok _ => true,
        err _ => false,
    }

def elim_rejected (e : Elim) (local_types : List Term) (scope : Scope) : Bool :=
    not (elim_accepted e local_types scope)

/// The happy path for the whole rule's plumbing: inductive resolution,
/// the scrutinee-vs-params check, the motive's sort check, and the
/// lockstep walk over `Bool`'s two constructors.
#[test]
def elim_bool_constant_motive_is_accepted : Bool :=
    let e : Elim := Elim.mk bool_name List.empty List.empty bool_constant_motive
        (List.cons Term.hole (List.cons Term.hole List.empty)) bool_scrutinee in
    elim_accepted e bool_local_types bool_scope

/// Soundness-shaped pin: an `e.inductive` that names no real inductive
/// must be refused, not silently treated as unconstrained.
#[test]
def elim_unknown_inductive_is_rejected : Bool :=
    let bad_name : NamePath := NamePath.mk (List.cons (Identifier.id "NoSuchInductive") List.empty) in
    let e : Elim := Elim.mk bad_name List.empty List.empty bool_constant_motive
        (List.cons Term.hole (List.cons Term.hole List.empty)) bool_scrutinee in
    elim_rejected e bool_local_types bool_scope

/// The motive must be a function into a SORT -- `Term.hole` as a body is
/// neither.
#[test]
def elim_non_sort_motive_is_rejected : Bool :=
    let bad_motive : Term := Term.lam binder_anon Term.hole Term.hole in
    let e : Elim := Elim.mk bool_name List.empty List.empty bad_motive
        (List.cons Term.hole (List.cons Term.hole List.empty)) bool_scrutinee in
    elim_rejected e bool_local_types bool_scope

/// `Bool` declares two constructors; one minor is one short -- this is
/// the genuinely NEW pin R4 did not carry: a wrong MINOR COUNT, distinct
/// from a wrong field arity WITHIN one minor (below).
#[test]
def elim_wrong_minor_count_is_rejected : Bool :=
    let e : Elim := Elim.mk bool_name List.empty List.empty bool_constant_motive
        (List.cons Term.hole List.empty) bool_scrutinee in
    elim_rejected e bool_local_types bool_scope

/// `circle`/`square` each declare ONE field (`r : I64`); a minor that is
/// a concrete non-function term (`Sort 0`, not a lambda at all) is
/// checked against a one-argument Pi (`build_elim_minor_pi_chain`) and
/// must be refused -- the per-minor FIELD-ARITY counterpart to the
/// minor-COUNT pin above, which `Bool`'s nullary constructors cannot
/// exercise at all. (`Term.hole` cannot stand in for the wrong-shaped
/// minor here -- it trivially satisfies ANY expected type, per
/// `type_check`'s own `Term.hole` arm, so it would make this pin pass
/// whether or not the arity check exists at all.)
#[test]
def elim_minor_with_wrong_field_arity_is_rejected : Bool :=
    let shape_scrutinee : Term := Term.var 0 DebugName.unnamed in
    let shape_local_types : List Term := List.cons (named_free_var "Shape") List.empty in
    let motive : Term := Term.lam binder_anon Term.hole (sort_n 0) in
    let e : Elim := Elim.mk shape_name List.empty List.empty motive
        (List.cons (sort_n 0) (List.cons (sort_n 0) List.empty)) shape_scrutinee in
    elim_rejected e shape_local_types shape_scope

// ─── Iota: a CHECKED `Elim` reduces through `whnf` (R4 + R5, end to end) ───

/// `type_check` on a real constructor scrutinee (`Bool.true`, not a bound
/// variable) returns a CHECKED `Term.elim` (`tt.term`); `whnf` on that
/// term must fire the FIRST minor (`true` is `Bool`'s first constructor)
/// -- the property R4 and R5 together are supposed to deliver: a
/// well-typed elimination actually COMPUTES. `Marker1`/`Marker2` (see
/// `marker_scope`) are the two minors: distinct, resolvable, and into
/// `Sort 1` (the motive's codomain, one level above the two TYPES being
/// selected between).
#[test]
def elim_checked_term_reduces_to_first_minor : Bool :=
    let scrutinee : Term := named_free_var "Bool.true" in
    let e : Elim := Elim.mk bool_name List.empty List.empty bool_marker_motive
        (List.cons (named_free_var "Marker1") (List.cons (named_free_var "Marker2") List.empty)) scrutinee in
    match type_check (Term.elim e) Term.hole marker_scope List.empty empty_locals {
        err _ => false,
        ok tt => Similar.similar (whnf marker_scope empty_locals tt.term) (named_free_var "Marker1"),
    }

/// The other constructor selects the other minor.
#[test]
def elim_checked_term_reduces_to_second_minor : Bool :=
    let scrutinee : Term := named_free_var "Bool.false" in
    let e : Elim := Elim.mk bool_name List.empty List.empty bool_marker_motive
        (List.cons (named_free_var "Marker1") (List.cons (named_free_var "Marker2") List.empty)) scrutinee in
    match type_check (Term.elim e) Term.hole marker_scope List.empty empty_locals {
        err _ => false,
        ok tt => Similar.similar (whnf marker_scope empty_locals tt.term) (named_free_var "Marker2"),
    }

/// A BOUND scrutinee has nothing to dispatch on: the checked term must
/// stay a (reduced-scrutinee) `Term.elim` under `whnf`, not collapse to
/// either minor -- the negative control proving the two pins above
/// actually discriminate, rather than any `Elim` reducing to the first
/// minor regardless of its scrutinee.
#[test]
def elim_checked_term_with_unresolved_scrutinee_stays_stuck : Bool :=
    let e : Elim := Elim.mk bool_name List.empty List.empty bool_marker_motive
        (List.cons (named_free_var "Marker1") (List.cons (named_free_var "Marker2") List.empty)) bool_scrutinee in
    match type_check (Term.elim e) Term.hole marker_scope bool_local_types empty_locals {
        err _ => false,
        ok tt =>
            match whnf marker_scope empty_locals tt.term {
                Term.elim _ => true,
                _ => false,
            },
    }
