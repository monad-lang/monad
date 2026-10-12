// Pins on R10: every SHAPE PROBE reads through a `Term.ctx` location
// wrapper (plans/type-system/core-term-simplification.md).
//
// What is under test is a property of the REPRESENTATION, not a typing
// rule: `Term.ctx` is a pure annotation, so a probe that inspects a
// term's shape must answer exactly what it would answer for the
// unwrapped term. `term_peel`'s own doc comment (`lang/src/types.mo`)
// states the contract; `Similar.similar` and `unify` have always met it,
// `sort_level_of`/`cubical_prim_of`/`term_matches_carrier`/
// `flatten_call_spine` were made to meet it one at a time, each after a
// measured regression, and R10 finishes the job for the four probes
// pinned here.
//
// WHY THIS FILE IS NOT IN `proofs/src/checker/`: those files pin
// TYPE-THEORETIC rules (sort universes, cubical primitives, eliminator
// motives) and are a separate mote, which can only reach `lang` through
// `pub` names -- `harness.mo` records keeping that export surface at
// zero as a deliberate constraint. These four probes are internal, and
// the intra-mote precedent is `types_tests.mo`'s
// `test_cubical_prim_of_peels_a_location`, which is the same pin for the
// same reason. Moving these to `proofs/` would widen `lang`'s surface
// for no gain.
//
// Every pin below is NON-VACUOUS BY CONSTRUCTION, and that is the design
// constraint rather than a nicety: a probe that answers
// `Option.none`/its fallback for BOTH the wrapped and the unwrapped term
// satisfies any differential form of this property while testing
// nothing. So each pin asserts the probe's real ANSWER on the wrapped
// input -- the name it must resolve, the type it must return, the
// substitution it must record -- which is only reachable through the
// peel. `lang/src/tests/cubical_bind_tests.mo`'s term-shaped pins reach
// for the same reason.

use std::list {List.length}
use lang::types {
  Identifier, Location, ModulePath, Scope, ScopeData, Similar, Term, binder_anon, named,
  sentinel,
}
use lang::module {try_parse_decls}
use lang::scope {build_scope_from_decls, type_head_name_local}
use lang::typecheck::infer {
  con_spine_result_typ, solve_typevars, type_head_name,
}

def ctx_peel_synthetic_path : ModulePath :=
    ModulePath.mk (List.cons (Identifier.id "ctx_peel_tests") List.empty)

/// A location to wrap terms in. Every field is a real value: an unset
/// one would make a pin pass or fail for reasons unrelated to peeling.
def ctx_peel_loc : Location := { offset := 0, line := 1, column := 1 }

/// `Box` with one zero-arity constructor and NO type parameters --
/// `con_spine_result_typ`'s non-vacuity needs both: `inductive_has_params`
/// makes a parameterized inductive fall through to the fallback, and
/// `find_constructor_in_inductive` has to find the constructor it is
/// handed. Built from source through the real parse + scope-build
/// pipeline, so the lookup keys are the ones the compiler really
/// produces rather than ones this file guesses.
def ctx_peel_scope : Scope :=
    let sd : ScopeData :=
        match try_parse_decls "type Box { box }\n" {
            Option.some decl_list => build_scope_from_decls ctx_peel_synthetic_path decl_list,
            Option.none => build_scope_from_decls ctx_peel_synthetic_path List.empty,
        } in
    {
        module_id := ctx_peel_synthetic_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
    }

/// A named free variable -- the only head `type_head_name` answers for.
def ctx_peel_named (n : String) : Term :=
    Term.var sentinel (DebugName.named (Identifier.id n))

/// The head `con_spine_result_typ` resolves: a DOTTED reference whose
/// qualifier names an inductive in scope (`qualified_con_ref_typ`'s
/// `Box.box` convention).
def ctx_peel_con_head : Term := ctx_peel_named "Box.box"

/// What `con_spine_result_typ` must answer for `ctx_peel_con_head`: the
/// owning inductive's OWN bare name, which is what
/// `qualified_con_ref_typ` substitutes. Spelled out rather than
/// compared against a second call, so the pin states the rule instead of
/// stating that two calls agree.
def ctx_peel_con_head_typ : Term := ctx_peel_named "Box"

def ctx_peel_opt_eq (got : Option Identifier) (want : String) : Bool :=
    match got {
        Option.some id => Similar.similar id (Identifier.id want),
        Option.none => false,
    }

// --- `type_head_name` (`lang/src/typecheck/infer.mo`) --------------------

/// The direct shape: the wrapper is on the term being probed.
#[test]
def test_type_head_name_peels_a_location : Bool :=
    ctx_peel_opt_eq (type_head_name (Term.ctx ctx_peel_loc (ctx_peel_named "List"))) "List"

/// `Term.app` position. `type_head_name`'s own recursion passes `f` on
/// UNPEELED, so this is a different arm from the pin above: the wrapper
/// is reached one call deeper, and without the `Term.ctx` arm the answer
/// is `Option.none` rather than the name. A pin that only wrapped the
/// outermost term would not cover it.
#[test]
def test_type_head_name_peels_a_located_head_of_a_spine : Bool :=
    let spine : Term := Term.app (Term.ctx ctx_peel_loc (ctx_peel_named "List")) (ctx_peel_named "x") in
    ctx_peel_opt_eq (type_head_name spine) "List"

/// The complementary shape: the wrapper is around the whole spine, so
/// the first match is the one that has to see through it.
#[test]
def test_type_head_name_peels_a_located_spine : Bool :=
    let spine : Term := Term.app (ctx_peel_named "List") (ctx_peel_named "x") in
    ctx_peel_opt_eq (type_head_name (Term.ctx ctx_peel_loc spine)) "List"

// --- `type_head_name_local` (`lang/src/scope.mo`) -----------------------

/// `scope.mo`'s deliberate duplicate of the function above. Its doc
/// comment records why it exists (a module cycle) and why the two must
/// agree; these two pins are what hold them to it. If only one twin
/// peels, a carrier resolves on one side of the pipeline and not the
/// other -- an inconsistency no single-sided pin can observe.
#[test]
def test_type_head_name_local_peels_a_location : Bool :=
    ctx_peel_opt_eq (type_head_name_local (Term.ctx ctx_peel_loc (ctx_peel_named "List"))) "List"

#[test]
def test_type_head_name_local_peels_a_located_head_of_a_spine : Bool :=
    let spine : Term := Term.app (Term.ctx ctx_peel_loc (ctx_peel_named "List")) (ctx_peel_named "x") in
    ctx_peel_opt_eq (type_head_name_local spine) "List"

// --- `con_spine_result_typ` (`lang/src/typecheck/infer.mo`) -------------

/// The head of the spine. The answer here is not `Option`-shaped, so the
/// failure mode is a silent downgrade to the FALLBACK rather than a
/// miss: without the peel the spine reports `Term.hole`, and a
/// constructor call gets an uninformative result type instead of its
/// own.
#[test]
def test_con_spine_result_typ_peels_a_located_head : Bool :=
    let got : Term :=
        con_spine_result_typ (Term.ctx ctx_peel_loc ctx_peel_con_head) Term.hole ctx_peel_scope in
    Similar.similar got ctx_peel_con_head_typ

/// An inner `app` of the spine -- `con_spine_result_typ`'s recursion
/// hands `g` on unpeeled, so a wrapper between two applications would end
/// the walk early with the same silent fallback.
#[test]
def test_con_spine_result_typ_peels_a_located_inner_app : Bool :=
    let spine : Term := Term.app (Term.ctx ctx_peel_loc ctx_peel_con_head) (ctx_peel_named "x") in
    let got : Term := con_spine_result_typ spine Term.hole ctx_peel_scope in
    Similar.similar got ctx_peel_con_head_typ

/// Non-vacuity control for the two pins above: the same call on a head
/// that does NOT resolve must give the fallback. If this ever returns
/// the box type, the pins above are passing for a reason other than the
/// peel.
#[test]
def test_con_spine_result_typ_falls_back_for_an_unresolvable_head : Bool :=
    let got : Term := con_spine_result_typ (ctx_peel_named "Nope.nothing") Term.hole ctx_peel_scope in
    Similar.similar got Term.hole

// --- `solve_typevars` (`lang/src/typecheck/infer.mo`) -------------------

/// A two-`pi` parameter type and a two-`pi` actual of the SAME shape.
/// Each `pi` layer solves one type variable, so the length of the
/// substitution counts the layers the walk reached -- and both the
/// wrapped-parameter and wrapped-actual pins below read it.
def ctx_peel_two_pis (a : String) (b : String) : Term :=
    Term.pi binder_anon (ctx_peel_named a) (ctx_peel_named b)

/// The parameter side. A wrapper here stops the walk at `_ => subst`
/// before any layer is examined, so a type variable is silently never
/// solved.
#[test]
def test_solve_typevars_peels_a_located_parameter : Bool :=
    let got : List (Pair Identifier Term) :=
        solve_typevars ctx_peel_scope
            (Term.ctx ctx_peel_loc (ctx_peel_named "TvA"))
            (ctx_peel_named "Zeta") List.empty in
    I64.beq (List.length got) 1

/// The actual side, one `pi` deep. This pin is why the peel is on
/// `actual` too and not only on `param`: the parameter arm matches
/// `Term.pi`, and a wrapper on the ACTUAL stops the descent one level
/// down, where the length drops to zero with no visible cause. It also
/// reaches the `Term.hole` guard from the wrong side -- a wrapper hides
/// a hole actual, so the guard that exists to stop the substitution
/// being poisoned lets it through instead.
#[test]
def test_solve_typevars_peels_a_located_actual : Bool :=
    let got : List (Pair Identifier Term) :=
        solve_typevars ctx_peel_scope
            (ctx_peel_two_pis "TvA" "TvB")
            (Term.ctx ctx_peel_loc (ctx_peel_two_pis "Xa" "Xb")) List.empty in
    I64.beq (List.length got) 2

/// Non-vacuity control: the same call with the actual UNWRAPPED must
/// record both layers. Without this, a `solve_typevars` that recorded
/// two pairs for every input would make the pin above pass unchanged.
#[test]
def test_solve_typevars_records_both_layers_unwrapped : Bool :=
    let got : List (Pair Identifier Term) :=
        solve_typevars ctx_peel_scope
            (ctx_peel_two_pis "TvA" "TvB")
            (ctx_peel_two_pis "Xa" "Xb") List.empty in
    I64.beq (List.length got) 2
