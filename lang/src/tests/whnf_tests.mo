use lib::types {
  DebugName, Identifier, Literal, Location, LocalScope, LocalVar, MatchCase,
  ModulePath, Scope, ScopeData, Similar, Term, id, mp, named, sentinel,
}
use lib::module {parse_all_decls}
use lib::parser::core {fail, success}
use lib::scope {build_scope_from_decls}
use lib::typecheck::whnf {whnf}

// Unit tests for the WHNF reducer. Scopes are built by PARSING a real
// source snippet rather than hand-assembling `Def`s: `build_scope_from_
// decls` is the same entry the checker itself goes through, so a def's
// body reaches `ScopeData.def_bodies` in exactly the shape delta
// reduction will meet in production (a `Term.lam` chain, one lambda per
// declared parameter). Inputs are hand-built `Term`s, so each test
// exercises one reduction rule in isolation.

def synthetic_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "synthetic") List.empty)

def empty_locals : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

/// A scope carrying whatever `source` declares. A snippet that fails to
/// parse yields an empty scope, which makes the delta tests below fail
/// rather than silently pass on a stuck term.
def scope_of (source : String) : Scope :=
    let sd : ScopeData :=
        match parse_all_decls source {
            success _ decl_list => build_scope_from_decls synthetic_path decl_list,
            fail _ => build_scope_from_decls synthetic_path List.empty,
        } in
    {
        module_id := synthetic_path,
        scope := sd,
        parent := Option.none,
    }

/// A free (global) reference by name -- `sentinel` is what marks a var
/// as unbound-and-resolved-by-name, see `ScopeData`'s own docs.
def free_var (nm : String) : Term := Term.var sentinel (DebugName.named (Identifier.id nm))

def dbg_x : DebugName := DebugName.named (Identifier.id "x")

/// `idt` is the identity on types; `konst` ignores its argument (the
/// `identity_type` shape from the conversion-checking plan). Both need
/// BOTH rules to reduce: delta to turn the name into a lambda, then
/// beta to apply it.
///
/// `idt`'s body is deliberately the PARAMETER rather than a type name.
/// `build_scope_from_decls` runs on raw, PRE-elaboration decls, so a
/// body written `Type` is still an unresolved name there, not
/// `Term.type_ 1` -- comparing against a hand-built sort would be
/// asserting something about elaboration, not about reduction. A bound
/// variable substituted by beta is unambiguous.
def idt_scope : Scope := scope_of "type P { p0 }\ndef idt (x : Type) : Type := x\ndef konst (x : Type) : Type := P"

// --- beta ---

#[test]
def test_whnf_beta_identity_lambda : Bool :=
    // `(fn x : Type => x) Prop` reduces to `Prop`.
    let redex : Term := Term.app (Term.lam dbg_x (Term.type_ 1) (Term.var 0 dbg_x)) (Term.type_ 0) in
    Similar.similar (whnf idt_scope empty_locals redex) (Term.type_ 0)

#[test]
def test_whnf_beta_constant_lambda_drops_argument : Bool :=
    // `(fn x : Type => Type) Prop` reduces to `Type`, and the discarded
    // argument must not leak into the result.
    let redex : Term := Term.app (Term.lam dbg_x (Term.type_ 1) (Term.type_ 1)) (Term.type_ 0) in
    Similar.similar (whnf idt_scope empty_locals redex) (Term.type_ 1)

// --- delta ---

#[test]
def test_whnf_delta_unfolds_global_def : Bool :=
    // `idt` on its own unfolds to its body, which is a lambda.
    match whnf idt_scope empty_locals (free_var "idt") {
        Term.lam _ _ _ => true,
        _ => false,
    }

#[test]
def test_whnf_delta_then_beta : Bool :=
    // The rule this whole module exists for: `idt Prop` is headed by a
    // FREE VARIABLE, so beta alone has nothing to fire on. Only after
    // delta unfolds `idt` into a lambda can beta substitute `Prop` for
    // its parameter.
    Similar.similar (whnf idt_scope empty_locals (Term.app (free_var "idt") (Term.type_ 0))) (Term.type_ 0)

#[test]
def test_whnf_delta_then_beta_constant_function : Bool :=
    // `konst Prop` -- the `identity_type foo` shape from the plan: the
    // body ignores the argument entirely, so the result must be
    // `konst`'s body (the name `P`) with no trace of `Prop`, and must
    // no longer be an application.
    let reduced : Term := whnf idt_scope empty_locals (Term.app (free_var "konst") (Term.type_ 0)) in
    match reduced {
        Term.app _ _ => false,
        _ => Similar.similar reduced (free_var "P"),
    }

#[test]
def test_whnf_unknown_name_is_stuck : Bool :=
    let t : Term := free_var "no_such_def" in
    Similar.similar (whnf idt_scope empty_locals t) t

// --- delta must not unfold a shadowed name ---

#[test]
def test_whnf_local_binding_shadows_global : Bool :=
    // `locals_with_def_typevars` skolemises implicit type parameters
    // into NAMED locals that resolve through the same path as globals.
    // A local `idt` must stay stuck, not unfold into the global `idt`'s
    // unrelated body.
    let lv : LocalVar := {
        name := Identifier.id "idt",
        typ := Term.type_ 1,
        multiplicity := Multiplicity.many,
    } in
    let locals : LocalScope := {
        vars := List.cons lv List.empty,
        parent := Option.none,
    } in
    let t : Term := free_var "idt" in
    Similar.similar (whnf idt_scope locals t) t

// --- rigid heads are already in WHNF ---

#[test]
def test_whnf_sort_unchanged : Bool :=
    Similar.similar (whnf idt_scope empty_locals (Term.type_ 1)) (Term.type_ 1)

#[test]
def test_whnf_pi_unchanged : Bool :=
    // A `pi` is rigid even though its parts contain a reducible term:
    // WHNF reduces the HEAD only, never inside.
    let p : Term := Term.pi (Term.app (free_var "idt") (Term.type_ 0)) (Term.type_ 1) in
    Similar.similar (whnf idt_scope empty_locals p) p

#[test]
def test_whnf_bound_var_unchanged : Bool :=
    let t : Term := Term.var 0 dbg_x in
    Similar.similar (whnf idt_scope empty_locals t) t

#[test]
def test_whnf_stuck_application_keeps_reduced_head : Bool :=
    // Head is an unknown name, so the application cannot fire -- but it
    // must come back as an application, not collapse to something else.
    match whnf idt_scope empty_locals (Term.app (free_var "no_such_def") (Term.type_ 0)) {
        Term.app _ _ => true,
        _ => false,
    }

// --- located terms ---

#[test]
def test_whnf_peels_located_wrapper : Bool :=
    // A `Term.ctx` wrapper must not stop reduction dead. Reduction that
    // silently stopped here would be the quiet kind of wrong: the
    // comparison would just report a mismatch as before.
    let loc : Location := { offset := 0, line := 1, column := 1 } in
    let wrapped : Term := Term.ctx loc (Term.app (free_var "idt") (Term.type_ 0)) in
    Similar.similar (whnf idt_scope empty_locals wrapped) (Term.type_ 0)

// --- divergence is bounded ---

#[test]
def test_whnf_recursive_def_terminates_on_fuel : Bool :=
    // `loop` unfolds to a body that calls `loop` again, forever. The
    // self-hosted compiler has no termination checker, so fuel is the
    // only thing standing between conversion checking and a hung
    // compiler. Reaching the assertion at all IS the assertion.
    let s : Scope := scope_of "def loop (x : Type) : Type := loop x" in
    let t : Term := Term.app (free_var "loop") (Term.type_ 1) in
    let reduced : Term := whnf s empty_locals t in
    match reduced {
        Term.hole => false,
        _ => true,
    }

// ─── iota ─────────────────────────────────────────────────────────────
//
// A `match`/`if` reduces only when its scrutinee has already reduced to
// a KNOWN constructor application. In this checker a constructor
// application is a FREE-VAR application spine (`Two2.mk2 P.p0 Q.q0`) --
// the parser never builds `Term.con` (see `type_check_con`'s own doc
// comment, lang/typecheck/infer.mo) -- so these tests spell scrutinees
// exactly the way production terms spell them, and the constructor's
// own simple name (`mk2`, the last dotted segment) is what a case's
// pattern name is compared against, the same convention match lowering
// (`find_case_for_ctor`, lang/lower_core_ir.mo) already relies on.

def iota_scope : Scope :=
    scope_of "type Bool { true, false }\ntype P { p0, p1 }\ntype Q { q0 }\ntype Two2 { mk2 (fst : P) (snd : Q) }"

/// One positional match arm: constructor name, pattern binders, body.
/// `field_pattern` is `Option.none` -- what every ELABORATED case
/// carries (the checker clears it once the real constructor is known).
def mc (con : String) (binders : List Identifier) (body : Term) : MatchCase :=
    MatchCase.mc (Identifier.id con) binders body Option.none

def id_a : Identifier := Identifier.id "a"
def id_b : Identifier := Identifier.id "b"

/// `Two2.mk2 P.p0 Q.q0` as the parser spells it.
def two_full : Term := Term.app (Term.app (free_var "Two2.mk2") (free_var "P.p0")) (free_var "Q.q0")

#[test]
def test_whnf_iota_match_known_constructor : Bool :=
    // `match P.p0 { p0 => Q, p1 => P }` fires the first arm.
    let c0 : MatchCase := mc "p0" List.empty (free_var "Q") in
    let c1 : MatchCase := mc "p1" List.empty (free_var "P") in
    let m : Term := Term.lit (Literal.match_ (free_var "P.p0") (List.cons c0 (List.cons c1 List.empty))) in
    Similar.similar (whnf iota_scope empty_locals m) (free_var "Q")

#[test]
def test_whnf_iota_match_second_case : Bool :=
    // `match P.p1 { p0 => Q, p1 => P }` fires the SECOND arm -- the
    // scan must not stop at the first case just because it exists.
    let c0 : MatchCase := mc "p0" List.empty (free_var "Q") in
    let c1 : MatchCase := mc "p1" List.empty (free_var "P") in
    let m : Term := Term.lit (Literal.match_ (free_var "P.p1") (List.cons c0 (List.cons c1 List.empty))) in
    Similar.similar (whnf iota_scope empty_locals m) (free_var "P")

#[test]
def test_whnf_iota_wildcard_fires_when_no_named_case_matches : Bool :=
    // `match P.p1 { p0 => Q, _ => P }` falls through to the wildcard,
    // the same choice the runtime's tag-indexed dispatch makes
    // (`lower_one_match_arm`, lang/lower_core_ir.mo).
    let c0 : MatchCase := mc "p0" List.empty (free_var "Q") in
    let cw : MatchCase := mc "_" List.empty (free_var "P") in
    let m : Term := Term.lit (Literal.match_ (free_var "P.p1") (List.cons c0 (List.cons cw List.empty))) in
    Similar.similar (whnf iota_scope empty_locals m) (free_var "P")

#[test]
def test_whnf_iota_stuck_on_variable_scrutinee : Bool :=
    // `match x { p0 => Q }` with `x` a BOUND variable has no
    // constructor to dispatch on. It must come back as a match (with
    // the scrutinee still reduced, but here already rigid), not
    // collapse -- and NOT fire the arm by accident.
    let c0 : MatchCase := mc "p0" List.empty (free_var "Q") in
    let m : Term := Term.lit (Literal.match_ (Term.var 0 dbg_x) (List.cons c0 List.empty)) in
    match whnf iota_scope empty_locals m {
        Term.lit _ => true,
        _ => false,
    }

#[test]
def test_whnf_iota_substitutes_second_field : Bool :=
    // The acid test for binder ORDER: `Two2.mk2`'s second field is the
    // INNERMOST pattern binder (`b`, de Bruijn 0 in the arm body), and
    // its value is the SECOND spine argument (`Q.q0`). A substitution
    // that peels binders in the wrong direction silently yields
    // `P.p0` here instead.
    let body : Term := Term.var 0 (DebugName.named id_b) in
    let case_ : MatchCase := mc "mk2" (List.cons id_a (List.cons id_b List.empty)) body in
    let m : Term := Term.lit (Literal.match_ two_full (List.cons case_ List.empty)) in
    Similar.similar (whnf iota_scope empty_locals m) (free_var "Q.q0")

#[test]
def test_whnf_iota_substitutes_first_field : Bool :=
    // The other half of the order contract: the FIRST field is the
    // OUTERMOST binder (`a`, de Bruijn 1 here), substituted first with
    // the argument shifted up past the still-present inner binder. A
    // substitution that forgets the shift lands `P.p0` one level off
    // and this catches it.
    let body : Term := Term.var 1 (DebugName.named id_a) in
    let case_ : MatchCase := mc "mk2" (List.cons id_a (List.cons id_b List.empty)) body in
    let m : Term := Term.lit (Literal.match_ two_full (List.cons case_ List.empty)) in
    Similar.similar (whnf iota_scope empty_locals m) (free_var "P.p0")

#[test]
def test_whnf_iota_substitutes_into_nested_match_body : Bool :=
    // The outer arm's body is itself a match whose own arm body
    // references the outer arm's FIRST binder (`a`, index 1 from the
    // inside: the outer `b` sits at 0). Firing the outer match must
    // substitute THROUGH the inner match's binding form (its zero
    // binders here, but the walk still has to cross it -- AGENTS.md
    // item 22), and the inner match must then fire too.
    let inner_body : Term := Term.var 1 (DebugName.named id_a) in
    let inner_case : MatchCase := mc "p0" List.empty inner_body in
    let inner : Term := Term.lit (Literal.match_ (free_var "P.p0") (List.cons inner_case List.empty)) in
    let outer_case : MatchCase := mc "mk2" (List.cons id_a (List.cons id_b List.empty)) inner in
    let m : Term := Term.lit (Literal.match_ two_full (List.cons outer_case List.empty)) in
    Similar.similar (whnf iota_scope empty_locals m) (free_var "P.p0")

#[test]
def test_whnf_iota_stuck_on_arity_mismatch : Bool :=
    // A hand-built ill-typed match (case binds one binder, the
    // constructor has two fields) must stay STUCK, not substitute
    // binders against the wrong arguments -- reduction only ever
    // widens what a sound checker accepts, never invents answers for
    // terms the checker would have rejected.
    let case_ : MatchCase := mc "mk2" (List.cons id_a List.empty) (Term.var 0 (DebugName.named id_a)) in
    let m : Term := Term.lit (Literal.match_ two_full (List.cons case_ List.empty)) in
    match whnf iota_scope empty_locals m {
        Term.lit _ => true,
        _ => false,
    }

#[test]
def test_whnf_iota_stuck_on_partial_application : Bool :=
    // `Two2.mk2 P.p0` is a PARTIAL constructor application -- one field
    // short of anything an arm could project. Iota has no constructor
    // to fire on and must leave the match alone.
    let partial : Term := Term.app (free_var "Two2.mk2") (free_var "P.p0") in
    let body : Term := Term.var 0 (DebugName.named id_b) in
    let case_ : MatchCase := mc "mk2" (List.cons id_a (List.cons id_b List.empty)) body in
    let m : Term := Term.lit (Literal.match_ partial (List.cons case_ List.empty)) in
    match whnf iota_scope empty_locals m {
        Term.lit _ => true,
        _ => false,
    }

#[test]
def test_whnf_iota_stuck_on_non_constructor_head : Bool :=
    // `no_such_def P.p0` has a stuck head that merely SHARES a case's
    // name shape -- but `no_such_def` names no constructor, so no arm
    // fires. This is the guard that keeps iota from firing on any
    // stuck application whose head happens to be spelled like a case.
    let scrut : Term := Term.app (free_var "no_such_def") (free_var "P.p0") in
    let case_ : MatchCase := mc "no_such_def" List.empty (free_var "Q") in
    let m : Term := Term.lit (Literal.match_ scrut (List.cons case_ List.empty)) in
    match whnf iota_scope empty_locals m {
        Term.lit _ => true,
        _ => false,
    }

#[test]
def test_whnf_iota_if_true : Bool :=
    // `if true then Q else P` -- the condition reduces to Bool's
    // `true` constructor, so the whole `if` reduces to its then-branch.
    let i : Term := Term.lit (Literal.if_ (free_var "true") (free_var "Q") (free_var "P")) in
    Similar.similar (whnf iota_scope empty_locals i) (free_var "Q")

#[test]
def test_whnf_iota_if_false : Bool :=
    let i : Term := Term.lit (Literal.if_ (free_var "false") (free_var "Q") (free_var "P")) in
    Similar.similar (whnf iota_scope empty_locals i) (free_var "P")

#[test]
def test_whnf_iota_if_stuck_on_variable_condition : Bool :=
    // `if x then Q else P` with `x` bound: no constructor, no
    // reduction. Must stay an `if` (a `Term.lit`), not pick a branch.
    let i : Term := Term.lit (Literal.if_ (Term.var 0 dbg_x) (free_var "Q") (free_var "P")) in
    match whnf iota_scope empty_locals i {
        Term.lit _ => true,
        _ => false,
    }

#[test]
def test_whnf_iota_reduces_scrutinee_first : Bool :=
    // The scrutinee must be REDUCED before dispatch, not matched
    // syntactically: here it is written as an application of the
    // delta-reducible `konst` rather than as the constructor spelling
    // itself. (`konst` is `def konst (x : Type) : Type := P.p0`-shaped:
    // its body is the constructor reference the match fires on.)
    let s : Scope := scope_of "type P { p0 }\ndef konst (x : Type) : Type := P.p0" in
    let scrut : Term := Term.app (free_var "konst") (Term.type_ 1) in
    let case_ : MatchCase := mc "p0" List.empty (free_var "P") in
    let m : Term := Term.lit (Literal.match_ scrut (List.cons case_ List.empty)) in
    Similar.similar (whnf s empty_locals m) (free_var "P")

#[test]
def test_whnf_iota_iota_chain_terminates_on_fuel : Bool :=
    // `spin` reduces to a match that fires into another call of `spin`
    // -- an iota chain with no end, the match-flavoured sibling of
    // `test_whnf_recursive_def_terminates_on_fuel` above. Fuel bounds
    // it; reaching the assertion at all IS the assertion.
    let s : Scope :=
        scope_of "type P { p0, p1 }\ndef spin (x : P) : P := match x { P.p0 => spin P.p1, P.p1 => spin P.p0 }" in
    let t : Term := Term.app (free_var "spin") (free_var "P.p0") in
    let reduced : Term := whnf s empty_locals t in
    match reduced {
        Term.hole => false,
        _ => true,
    }
