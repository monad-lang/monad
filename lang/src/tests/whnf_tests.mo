use lib::types {
  DebugName, Location, LocalScope, LocalVar, ModulePath, Scope, ScopeData,
  Similar, Term, id, mp, named, sentinel,
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
