// Pins for `lang/src/typecheck/ctor_refine.mo`: constructor index inversion.
//
// The scope comes from real parsed source (`try_parse_decls` +
// `build_scope_from_decls`, as `elim_lower_tests.mo` does), so the inductive's
// params, constructor return types and constructor registry are the real ones.
// `N`/`V` are a private Nat/Vec so the pins do not depend on the prelude.

use std::list {}
use lang::types {
    DebugName, Identifier, InductConstructor, Inductive, ModulePath, NamePath, Scope,
    ScopeData, Similar, Term, sentinel,
}
use lib::module {try_parse_decls}
use lib::scope {build_scope_from_decls, find_constructor_in_inductive, scope_find_inductive}
use lib::typecheck::ctor_refine {
    IndexMatch, IndexSolution, MatchEnv, empty_solution, index_positions, intro_clash, intro_ctor,
    intro_indices, nat_literal_term, refine_expected, refine_field_types, solve_ctor,
}

def ctor_refine_test_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "ctor_refine_tests") List.empty)

def source : String :=
    "type N { z, s (p : N) }\n"
        ++ "type V (len : N) A { vnil : V N.z A, vcons (head : A) (tail : V len A) : V (N.s len) A }\n"
        ++ "type Opt A { sm (a : A), nn }\n"

def scope_ : Scope :=
    let sd : ScopeData :=
        match try_parse_decls source {
            Option.some decl_list => build_scope_from_decls ctor_refine_test_path decl_list,
            Option.none => build_scope_from_decls ctor_refine_test_path List.empty,
        } in
    {
        module_id := ctor_refine_test_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
    }

def np (name : String) : NamePath := NamePath.mk (List.cons (Identifier.id name) List.empty)

def named (name : String) : Term := Term.var sentinel (DebugName.named (Identifier.id name))

def app2 (f : Term) (a : Term) (b : Term) : Term := Term.app (Term.app f a) b

def ind_of (name : String) : Option Inductive :=
    match scope_find_inductive (np name) scope_ {
        Result.ok ind => Option.some ind,
        Result.err _ => Option.none,
    }

def env_ : MatchEnv := {
    locals := List.cons (Identifier.id "len") List.empty,
    binders := List.cons (Identifier.id "m") List.empty,
    scope := scope_,
    skolem_suffix := "7",
}

/// `V <index> T`.
def v_of (index : Term) : Term := app2 (named "V") index (named "T")

def succ_of (t : Term) : Term := Term.app (named "N.s") t

/// Solve constructor `ctor` of `V` against `sc_typ`.
def solve_v (ctor : String) (sc_typ : Term) : Option IndexMatch :=
    match ind_of "V" {
        Option.none => Option.none,
        Option.some ind =>
            match find_constructor_in_inductive ind (np ctor) {
                Option.none => Option.none,
                Option.some c => Option.some (solve_ctor env_ ind c sc_typ),
            },
    }

def is_impossible (m : Option IndexMatch) : Bool :=
    match m {
        Option.some r => match r { IndexMatch.impossible => true, _ => false },
        Option.none => false,
    }

def is_unknown (m : Option IndexMatch) : Bool :=
    match m {
        Option.some r => match r { IndexMatch.unknown => true, _ => false },
        Option.none => false,
    }

def solution_of (m : Option IndexMatch) : Option IndexSolution :=
    match m {
        Option.some r => match r { IndexMatch.solved s => Option.some s, _ => Option.none },
        Option.none => Option.none,
    }

def subst_is (s : IndexSolution) (name : String) (expected : Term) : Bool :=
    match s.subst {
        List.cons b rest =>
            match b {
                Pair.pair x v =>
                    List.is_empty rest && Similar.similar x (Identifier.id name) && Similar.similar v expected,
            },
        List.empty => false,
    }

def refine_is (s : IndexSolution) (k : I64) (expected : Term) : Bool :=
    match s.refine {
        List.cons r rest =>
            match r {
                Pair.pair j v => List.is_empty rest && I64.beq j k && Similar.similar v expected,
            },
        List.empty => false,
    }

#[terminating]
def terms_similar (xs : List Term) (ys : List Term) : Bool :=
    match xs {
        List.empty => List.is_empty ys,
        List.cons x xrest =>
            match ys {
                List.empty => false,
                List.cons y yrest => Similar.similar x y && terms_similar xrest yrest,
            },
    }

def refining (k : I64) (t : Term) : IndexSolution :=
    { empty_solution with refine := List.cons (Pair.pair k t) List.empty }

// --- Index positions -------------------------------------------------------

#[test]
def test_vec_len_is_an_index_position : Bool :=
    match ind_of "V" {
        Option.some ind => match index_positions ind {
            List.cons i rest => I64.beq i 0 && List.is_empty rest,
            List.empty => false,
        },
        Option.none => false,
    }

#[test]
def test_a_uniform_family_has_no_index_positions : Bool :=
    match ind_of "Opt" {
        Option.some ind => List.is_empty (index_positions ind),
        Option.none => false,
    }

// --- Solving ---------------------------------------------------------------

#[test]
def test_cons_against_a_successor_index_solves_len : Bool :=
    match solution_of (solve_v "vcons" (v_of (succ_of (Term.var 3 DebugName.unnamed)))) {
        Option.some s => subst_is s "len" (Term.var 3 DebugName.unnamed) && List.is_empty s.refine,
        Option.none => false,
    }

#[test]
def test_cons_against_a_zero_index_is_impossible : Bool :=
    is_impossible (solve_v "vcons" (v_of (named "N.z")))

#[test]
def test_nil_against_a_successor_index_is_impossible : Bool :=
    is_impossible (solve_v "vnil" (v_of (succ_of (named "n"))))

#[test]
def test_nil_against_a_zero_index_is_solved : Bool :=
    match solution_of (solve_v "vnil" (v_of (named "z"))) {
        Option.some s => List.is_empty s.subst && List.is_empty s.refine,
        Option.none => false,
    }

#[test]
def test_cons_against_a_bound_index_refines_it_with_a_skolem : Bool :=
    match solution_of (solve_v "vcons" (v_of (Term.var 2 DebugName.unnamed))) {
        Option.some s =>
            subst_is s "len" (named "len@7")
                && refine_is s 2 (succ_of (named "len@7")),
        Option.none => false,
    }

#[test]
def test_cons_against_an_opaque_free_index_is_unknown : Bool :=
    is_unknown (solve_v "vcons" (v_of (named "n")))

// --- Applying a solution -----------------------------------------------------

#[test]
def test_cons_field_types_use_the_solved_length : Bool :=
    let sc : Term := v_of (succ_of (Term.var 3 DebugName.unnamed)) in
    match ind_of "V" {
        Option.none => false,
        Option.some ind =>
            match solution_of (solve_v "vcons" sc) {
                Option.none => false,
                Option.some s =>
                    let tail_typ : Term := app2 (named "V") (named "len") (named "A") in
                    let fields : List Term := List.cons (named "A") (List.cons tail_typ List.empty) in
                    terms_similar (refine_field_types ind sc s fields)
                        (List.cons (named "T") (List.cons (v_of (Term.var 3 DebugName.unnamed)) List.empty)),
            },
    }

#[test]
def test_refine_expected_replaces_the_bound_index : Bool :=
    Similar.similar
        (refine_expected (refining 0 (named "N.z")) (v_of (Term.var 0 DebugName.unnamed)))
        (v_of (named "N.z"))

#[test]
def test_refine_expected_keeps_other_bound_variables : Bool :=
    let before : Term := app2 (named "V") (Term.var 1 DebugName.unnamed) (Term.var 0 DebugName.unnamed) in
    Similar.similar
        (refine_expected (refining 1 (named "N.z")) before)
        (app2 (named "V") (named "N.z") (Term.var 0 DebugName.unnamed))

#[test]
def test_cons_against_a_named_local_index_refines_it_by_name : Bool :=
    match solution_of (solve_v "vcons" (v_of (named "m"))) {
        Option.some s =>
            subst_is s "len" (named "len@7")
                && List.is_empty s.refine
                && Similar.similar (refine_expected s (v_of (named "m"))) (v_of (succ_of (named "len@7"))),
        Option.none => false,
    }

// --- Introduction (Stage 3c) -----------------------------------------------

def vnil_ : Term := named "V.vnil"

def vcons_ (x : Term) (tail : Term) : Term := app2 (named "V.vcons") x tail

def no_types (t : Term) : Option Term := Option.none

/// `t : V N.z T` for bound variable 0; nothing else is typed.
def tail_typed (t : Term) : Option Term :=
    match t {
        Term.var k _dbg => if I64.beq k 0 then Option.some (v_of (named "N.z")) else Option.none,
        _ => Option.none,
    }

def indices_of (t : Term) : Option (List Term) :=
    match intro_ctor scope_ t {
        Option.some ic => intro_indices scope_ no_types ic,
        Option.none => Option.none,
    }

def clashes (arg_type : Term -> Option Term) (t : Term) (expected : Term) : Bool :=
    match intro_ctor scope_ t {
        Option.some ic =>
            match intro_clash scope_ arg_type ic expected {
                Option.some _ => true,
                Option.none => false,
            },
        Option.none => false,
    }

#[test]
def test_a_nested_constructor_application_computes_its_length : Bool :=
    match indices_of (vcons_ (named "x") (vcons_ (named "y") vnil_)) {
        Option.some idx => terms_similar idx [succ_of (succ_of (named "N.z"))],
        Option.none => false,
    }

#[test]
def test_an_untyped_tail_leaves_the_length_unknown : Bool :=
    match indices_of (vcons_ (named "x") (named "t")) {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_nil_clashes_with_a_successor_length : Bool :=
    clashes no_types vnil_ (v_of (succ_of (named "N.z")))

#[test]
def test_cons_of_nil_fits_length_one : Bool :=
    Bool.not (clashes no_types (vcons_ (named "x") vnil_) (v_of (succ_of (named "N.z"))))

#[test]
def test_a_typed_tail_supplies_the_length_that_clashes : Bool :=
    clashes tail_typed (vcons_ (named "x") (Term.var 0 DebugName.unnamed)) (v_of (named "N.z"))

#[test]
def test_a_variable_expected_length_never_clashes : Bool :=
    Bool.not (clashes no_types vnil_ (v_of (named "m")))

#[test]
def test_a_nat_literal_unfolds_to_a_constructor_chain : Bool :=
    Similar.similar (nat_literal_term 2)
        (Term.app (named "Nat.succ") (Term.app (named "Nat.succ") (named "Nat.zero")))
