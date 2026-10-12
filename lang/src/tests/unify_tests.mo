use lang::types {
  Decl, Def, LocalScope, Location, ModulePath, Scope, Term, TypeError, app,
  binder_anon, binder_binder, binder_is_explicit, concrete, hole, id, lit, named,
  pi, result_is_ok, sentinel, sort_n, str, term_loc, unnamed, var,
  cub, i0, i1,
}
use lib::typecheck::unify {unify}
use lib::typecheck::infer {type_check}
use lib::scope {build_scope_from_decls}
use lib::parser {decls_parser_located}

/// An empty scope/locals pair. Every test below compares terms that
/// need no delta reduction, so there is nothing for `unify` to look up
/// -- conversion checking against a populated scope is exercised in
/// `whnf_tests.mo` and end-to-end in `typecheck_examples_tests.mo`.
def test_scope : Scope := {
    module_id := ModulePath.mk List.empty,
    scope := build_scope_from_decls (ModulePath.mk List.empty) List.empty,
    parent := Option.none,
    incomplete_match_ok := false,
}

def test_locals : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

def run_unify (a : Term) (b : Term) : Bool :=
    result_is_ok (unify a b test_scope test_locals)

// --- Hole tests ---

#[test]
def test_unify_hole_left : Bool :=
    run_unify Term.hole (sort_n 1)

#[test]
def test_unify_hole_right : Bool :=
    run_unify (sort_n 1) Term.hole

#[test]
def test_unify_hole_hole : Bool :=
    run_unify Term.hole Term.hole

// --- Sort tests ---

#[test]
def test_unify_sort_same : Bool :=
    run_unify (sort_n 1) (sort_n 1)

#[test]
def test_unify_sort_cumulativity : Bool :=
    run_unify (sort_n 0) (sort_n 1)

#[test]
def test_unify_sort_too_small : Bool :=
    let ok : Bool := run_unify (sort_n 1) (sort_n 0) in
    Bool.not ok

// --- Pi tests ---

#[test]
def test_unify_pi_same : Bool :=
    let p1 : Term := Term.pi binder_anon (sort_n 1) (sort_n 1) in
    let p2 : Term := Term.pi binder_anon (sort_n 1) (sort_n 1) in
    run_unify p1 p2

#[test]
def test_unify_pi_arg_mismatch : Bool :=
    let p1 : Term := Term.pi binder_anon (sort_n 2) (sort_n 1) in
    let p2 : Term := Term.pi binder_anon (sort_n 0) (sort_n 1) in
    let ok : Bool := run_unify p1 p2 in
    Bool.not ok

#[test]
def test_unify_pi_ret_mismatch : Bool :=
    let p1 : Term := Term.pi binder_anon (sort_n 1) (sort_n 2) in
    let p2 : Term := Term.pi binder_anon (sort_n 1) (sort_n 0) in
    let ok : Bool := run_unify p1 p2 in
    Bool.not ok

#[test]
def test_unify_pi_vs_sort : Bool :=
    let p : Term := Term.pi binder_anon (sort_n 1) (sort_n 1) in
    let ok : Bool := run_unify p (sort_n 1) in
    Bool.not ok

// --- Quantifier tests ---
//
// A quantifier binder is TRANSPARENT to `unify`: stripped and retried, on
// either side. Before R2b these were built with `Term.forall`; the binder
// tag is what says so now, and these two pins are what says the stripping
// still happens on the constructor it moved to.

#[test]
def test_unify_quantifier_stripped : Bool :=
    let body : Term := sort_n 1 in
    let f : Term := Term.pi (binder_binder (Identifier.id "A")) (sort_n 1) body in
    run_unify f (sort_n 1)

#[test]
def test_unify_quantifier_both_sides : Bool :=
    let body_left : Term := Term.pi binder_anon (sort_n 1) (sort_n 1) in
    let f_left : Term := Term.pi (binder_binder (Identifier.id "A")) (sort_n 1) body_left in
    let body_right : Term := Term.pi binder_anon (sort_n 1) (sort_n 1) in
    let f_right : Term := Term.pi (binder_binder (Identifier.id "B")) (sort_n 1) body_right in
    run_unify f_left f_right

// --- Literal / structural mismatch ---

#[test]
def test_unify_lit_vs_type : Bool :=
    let lit : Term := Term.lit (Literal.str "hello") in
    let ok : Bool := run_unify lit (sort_n 1) in
    Bool.not ok

#[test]
def test_unify_var_vs_different_var : Bool :=
    let v1 : Term := Term.var 0 (DebugName.named (Identifier.id "x")) in
    let v2 : Term := Term.var 1 (DebugName.named (Identifier.id "y")) in
    let ok : Bool := run_unify v1 v2 in
    Bool.not ok

// --- Combined structures ---

#[test]
def test_unify_nested_pi : Bool :=
    let arg : Term := sort_n 1 in
    let inner_ret : Term := sort_n 1 in
    let outer_ret : Term := Term.pi binder_anon arg inner_ret in
    let p1 : Term := Term.pi binder_anon arg outer_ret in
    let p2 : Term := Term.pi binder_anon arg outer_ret in
    run_unify p1 p2

// --- App tests (no deep structural matching for apps yet) ---

#[test]
def test_unify_app_same : Bool :=
    let f : Term := Term.var 0 (DebugName.unnamed) in
    let a : Term := sort_n 1 in
    let app1 : Term := Term.app f a in
    run_unify app1 app1

#[test]
def test_unify_app_different : Bool :=
    let app1 : Term := Term.app (sort_n 1) (sort_n 1) in
    let app2 : Term := Term.app (sort_n 0) (sort_n 1) in
    let ok : Bool := run_unify app1 app2 in
    Bool.not ok

// --- conversion checking (definitional equality) ---
//
// `unify` compares structurally first and only reduces when that has
// already failed, so these are the cases that used to be reported as
// mismatches purely on spelling.

use lib::module {parse_all_decls}
use parsec::core {fail, success}

def conv_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "conv") List.empty)

/// `idt` is the identity on types, `konst` ignores its argument.
def conv_scope : Scope :=
    let src : String := "type P { p0 }\ndef idt (x : Type) : Type := x\ndef konst (x : Type) : Type := P" in
    {
        module_id := conv_path,
        scope :=
            match parse_all_decls src {
                success _ decl_list => build_scope_from_decls conv_path decl_list,
                fail _ => build_scope_from_decls conv_path List.empty,
            },
        parent := Option.none,
        incomplete_match_ok := false,
    }

def run_unify_conv (a : Term) (b : Term) : Bool :=
    result_is_ok (unify a b conv_scope test_locals)

def conv_free (nm : String) : Term := Term.var sentinel (DebugName.named (Identifier.id nm))

#[test]
def test_unify_reduces_application_to_match : Bool :=
    // `idt Prop` reduces to `Prop`; structurally they are an `app` and
    // a `type_`, which never matched before.
    run_unify_conv (Term.app (conv_free "idt") (sort_n 0)) (sort_n 0)

#[test]
def test_unify_reduces_application_on_either_side : Bool :=
    run_unify_conv (sort_n 0) (Term.app (conv_free "idt") (sort_n 0))

#[test]
def test_unify_reduces_both_sides : Bool :=
    // Two differently-spelled applications that reduce alike: `konst
    // Prop` discards its argument and yields `P`, and `idt P` yields
    // its argument, also `P`. Neither side is structurally anything
    // like the other.
    run_unify_conv (Term.app (conv_free "konst") (sort_n 0))
                   (Term.app (conv_free "idt") (conv_free "P"))

#[test]
def test_unify_still_rejects_when_reduction_disagrees : Bool :=
    // `idt Prop` reduces to `Prop` (sort 0), not `Type` (sort 1). The
    // retry must not turn every mismatch into a match.
    not (run_unify_conv (Term.app (conv_free "idt") (sort_n 1)) (sort_n 0))

#[test]
def test_unify_still_rejects_irreducible_mismatch : Bool :=
    // Neither side reduces at all -- the early-out path in
    // `unify_stuck`.
    not (run_unify_conv (conv_free "no_such_a") (conv_free "no_such_b"))

// --- Level variables ---
//
// `unify` routes every sort to `unify_sort` before the
// structural `Similar.similar` fallback ever runs, so a sort's
// reflexivity is decided by `level_le` (`lang/types.mo`) and by nothing
// else. These two pin the pair of answers that relation has to give.

/// REFLEXIVITY. `Sort u` unifies with `Sort u` -- `u <= u` holds under
/// every valuation, so this is not a guess. It failed before `level_le`
/// grew its `level_eq` arm: `level_const` has no number for a variable,
/// so the concrete comparison refused, and a universe-polymorphic
/// signature could not be compared against itself.
#[test]
def test_unify_same_level_var_is_reflexive : Bool :=
    run_unify (Term.sort (SortLevel.var (Identifier.id "u")))
              (Term.sort (SortLevel.var (Identifier.id "u")))

/// ...and two DIFFERENT level variables still do not, which is what
/// keeps the arm above from being a blanket "any unresolved level
/// matches". Nothing has determined that `u <= v`, so refusing is the
/// sound direction; W1.5's normalizing comparison is what will resolve
/// these structurally.
#[test]
def test_unify_distinct_level_vars_still_refuse : Bool :=
    not (run_unify (Term.sort (SortLevel.var (Identifier.id "u")))
                   (Term.sort (SortLevel.var (Identifier.id "v"))))

/// Reflexivity reaches UNDER a binder too: `unify_go`'s `Term.pi` arm
/// recurses through `unify`, so a Pi over a level variable is compared
/// component-wise and each component meets the same relation.
#[test]
def test_unify_pi_over_a_level_var_is_reflexive : Bool :=
    let s : Term := Term.sort (SortLevel.var (Identifier.id "u")) in
    run_unify (Term.pi binder_anon s s) (Term.pi binder_anon s s)

// --- Probes: does a `Term.ctx` wrapper reach a `TypeError` payload? ---
//
// The LSP needs a source range for every diagnostic, and `Term.ctx` is the
// only span carrier in the tree. `lang/src/module.mo`'s `parse_all_decls`
// (:118) puts one on EVERY path -- see its doc block, which explains that
// locating on every path is deliberate, so that "the 1467-test corpus
// exercises wrapper transparency continuously". So the question is not
// whether wrappers reach the CHECKER (they do, on every run), but whether
// they survive into the ERROR the checker reports.
//
// These probes measure that rather than infer it. Reading says no, and
// uniformly, for a structural reason worth recording beside the
// measurement:
//
//   * `unify` peels BOTH operands at entry (`unify.mo:49`), and every
//     recursive descent in `unify_go` calls `unify` again rather than
//     `unify_go` (`unify.mo:90`, `:92`, `:95`, `:103`). So a NESTED
//     comparison re-peels too, and both live `mismatch` sites
//     (`unify.mo:133`, `:159`, `:163`) are reached with peeled operands.
//   * `not_a_type` is bare for a different reason: `type_check`'s `ctx`
//     arm strips the wrapper into `type_check_located` BEFORE dispatching
//     (`infer.mo:99`), which discards it again on failure
//     (`infer.mo:107` -- `err e => err e`), and `kind_wants_loc(sort)`
//     is `false` besides (`lang/src/parser/lower_parse.mo:445`).
//   * `not_a_function` and `infinite_type` are not constructed anywhere in
//     the tree -- they appear only at their declaration and their
//     rendering arms (`lang/src/typecheck/diagnostic.mo:50`, `:54`). The
//     live payload-bearing variants are exactly `mismatch` and
//     `not_a_type`.
//
// The constructive half is the last probe: a def's body DOES land on a
// `Term.ctx` after its binders are stripped, which is what a per-def range
// will be built on regardless of how the payload question is answered.
//
// These tests assert the OBSERVED behaviour, so they document the current
// state and flip if it changes -- the same idiom as
// `test_plain_parser_records_nothing` (`lang/src/parser.mo:4660`).

/// Was this a payload-bearing variant at all? A two-way `Option Location`
/// cannot answer that, and the distinction is load-bearing here: its
/// `none` would mean both "the term was unwrapped" and "this error never
/// had a term". Every probe below would then pass on a `TypeError.custom`
/// -- which carries no term and so could never carry a location -- and the
/// measurement would be vacuous. The probes therefore require a
/// payload-bearing variant AND an absent location.
def probe_payload_variant (e : TypeError) : Bool := match e {
    TypeError.mismatch _a _b => true,
    TypeError.not_a_type _t => true,
    TypeError.not_a_function _t => true,
    TypeError.infinite_type _t => true,
    _ => false,
}

/// The term a payload-bearing `TypeError` carries, if any. `mismatch`
/// carries two; this returns the left operand.
def probe_payload_term (e : TypeError) : Option Term := match e {
    TypeError.mismatch a _b => Option.some a,
    TypeError.not_a_type t => Option.some t,
    TypeError.not_a_function t => Option.some t,
    TypeError.infinite_type t => Option.some t,
    _ => Option.none,
}

/// The location a `TypeError` payload carries, if any.
def probe_payload_loc (e : TypeError) : Option Location := match e {
    TypeError.mismatch a _b => term_loc a,
    TypeError.not_a_type t => term_loc t,
    TypeError.not_a_function t => term_loc t,
    TypeError.infinite_type t => term_loc t,
    _ => Option.none,
}

/// A wrapper handed straight to `type_check`. This isolates
/// `type_check_located`'s `err` arm, which drops the location.
#[test]
def test_probe_ctx_does_not_reach_a_sort_payload : Bool :=
    let loc : Location := { offset := 0, line := 7, column := 3 } in
    let wrapped : Term := Term.ctx loc (Term.sort (SortLevel.concrete 3)) in
    match type_check wrapped (sort_n 1) test_scope List.empty test_locals {
        ok _ => false,
        err e => match probe_payload_loc e {
            Option.some _ => false,
            Option.none => probe_payload_variant e,
        },
    }

/// `unify` peels at entry, so a wrapped operand is gone by the time
/// `unify_sort` reports. Expected: the payload is unlocated.
#[test]
def test_probe_unify_peels_a_wrapped_operand : Bool :=
    let loc : Location := { offset := 0, line := 7, column := 3 } in
    let wrapped : Term := Term.ctx loc (Term.sort (SortLevel.concrete 1)) in
    match unify wrapped (sort_n 0) test_scope test_locals {
        ok _ => false,
        err e => match probe_payload_loc e {
            Option.some _ => false,
            Option.none => probe_payload_variant e,
        },
    }

/// The nested case, which is the one that would matter: a wrapper on a
/// SUBterm of an otherwise-unwrapped pair. `unify_go`'s `pi` arm recurses
/// through `unify` (`unify.mo:90`), which re-peels -- so this is unlocated
/// too. If this ever starts answering `some`, the LSP can take ranges off
/// the payload instead of the decl-span table.
#[test]
def test_probe_unify_peels_a_nested_operand : Bool :=
    let loc : Location := { offset := 0, line := 7, column := 3 } in
    let inner : Term := Term.ctx loc (Term.sort (SortLevel.concrete 1)) in
    let p_left : Term := Term.pi binder_anon inner (sort_n 1) in
    let p_right : Term := Term.pi binder_anon (sort_n 0) (sort_n 1) in
    match unify p_left p_right test_scope test_locals {
        ok _ => false,
        err e => match probe_payload_loc e {
            Option.some _ => false,
            Option.none => probe_payload_variant e,
        },
    }

/// Strip leading `lam`/`forall` binders but KEEP the `Term.ctx` they land
/// on -- the same rule `strip_db_lams` (`lang/src/codegen/validate.mo:457`,
/// "the term WITH its wrapper, not the peeled one ... peeling here would
/// silently discard it") and `dbg_loc_of_body`
/// (`lang/src/codegen/emit.mo:4476`) already rely on. Duplicated locally
/// rather than imported because those live in `lang.codegen`, which
/// depends on `lang.module` -- importing back is a cycle.
def probe_strip_binders (t : Term) : Term := match t {
    Term.lam _dbg _typ body => probe_strip_binders body,
    // R2b folded `Term.forall` into `Term.pi`: a quantifier is a non-explicit
    // binder, and an explicit one is the old `pi` catch-all -- unstripped.
    Term.pi b _dom body => if binder_is_explicit b then t else probe_strip_binders body,
    _ => t,
}

/// Typed accessor, not `loc.line` inline: a `#[test]`-reachable def that
/// reads a struct field directly gets the FIELD's LLVM type as its own
/// return type under the compiled self-hosted runner, which would silently
/// break this Bool. Only the compiled runner fails; the Rust host is fine.
/// Hence an accessor whose signature already says `I64`.
def probe_loc_line (l : Location) : I64 := l.line

/// Same remedy for `Def.term`: this def's declared return type IS the
/// field's type, so the field's LLVM type and the def's agree.
def probe_def_term (d : Def) : Term := d.term

def probe_first_def_body_loc (ds : List Decl) : Bool := match ds {
    List.empty => false,
    List.cons d _rest => match d {
        Decl.def_d def_ => match term_loc (probe_strip_binders (probe_def_term def_)) {
            Option.some loc => I64.beq (probe_loc_line loc) 2,
            Option.none => false,
        },
        _ => false,
    }
}

/// The CONSTRUCTIVE probe. This must pass: the located parse does put a
/// wrapper on a def's body, so a per-def range is obtainable today even
/// though no diagnostic payload carries one. The body is on line 2, not
/// line 1 -- the wrapper is the body expression, not the `def` header
/// (the same distinction `test_located_parser_records_a_position` pins at
/// `lang/src/parser.mo:4650`).
#[test]
def test_probe_def_body_lands_on_a_ctx : Bool :=
    match decls_parser_located "def f (x : I64) : I64 :=\n    x\n" {
        fail _e => false,
        success _rem ds => probe_first_def_body_loc ds,
    }

/// The asymmetry the three probes above do NOT settle, and the one crack
/// through which an expression-granular range could still be recovered
/// without a location-carrying `TypeError`: `term_peel` strips the outer
/// `ctx` CHAIN only, so a `mismatch` payload can have a BARE root and a
/// WRAPPED child at the same time. `term_loc` on the payload then answers
/// `none` while `term_loc` on the payload's child answers `some`.
///
/// The two operands are apps over distinct variables, so this reaches
/// `unify_stuck` (`unify.mo:150-165`) rather than reducing: apps have no
/// structural arm of their own, and neither side is reducible.
#[test]
def test_probe_a_child_wrapper_survives_the_peel : Bool :=
    let loc : Location := { offset := 0, line := 7, column := 3 } in
    let left : Term :=
        Term.app (Term.ctx loc (Term.var 0 (DebugName.unnamed)))
                 (Term.var 1 (DebugName.unnamed)) in
    let right : Term :=
        Term.app (Term.var 2 (DebugName.unnamed))
                 (Term.var 3 (DebugName.unnamed)) in
    match unify left right test_scope test_locals {
        ok _ => false,
        err e => match probe_payload_term e {
            Option.none => false,
            Option.some payload => match term_loc payload {
                // The root must be bare -- the peel did its job...
                Option.some _ => false,
                // ...while the child still carries its position.
                Option.none => match probe_child_loc payload {
                    Option.some _ => true,
                    Option.none => false,
                },
            },
        },
    }

/// The location the payload root's first child carries, if the root is an
/// app. Used only by the probe above.
def probe_child_loc (t : Term) : Option Location := match t {
    Term.app f _a => term_loc f,
    _ => Option.none,
}

// --- App spine congruence (P2) ---
//
// `unify_go` grew an `app`/`app` arm (plans/type-system/
// core-term-simplification.md). Before it, every application spine hit
// the catch-all: `Similar.similar`, then `unify_stuck` reducing the
// WHOLE spine weak-head -- which stops at a stuck head and never looks
// inside an argument. So `A (idt P)` vs `A P` failed on spelling while
// `idt P` vs `P` alone succeeds, and an argument hole failed the same
// way. These are the cases the arm exists for, and the head `A` below
// is a free variable on purpose: a def head would let the whole-spine
// path delta-reduce the head and hide the difference.
//
// Stage 2 makes this load-bearing rather than tidy: every boundary
// comparison in `PathP` has the shape `A i` with `A` a stuck line and
// `i` a dimension.

#[test]
def test_unify_app_argument_converts_under_a_stuck_head : Bool :=
    // THE pin. `A (idt P)` vs `A P`: the heads are identical, the
    // arguments convert by delta+beta -- and the whole spine is stuck
    // under `A`, so only component-wise comparison can see it.
    let left : Term := Term.app (conv_free "A") (Term.app (conv_free "idt") (conv_free "P")) in
    let right : Term := Term.app (conv_free "A") (conv_free "P") in
    run_unify_conv left right

#[test]
def test_unify_app_hole_argument_matches : Bool :=
    // `A hole` vs `A P`. A hole in ARGUMENT position matches anything,
    // the same rule the top-level `Term.hole` arm has always applied;
    // `Similar.similar` answers false against a hole, so before the arm
    // this failed despite hole propagation being pervasive.
    let left : Term := Term.app (conv_free "A") Term.hole in
    let right : Term := Term.app (conv_free "A") (conv_free "P") in
    run_unify_conv left right

#[test]
def test_unify_app_spine_congruence_is_recursive : Bool :=
    // A two-argument spine is a nested app: `A P (idt P)` vs `A P P`.
    // The OUTER arm compares the heads `A P` vs `A P` (itself an
    // app/app pair, answered by the fast path) and then the arguments,
    // where the inner conversion happens -- so congruence has to
    // recurse through the spine, not just peel one level.
    run_unify_conv
        (Term.app (Term.app (conv_free "A") (conv_free "P"))
            (Term.app (conv_free "idt") (conv_free "P")))
        (Term.app (Term.app (conv_free "A") (conv_free "P")) (conv_free "P"))

#[test]
def test_unify_app_still_rejects_when_arguments_disagree : Bool :=
    // `A P` vs `A Prop`: distinct rigid arguments under the same head.
    // The congruence must not become "same head, anything goes".
    let left : Term := Term.app (conv_free "A") (conv_free "P") in
    let right : Term := Term.app (conv_free "A") (sort_n 0) in
    let ok : Bool := run_unify_conv left right in
    Bool.not ok

#[test]
def test_unify_app_dimensions_do_not_convert : Bool :=
    // The Stage 2 shape: `A i0` vs `A i1` with the same line. The two
    // dimensions are distinct cubical primitives, conversion between
    // them is exactly what `whnf_cubical` does NOT do, and a boundary
    // rule that quietly accepted this would make every path degenerate.
    let left : Term := Term.app (conv_free "A") (cub CubicalPrim.i0 List.empty) in
    let right : Term := Term.app (conv_free "A") (cub CubicalPrim.i1 List.empty) in
    let ok : Bool := run_unify_conv left right in
    Bool.not ok
