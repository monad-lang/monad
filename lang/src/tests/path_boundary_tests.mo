// Direct pins on the applied-path boundary rewrite (univalence.md K5).
//
// `normalize_path_boundary` is internal to `lang/typecheck/infer.mo`; these
// pins import it from inside the `lang` mote, the same way `unify_tests.mo`
// imports the non-`pub` `unify`. The end-to-end pin is `funext` in
// `proofs/src/checker/paths_props.mo`; this file exists because the
// end-to-end pin cannot tell a wrong de Bruijn depth from a missing rewrite.
//
// The shape under test is funext's boundary: `h : (x : A) -> Path (B) (f x)
// (g x)`, applied as `h x i0`, whose endpoint is `f x`. The bare-variable
// rewrite already handled `p i0`; what is new is the application spine
// BEFORE the endpoint argument.

use lang::types {
  DebugName, Identifier, LocalScope, ModulePath, Scope, Similar, Term,
  binder_anon, binder_named, cub_i0, cub_i1, cub_interval, cub_pathp,
  sentinel,
}
use lib::scope {build_scope_from_decls}
use lib::typecheck::infer {normalize_path_boundary}

def path_boundary_path : ModulePath := ModulePath.mk List.empty

def path_boundary_scope : Scope := {
    module_id := path_boundary_path,
    scope := build_scope_from_decls path_boundary_path List.empty,
    parent := Option.none,
    incomplete_match_ok := false,
}

def path_boundary_locals : LocalScope := {
    vars := List.empty,
    parent := Option.none,
}

/// A free (global) reference: `whnf` may unfold it, `nth_type` never sees it.
def fv (nm : String) : Term :=
    Term.var sentinel (DebugName.named (Identifier.id nm))

def lv (idx : I64) (nm : String) : Term :=
    Term.var idx (DebugName.named (Identifier.id nm))

def rewrites_to (input : Term) (local_types : List Term) (expected : Term) : Bool :=
    Similar.similar
        (normalize_path_boundary input path_boundary_scope local_types path_boundary_locals)
        expected

/// `h : (x : A) -> Path B (f x) (g x)`, stored at the depth outside `h`.
def applied_h_ty : Term :=
    Term.pi binder_anon (fv "A")
        (cub_pathp (Term.lam binder_anon cub_interval (fv "B"))
            (Term.app (fv "f") (lv 0 "x"))
            (Term.app (fv "g") (lv 0 "x")))

/// `h x <last>`: `h` is at local index 0, so the whole spine is one binder
/// deep and the depth shift is a no-op for the free variables in this fixture.
def applied_spine (last : Term) : Term :=
    Term.app (Term.app (lv 0 "h") (fv "x")) last

#[test]
def test_normalize_rewrites_an_applied_path_at_i0 : Bool :=
    rewrites_to (applied_spine cub_i0) [applied_h_ty]
        (Term.app (fv "f") (fv "x"))

#[test]
def test_normalize_rewrites_an_applied_path_at_i1 : Bool :=
    rewrites_to (applied_spine cub_i1) [applied_h_ty]
        (Term.app (fv "g") (fv "x"))

/// The same spine wrapped in a lambda: the normalizer descends under the
/// binder, pushes its type, and `h` is now local index 1. Without the descent
/// the whole lambda is left unchanged.
#[test]
def test_normalize_rewrites_under_a_binder : Bool :=
    rewrites_to
        (Term.lam (binder_named (Identifier.id "x")) cub_interval
            (Term.app (Term.app (lv 1 "h") (lv 0 "x")) cub_i0))
        [applied_h_ty]
        (Term.lam (binder_named (Identifier.id "x")) cub_interval
            (Term.app (fv "f") (lv 0 "x")))

#[test]
def test_normalize_leaves_a_non_endpoint_last_argument : Bool :=
    rewrites_to (applied_spine (fv "q")) [applied_h_ty] (applied_spine (fv "q"))

/// A head whose Pi chain does not end in a path has no endpoint to give.
#[test]
def test_normalize_does_not_rewrite_a_non_path_spine : Bool :=
    let plain_h_ty : Term := Term.pi binder_anon (fv "A") (fv "A") in
    rewrites_to (applied_spine cub_i0) [plain_h_ty]
        (applied_spine cub_i0)

/// A global head is a `whnf`/delta job; the rewrite refuses it.
#[test]
def test_normalize_does_not_rewrite_a_global_head : Bool :=
    rewrites_to (Term.app (Term.app (fv "h") (fv "x")) cub_i0)
        [applied_h_ty]
        (Term.app (Term.app (fv "h") (fv "x")) cub_i0)

/// The leading arguments must SATURATE the Pi chain down to the path: with one
/// binder still left, there is no path to read an endpoint from.
#[test]
def test_normalize_requires_a_saturated_pi_chain : Bool :=
    let two_pi_h_ty : Term :=
        Term.pi binder_anon (fv "A")
            (Term.pi binder_anon (fv "A")
                (cub_pathp (Term.lam binder_anon cub_interval (fv "B"))
                    (fv "a") (fv "b"))) in
    rewrites_to (applied_spine cub_i0) [two_pi_h_ty] (applied_spine cub_i0)

/// The depth pin: `y` sits OUTSIDE `h`'s stored type, so inside the Pi's
/// codomain it is `var 1`. Reading the type here needs `term_shift (idx + 1)`;
/// dropping the shift would leave `y` as `var 0` after `beta_reduce`, aliasing
/// the Pi's own binder.
#[test]
def test_normalize_shifts_the_local_type_to_the_current_depth : Bool :=
    let y_name : DebugName := DebugName.named (Identifier.id "y") in
    let depth_h_ty : Term :=
        Term.pi binder_anon (fv "A")
            (cub_pathp (Term.lam binder_anon cub_interval (fv "B"))
                (Term.app (fv "f") (Term.var 1 y_name))
                (Term.app (fv "g") (Term.var 1 y_name))) in
    rewrites_to (applied_spine cub_i0) [depth_h_ty]
        (Term.app (fv "f") (Term.var 1 y_name))
