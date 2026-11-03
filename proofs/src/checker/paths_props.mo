// Pins on `proofs/src/paths.mo`'s combinators (univalence.md, Stage 2 /
// Part D step 3).
//
// A pin drives the real rule, `def_body_diagnostics`
// (lang/src/module.mo), so it names one def and fails on any diagnostic.
// For a PATH body the discriminating half is NOT the def-boundary `unify`
// -- the path arm echoes the expected `PathP` back as the lambda's type --
// but `check_path_lam`: the body against the path's LINE, and its two
// boundaries against the type's endpoints. Reaching that rule at all is
// what `as_cubical_type` (`lang/typecheck/whnf.mo`) bought: for a
// `Path A a b`-spelled type the dispatch used to fall to the inferring
// arm, and then EVERY pin here passed with any body whatsoever (measured).
//
// The scope is built by the REAL parse + scope-build pipeline over source
// text, not a hand-written `ScopeData`, because the combinators reference
// each other's shapes by name (`Path`, `Sigma`, the cubical primitives)
// and only resolve after the whole declaration list is registered. The
// text is a SECOND copy of `proofs/src/paths.mo`'s own defs, spelled
// without the `Cubical.` prefix the real file needs (the synthetic scope
// has no `with Cubical` block) -- the same arrangement, and the same
// reason, as `equiv_props.mo`.

use lang::module {def_body_diagnostics, try_parse_decls}
use lang::scope {build_scope_from_decls}
use lang::typecheck::infer {empty_locals}
use lang::types {Decl, Def, ModulePath, Scope, ScopeData, id, show_name_path}

def paths_props_path : ModulePath :=
    ModulePath.mk (List.cons (Identifier.id "proofs_paths_props") List.empty)

/// One trailing newline per element, including the last -- the shape the
/// `String.concat` chains elsewhere in this directory end up with.
def each_line (lines : List String) : String :=
    match lines {
        List.empty => "",
        List.cons line rest => String.concat (String.concat line "\n") (each_line rest),
    }

// The fixture source, in three groups. ONE list literal of all 25 elements
// crashes the compiled test binary (`apply_closure1`, SIGSEGV) under both
// the pre- and post-K4 compilers -- a pre-existing codegen bug triggered by
// the mixed literal shape, unrelated to the checker. Smaller nested
// `String.concat` chains, the shape `cubical_props.mo` already uses, are
// the workaround.

def paths_g0 : String :=
    String.concat "#[cubical \"interval\"] def I : Type\n" (String.concat "#[cubical \"i0\"] def i0 : I\n" (String.concat "#[cubical \"i1\"] def i1 : I\n" (String.concat "#[cubical \"ineg\"] def ineg (i : I) : I\n" (String.concat "#[cubical \"pathp\"] def PathP (A : I -> Type) (a : A i0) (b : A i1) : Type\n" (String.concat "pub type Sigma (A : Type) (B : A -> Type) { dpair (fst : A) (snd : B fst) }\n" (String.concat "def Path (A : Type) (a : A) (b : A) : Type := PathP (fn _ => A) a b\n" (String.concat "def refl {A : Type} (a : A) : Path A a a := fn (i : I) => a\n" ("def sym {A : Type} {a : A} {b : A} (p : Path A a b) : Path A b a := fn (i : I) => p (ineg i)\n"))))))))

def paths_g1 : String :=
    String.concat "def ap {A : Type} {B : Type} {a : A} {b : A} (f : A -> B) (p : Path A a b) : Path B (f a) (f b) := fn (i : I) => f (p i)\n" (String.concat "def apd {A : Type} {B : A -> Type} {a : A} {b : A} (f : (x : A) -> B x) (p : Path A a b) : PathP (fn x => B (p x)) (f a) (f b) := fn (i : I) => f (p i)\n" (String.concat "def funext {A : Type} {B : Type} {f : A -> B} {g : A -> B} (h : (x : A) -> Path B (f x) (g x)) : Path (A -> B) f g := fn (i : I) => fn (x : A) => h x i\n" (String.concat "def funext_dep {A : Type} {B : A -> Type} {f : (x : A) -> B x} {g : (x : A) -> B x} (h : (x : A) -> Path (B x) (f x) (g x)) : Path ((x : A) -> B x) f g := fn (i : I) => fn (x : A) => h x i\n" (String.concat "def funext_inv {A : Type} {B : Type} {f : A -> B} {g : A -> B} (p : Path (A -> B) f g) : (x : A) -> Path B (f x) (g x) := fn (x : A) => fn (i : I) => p i x\n" (String.concat "def ap_refl {A : Type} {B : Type} (f : A -> B) (a : A) : Path (Path B (f a) (f a)) (ap f (refl a)) (refl (f a)) := fn (i : I) => fn (j : I) => f a\n" (String.concat "def sym_sym {A : Type} {a : A} {b : A} (p : Path A a b) : Path (Path A a b) (sym (sym p)) p := fn (k : I) => fn (i : I) => p (ineg (ineg i))\n" ("def bad_boundary {A : Type} {a : A} {b : A} (p : Path A a b) : Path A a b := fn (i : I) => p (ineg i)\n")))))))

def paths_g2 : String :=
    String.concat "def bad_codomain {A : Type} {B : Type} (f : A -> B) {a : A} {b : A} (p : Path A a b) : Path B (f b) (f a) := fn (i : I) => f (p i)\n" (String.concat "def bad_funext_boundary {A : Type} {B : Type} {f : A -> B} {g : A -> B} (h : (x : A) -> Path B (f x) (g x)) : Path (A -> B) g f := fn (i : I) => fn (x : A) => h x i\n" (String.concat "def bad_funext_body {A : Type} {B : Type} {f : A -> B} {g : A -> B} (h : (x : A) -> Path B (f x) (g x)) : Path (A -> B) f g := fn (i : I) => fn (x : A) => f x\n" (String.concat "def bad_funext_dep {A : Type} {B : A -> Type} {f : (x : A) -> B x} {g : (x : A) -> B x} (h : (x : A) -> Path (B x) (f x) (g x)) : Path ((x : A) -> B x) g f := fn (i : I) => fn (x : A) => h x i\n" (String.concat "def bad_funext_inv {A : Type} {B : Type} {f : A -> B} {g : A -> B} (p : Path (A -> B) f g) : (x : A) -> Path B (g x) (f x) := fn (x : A) => fn (i : I) => p i x\n" (String.concat "def bad_sym_sym {A : Type} {a : A} {b : A} (p : Path A a b) : Path (Path A a b) (sym (sym p)) p := fn (k : I) => fn (i : I) => p (ineg i)\n" (String.concat "def bad_ap_refl_body {A : Type} {B : Type} (f : A -> B) (a : A) : Path (Path B (f a) (f a)) (ap f (refl a)) (refl (f a)) := fn (i : I) => fn (j : I) => a\n" ("def rejected_control : Type := no_such_name_anywhere\n")))))))

/// The two combinators that apply the dimension TWICE, kept in their own
/// group: the affine rule is not what these feed (`def_body_diagnostics` is
/// the type checker) -- that the second use is ALLOWED at all is the
/// `Copy Cubical.I` instance's job, pinned at the driver level in
/// `lang/src/tests/typecheck_negative_tests.mo`.
def paths_g3 : String :=
    String.concat "def ap2 {A : Type} {B : Type} {C : Type} {a0 : A} {a1 : A} {b0 : B} {b1 : B} (f : A -> B -> C) (p : Path A a0 a1) (q : Path B b0 b1) : Path C (f a0 b0) (f a1 b1) := fn (i : I) => f (p i) (q i)\n" (String.concat "def path_pair {A : Type} {B : A -> Type} {a0 : A} {a1 : A} {b0 : B a0} {b1 : B a1} (p : Path A a0 a1) (q : PathP (fn i => B (p i)) b0 b1) : Path (Sigma A B) (Sigma.dpair a0 b0) (Sigma.dpair a1 b1) := fn (i : I) => Sigma.dpair (p i) (q i)\n" "")

/// Their rejection controls: swapping the two-place application's endpoints,
/// and reversing the dependent pair's second component.
def paths_g4 : String :=
    String.concat "def bad_ap2 {A : Type} {B : Type} {C : Type} {a0 : A} {a1 : A} {b0 : B} {b1 : B} (f : A -> B -> C) (p : Path A a0 a1) (q : Path B b0 b1) : Path C (f a1 b1) (f a0 b0) := fn (i : I) => f (p i) (q i)\n" (String.concat "def bad_path_pair {A : Type} {B : A -> Type} {a0 : A} {a1 : A} {b0 : B a0} {b1 : B a1} (p : Path A a0 a1) (q : PathP (fn i => B (p i)) b0 b1) : Path (Sigma A B) (Sigma.dpair a0 b0) (Sigma.dpair a1 b1) := fn (i : I) => Sigma.dpair (p i) (q (ineg i))\n" "")

def paths_decls_source : String :=
    String.concat paths_g0 (String.concat paths_g1 (String.concat paths_g2 (String.concat paths_g3 paths_g4)))

/// The declarations, or the empty list on a parse failure -- which makes
/// every pin below fail rather than silently pass against nothing.
def paths_decls : List Decl :=
    match try_parse_decls paths_decls_source {
        Option.some decl_list => decl_list,
        Option.none => List.empty,
    }

def paths_scope : Scope :=
    let sd : ScopeData := build_scope_from_decls paths_props_path paths_decls in
    {
        module_id := paths_props_path,
        scope := sd,
        parent := Option.none,
        incomplete_match_ok := false,
    }

/// The `def` named `nm` in the parsed source, if it parsed as one.
def find_def (nm : String) (decls : List Decl) : Option Def :=
    match decls {
        List.empty => Option.none,
        List.cons d rest =>
            match d {
                Decl.def_d df =>
                    if String.beq (show_name_path df.name) nm
                    then Option.some df
                    else find_def nm rest,
                _ => find_def nm rest,
            },
    }

/// Every diagnostic `nm`'s body raises against its own declared type. A
/// missing def is a diagnostic too, so a renamed or unparsed def fails its
/// pin instead of vacuously passing.
def diagnostics_of (nm : String) : List String :=
    match find_def nm paths_decls {
        Option.none => List.cons (String.concat "missing def: " nm) List.empty,
        Option.some df => def_body_diagnostics df paths_scope empty_locals Option.none,
    }

def checks (nm : String) : Bool :=
    match diagnostics_of nm {
        List.empty => true,
        _ => false,
    }

#[test]
def test_refl_checks_against_its_declared_path : Bool :=
    checks "refl"

#[test]
def test_sym_checks_against_its_declared_path : Bool :=
    checks "sym"

#[test]
def test_ap_checks_against_its_declared_path : Bool :=
    checks "ap"

#[test]
def test_apd_checks_against_its_declared_pathp : Bool :=
    checks "apd"

#[test]
def test_ap2_checks_against_its_declared_path : Bool :=
    checks "ap2"

#[test]
def test_path_pair_checks_against_its_declared_path : Bool :=
    checks "path_pair"

/// ... and both are discriminating: swapping the two-place application's
/// endpoints, and reversing the dependent pair's second component, must fail.
#[test]
def test_ap2_with_swapped_endpoints_is_rejected : Bool :=
    not (checks "bad_ap2")

#[test]
def test_path_pair_with_a_reversed_second_component_is_rejected : Bool :=
    not (checks "bad_path_pair")

#[test]
def test_funext_checks_against_its_declared_path : Bool :=
    checks "funext"

#[test]
def test_funext_dep_checks_against_its_declared_path : Bool :=
    checks "funext_dep"

#[test]
def test_funext_inv_checks_against_its_declared_pi : Bool :=
    checks "funext_inv"

#[test]
def test_ap_refl_checks_against_its_declared_path : Bool :=
    checks "ap_refl"

#[test]
def test_sym_sym_checks_against_its_declared_path : Bool :=
    checks "sym_sym"

/// `funext`'s boundaries are the whole content of the rule: the body's i0
/// boundary is `fn x => f x`, so declaring `g` on the left must fail.
#[test]
def test_funext_with_swapped_endpoints_is_rejected : Bool :=
    not (checks "bad_funext_boundary")

/// A body that ignores the dimension returns `f x` at BOTH endpoints, so
/// the i1 boundary does not meet `g`.
#[test]
def test_funext_body_that_ignores_the_dimension_is_rejected : Bool :=
    not (checks "bad_funext_body")

#[test]
def test_funext_dep_with_swapped_endpoints_is_rejected : Bool :=
    not (checks "bad_funext_dep")

/// `funext_inv`'s endpoint swap: the body applies `p` at i0, giving `f x`,
/// where the declared left endpoint is `g x`.
#[test]
def test_funext_inv_with_swapped_endpoints_is_rejected : Bool :=
    not (checks "bad_funext_inv")

/// `sym_sym` with `sym`'s own body (`ineg i` instead of `ineg (ineg i)`) is
/// the opposite path; the endpoints must reject it.
#[test]
def test_sym_sym_with_the_sym_body_is_rejected : Bool :=
    not (checks "bad_sym_sym")

/// `ap_refl` returns an `A`-element where the path's line is `B`. A swapped
/// endpoint cannot discriminate here because `ap f (refl a)` and
/// `refl (f a)` are convertible, so this control exercises the body check.
#[test]
def test_ap_refl_body_of_the_wrong_type_is_rejected : Bool :=
    not (checks "bad_ap_refl_body")

/// `ap2` and `path_pair` are deliberately absent: both apply two paths at
/// the same dimension, and `proofs/` runs the affine rule in `error` mode
/// (no `[affine]` table in its manifest), so a dimension used twice is
/// rejected because `Cubical.I` has no `Copy` instance. Pinned as a
/// measured follow-up in univalence.md, not silently dropped.

/// `bad_boundary` is `sym`'s body under `sym`'s own (symmetry) type: it is
/// well-typed at the head and wrong at both endpoints, so it exercises
/// `check_path_boundary` rather than the body's own check.
#[test]
def test_a_path_with_the_wrong_boundary_is_rejected : Bool :=
    not (checks "bad_boundary")

/// `bad_codomain` is `ap` with its declared endpoints swapped: the body
/// itself is fine, the declared type is not the one the body has.
#[test]
def test_a_path_with_the_wrong_codomain_is_rejected : Bool :=
    not (checks "bad_codomain")

/// The harness's own control: a def whose body cannot check at all must be
/// reported, or every pin above passes against anything.
#[test]
def test_harness_reports_an_unresolvable_body : Bool :=
    not (checks "rejected_control")

#[test]
def test_harness_reports_a_missing_def : Bool :=
    not (checks "no_such_def_at_all")
