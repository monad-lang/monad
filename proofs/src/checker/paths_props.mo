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

def paths_decls_source : String :=
    each_line [
        "#[cubical \"interval\"] def I : Type",
        "#[cubical \"i0\"] def i0 : I",
        "#[cubical \"i1\"] def i1 : I",
        "#[cubical \"ineg\"] def ineg (i : I) : I",
        "#[cubical \"pathp\"] def PathP (A : I -> Type) (a : A i0) (b : A i1) : Type",
        "pub type Sigma (A : Type) (B : A -> Type) { dpair (fst : A) (snd : B fst) }",
        "def Path (A : Type) (a : A) (b : A) : Type := PathP (fn _ => A) a b",
        "def refl {A : Type} (a : A) : Path A a a := fn (i : I) => a",
        "def sym {A : Type} {a : A} {b : A} (p : Path A a b) : Path A b a := fn (i : I) => p (ineg i)",
        String.concat "def ap {A : Type} {B : Type} (f : A -> B) {a : A} {b : A} (p : Path A a b)"
            " : Path B (f a) (f b) := fn (i : I) => f (p i)",
        String.concat "def apd {A : Type} {B : A -> Type} (f : (x : A) -> B x) {a : A} {b : A}"
            " (p : Path A a b) : PathP (fn x => B (p x)) (f a) (f b) := fn (i : I) => f (p i)",
        // The harness's own controls, NOT part of `paths.mo`: two shapes
        // the combinator rules must reject, plus one that cannot check at
        // all. They are what makes the four pins above discriminating
        // rather than merely accepting.
        "def bad_boundary {A : Type} {a : A} {b : A} (p : Path A a b) : Path A a b := fn (i : I) => p (ineg i)",
        String.concat "def bad_codomain {A : Type} {B : Type} (f : A -> B) {a : A} {b : A}"
            " (p : Path A a b) : Path B (f b) (f a) := fn (i : I) => f (p i)",
        "def rejected_control : Type := no_such_name_anywhere",
    ]

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
