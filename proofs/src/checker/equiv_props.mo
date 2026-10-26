// Pins on Stage 6a's library defs (plans/type-system/univalence.md):
// `Path`, `isContr`, `fiber`, `isEquiv` and `Equiv`.
//
// These are ordinary library definitions rather than new typing rules, so
// what a pin can observe is that each def's BODY still checks against its
// own DECLARED type -- the comparison `check_def_with_scope`
// (lang/src/module.mo) attempts for every def, made explicit here so a pin
// names one def. Made explicit rather than relied on, because that attempt
// is VACUOUS for these shapes: `type_check`'s leaf arms (see this file's
// harness controls below) never compare against the expected type, so
// `check` alone would accept a body of the wrong type here.
//
// The `Path` pin is the load-bearing one and is why this file exists: its
// body `Cubical.PathP (fn _ => A) a b` is the FIRST code in the tree to
// hand a dependent parameter chain's later binder to `unify` from a
// context deeper than the one its type was written in, which is exactly
// what `type_check_bound_var`'s missing depth shift broke (fixed in the
// `lang: shift a bound variable's declared type...` commit). Reverting
// that one-line shift makes this pin fail and the others still pass --
// confirmed by running it both ways, which is what makes it a
// mutation-checked control rather than an acceptance pin.
//
// The scope is built by the REAL parse + scope-build pipeline over source
// text, not a hand-written `ScopeData`, because these defs reference each
// other by name (`Equiv` mentions `isEquiv`, `isEquiv` mentions
// `isContr`) and resolve only after the whole declaration list is
// registered. That text is a SECOND copy of `proofs/src/equiv.mo`'s own
// defs -- unavoidable here, because what is under test is the parse of
// that text, and a `use` of the compiled defs would bypass it. If the defs
// change, both copies change; `cubical_props.mo`'s own preamble says the
// same about its copy of the prelude's `with Cubical` block.

use lang::module {try_parse_decls}
use lang::scope {build_scope_from_decls}
use lang::typecheck::infer {empty_local_types, empty_locals, type_check}
use lang::types {
  Decl, Def, ModulePath, Scope, ScopeData, Term, id, show_name_path,
}

def equiv_props_path : ModulePath :=
    ModulePath.mk (List.cons (Identifier.id "proofs_equiv_props") List.empty)

/// One trailing newline per element, including the last -- the shape the
/// `String.concat` chains in `cubical_props.mo`/`elim_props.mo` end up
/// with. Factored out because a ten-deep nest is a paren-counting hazard
/// the parser reports a hundred characters away from the real mistake.
def each_line (lines : List String) : String :=
    match lines {
        List.empty => "",
        List.cons line rest => String.concat (String.concat line "\n") (each_line rest),
    }

/// The four cubical primitives these defs bottom out in (spelled as the
/// prelude's `with Cubical` block declares them, minus the wrapper and
/// prefixes -- the same source `cubical_props.mo` builds its scope from),
/// `Sigma`, and the five Stage 6a defs written verbatim as
/// `proofs/src/equiv.mo` declares them.
def equiv_decls_source : String :=
    each_line [
        "#[cubical \"interval\"] def I : Type",
        "#[cubical \"i0\"] def i0 : I",
        "#[cubical \"i1\"] def i1 : I",
        "#[cubical \"pathp\"] def PathP (A : I -> Type) (a : A i0) (b : A i1) : Type",
        "pub type Sigma (A : Type) (B : A -> Type) { dpair (fst : A) (snd : B fst) }",
        "def Path (A : Type) (a : A) (b : A) : Type := PathP (fn _ => A) a b",
        "def isContr (A : Type) : Type := Sigma A (fn center => ((x : A) -> Path A x center))",
        "def fiber (A : Type) (B : Type) (f : A -> B) (b : B) : Type := Sigma A (fn a => Path B (f a) b)",
        "def isEquiv (A : Type) (B : Type) (f : A -> B) : Type := (b : B) -> isContr (fiber A B f b)",
        "def Equiv (A : Type) (B : Type) : Type := Sigma (A -> B) (fn f => isEquiv A B f)",
        // The harness's own negative control, NOT part of `equiv.mo`: a
        // body that cannot check under any checker, since it names nothing.
        "def rejected_control : Type := no_such_name_anywhere",
    ]

/// The declarations, or the empty list on a parse failure -- which makes
/// every pin below fail rather than silently pass against nothing.
def equiv_decls : List Decl :=
    match try_parse_decls equiv_decls_source {
        Option.some decl_list => decl_list,
        Option.none => List.empty,
    }

def equiv_scope : Scope :=
    let sd : ScopeData := build_scope_from_decls equiv_props_path equiv_decls in
    {
        module_id := equiv_props_path,
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

/// Does `nm`'s parsed body check against `typ`?
///
/// Kept apart from `def_body_checks` so that no single function reads both
/// `df.typ` and `df.term`: those are two USES of an affine `Def`, which the
/// multiplicity checker rejects.
def body_checks (nm : String) (typ : Term) : Bool :=
    match find_def nm equiv_decls {
        Option.none => false,
        Option.some df =>
            match type_check df.term typ equiv_scope empty_local_types empty_locals {
                ok _ => true,
                err _ => false,
            },
    }

/// Does `nm`'s parsed body check against its own declared type?
def def_body_checks (nm : String) : Bool :=
    match find_def nm equiv_decls {
        Option.none => false,
        Option.some df => body_checks nm df.typ,
    }

#[test]
def test_path_body_checks : Bool :=
    def_body_checks "Path"

#[test]
def test_iscontr_body_checks : Bool :=
    def_body_checks "isContr"

#[test]
def test_fiber_body_checks : Bool :=
    def_body_checks "fiber"

#[test]
def test_isequiv_body_checks : Bool :=
    def_body_checks "isEquiv"

#[test]
def test_equiv_body_checks : Bool :=
    def_body_checks "Equiv"

/// The harness's own mutation controls: `def_body_checks` must be able to
/// report failure, or the five pins above pass against anything.
///
/// Both are forced to fail by a body that cannot check at all, rather than
/// by a real def checked against a WRONG expected type. The latter does
/// not work, and the reason is a measured pre-existing gap rather than a
/// property of these defs: `type_check`'s leaf arms return their own type
/// WITHOUT comparing it against `expected_type` -- the same statement
/// `type_check_pathp_endpoints`'s own comment makes about its `var` and
/// constructor arms, and `type_check_lit` is a third. So a def body of
/// `0i64` declared `: Type` checks. That does not weaken the pins above,
/// whose failure mode is `type_check` erroring on the body itself, which
/// the `Path` pin's mutation check exercises.
#[test]
def test_harness_reports_an_unresolvable_body : Bool :=
    not (def_body_checks "rejected_control")

#[test]
def test_harness_reports_a_missing_def : Bool :=
    not (def_body_checks "no_such_def_at_all")
