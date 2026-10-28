// Pins on the cubical NAME-BINDING (Stage 1 step 3,
// plans/type-system/univalence.md): the declarations' SHAPE must parse --
// a body-less `#[cubical "..."]`-marked def is the entire surface syntax
// a cubical primitive gets -- and `build_scope_from_decls` must enter
// each marked name into `ScopeData.cubical_prims`, the side table the
// checker's rewrite (`lang/typecheck/infer.mo`) consults.
//
// Scopes are built by PARSING a real source snippet (the same
// `parse_all_decls` + `build_scope_from_decls` entry the checker itself
// goes through), not by hand-assembling decls: the marker has to survive
// the actual parse path for any of this to mean anything. That is also
// what makes the first test load-bearing rather than trivial -- a
// SEQUENCE of body-less attributed defs is exactly the shape a parser
// can stop early on, and the reference host's parser does
// (it accepts a body-less def only under a preceding attribute and
// still rejects the second one in a row); the self-hosted parser's
// `def_body_block_or_none` fail arm must take all six.

use lib::types {
  CubicalPrim, ModulePath, NamePath, Scope, ScopeData,
  cubical_prim_eq,
  id,
}
use lib::module {parse_all_decls}
use parsec::core {fail, success}
use lib::scope {build_scope_from_decls, scope_find_cubical_prim}
use std::list {List.length}

def synthetic_path : ModulePath := ModulePath.mk (List.cons (Identifier.id "synthetic") List.empty)

/// The twelve Stage 1+2+3+4+5 declarations, Stage 6b's witness and Stage
/// 6b-ii's three,
/// spelled the way the real ones are declared (the `with Cubical` block
/// in `init/src/prelude.mo`), minus
/// the block wrapper and `Cubical.` prefixes: the binding pipeline under
/// test is spelling-independent, and the block-form interaction has its
/// own pin below. One literal per decl, concatenated: a single spanning
/// literal would need line continuations the string lexer does not have,
/// and one literal per line keeps each under the width the style ratchet
/// measures.
def cubical_source : String :=
    String.concat "#[cubical \"interval\"] def I : Type\n"
    (String.concat "#[cubical \"i0\"] def i0 : I\n"
    (String.concat "#[cubical \"i1\"] def i1 : I\n"
    (String.concat "#[cubical \"ineg\"] def ineg (i : I) : I\n"
    (String.concat "#[cubical \"imeet\"] def imeet (i : I) (j : I) : I\n"
    (String.concat "#[cubical \"ijoin\"] def ijoin (i : I) (j : I) : I\n"
    (String.concat "#[cubical \"pathp\"] def PathP (A : I -> Type) (a : A i0) (b : A i1) : Type\n"
    (String.concat "#[cubical \"transp\"] def transp (A : I -> Type) (a : A i0) : A i1\n"
    (String.concat "#[cubical \"face_eq0\"] def face_eq0 (i : I) : I\n"
    (String.concat "#[cubical \"face_eq1\"] def face_eq1 (i : I) : I\n"
    (String.concat "#[cubical \"is_one\"] def is_one (i : I) : Type\n"
    (String.concat "#[cubical \"hcomp\"] def hcomp (A : Type) (phi : I) (u : I -> is_one phi -> A) (u0 : A) : A\n"
    (String.concat "#[cubical \"it_is_one\"] def it_is_one : is_one i1\n"
    (String.concat "#[cubical \"glue\"] def Glue (A : Type) (phi : I) (T : is_one phi -> Type) (w : is_one phi -> Type) : Type\n"
    (String.concat "#[cubical \"glue_intro\"] def glue (A : Type) (phi : I) (T : is_one phi -> Type) (w : is_one phi -> Type) (t : is_one phi -> Type) (a : A) : Glue A phi T w\n"
    "#[cubical \"glue_elim\"] def unglue (g : Type) : Type\n"))))))))))))))

/// A scope carrying whatever `source` declares. A snippet that fails to
/// parse yields an empty scope, which makes the binding tests below
/// fail rather than silently pass on a scope with nothing in it.
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
        incomplete_match_ok := false,
    }

/// A one-segment `NamePath`, the shape a top-level def of this synthetic
/// module is registered under.
def name_of (nm : String) : NamePath := NamePath.mk (List.cons (Identifier.id nm) List.empty)

/// Does `scope` bind `nm` to exactly `p`?
def binds (s : Scope) (nm : String) (p : CubicalPrim) : Bool :=
    match scope_find_cubical_prim (name_of nm) s {
        Option.some q => cubical_prim_eq p q,
        Option.none => false,
    }

/// Does `scope` bind `nm` to NO primitive at all?
def binds_nothing (s : Scope) (nm : String) : Bool :=
    match scope_find_cubical_prim (name_of nm) s {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_cubical_decls_parse : Bool :=
    // All sixteen, not "at least one": a parser that stops after the
    // first body-less def (the reference host's does) still hands back
    // a successful non-empty parse.
    match parse_all_decls cubical_source {
        success _ decls => I64.beq (List.length decls) 16,
        fail _ => false,
    }

#[test]
def test_cubical_names_bind : Bool :=
    let s : Scope := scope_of cubical_source in
    binds s "I" CubicalPrim.interval
        && binds s "i0" CubicalPrim.i0
        && binds s "i1" CubicalPrim.i1
        && binds s "ineg" CubicalPrim.ineg
        && binds s "imeet" CubicalPrim.imeet
        && binds s "ijoin" CubicalPrim.ijoin
        && binds s "PathP" CubicalPrim.pathp
        && binds s "transp" CubicalPrim.transp
        && binds s "face_eq0" CubicalPrim.face_eq0
        && binds s "face_eq1" CubicalPrim.face_eq1
        && binds s "is_one" CubicalPrim.is_one
        && binds s "hcomp" CubicalPrim.hcomp
        && binds s "it_is_one" CubicalPrim.it_is_one
        && binds s "Glue" CubicalPrim.glue
        && binds s "glue" CubicalPrim.glue_intro
        && binds s "unglue" CubicalPrim.glue_elim

#[test]
def test_with_block_cubical_names_bind : Bool :=
    // The real prelude spelling: inside `with Cubical { ... }` the
    // primitive's REGISTERED name is the prefixed `Cubical.i0` (the
    // block's whole semantics is the name prefix), which is what
    // `scope_find_cubical_prim` must answer for -- and the bare
    // spelling binds nothing, because no def of that name exists.
    let s : Scope := scope_of "with Cubical { #[cubical \"interval\"] def I : Type\n#[cubical \"i0\"] def i0 : Cubical.I }" in
    binds s "Cubical.i0" CubicalPrim.i0
        && binds_nothing s "i0"

#[test]
def test_unmarked_def_of_the_same_name_binds_nothing : Bool :=
    // The MARKER binds, never the bare spelling -- a user's own `def I`
    // is an ordinary def and must not be stolen into a primitive.
    let s : Scope := scope_of "def I : Type" in
    binds_nothing s "I"

#[test]
def test_unknown_marker_string_binds_nothing : Bool :=
    // A marker naming no known primitive leaves the def ordinary -- the
    // cost of a typo'd marker is losing the binding, never misbinding.
    let s : Scope := scope_of "#[cubical \"nosuch\"] def K : Type" in
    binds_nothing s "K"

#[test]
def test_marker_with_no_string_argument_binds_nothing : Bool :=
    // `#[cubical i0]` names an identifier, not a string; the marker's
    // grammar is one STRING argument, so this binds nothing rather
    // than guessing.
    let s : Scope := scope_of "#[cubical i0] def K : Type" in
    binds_nothing s "K"