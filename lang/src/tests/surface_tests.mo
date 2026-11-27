/// Pins on the surface->legacy embedding (`lang::surface`). Each one asserts
/// that a `Surface` form embeds to EXACTLY the core term the old lowering
/// built for it, because S3's contract is byte-identical output.

use lang::types {
    DebugName, Def, Decl, FieldPattern, Identifier, Literal, Location,
    MatchCase, NamePath, NumSuffix, Similar, StructLitField, Term,
    Visibility, field_access_chain, term_loc,
}
use lib::surface {
    DefS, SLiteral, SMatchCase, SStructLitField, Surface, s_field_access_chain,
    surface_def_to_legacy, surface_to_legacy,
}
use lib::pretty {show_decl}

def named_var (idx : I64) (name : String) : Term :=
    Term.var idx (DebugName.named (Identifier.id name))

def named_surface (idx : I64) (name : String) : Surface :=
    Surface.var idx (DebugName.named (Identifier.id name))

#[test]
def test_surface_if_embeds_as_a_literal_if : Bool :=
    let s : Surface := Surface.if_ (named_surface 0 "a") (named_surface 1 "b") (named_surface 2 "c") in
    let expected : Term :=
        Term.lit (Literal.if_ (named_var 0 "a") (named_var 1 "b") (named_var 2 "c")) in
    Similar.similar (surface_to_legacy s) expected

#[test]
def test_surface_match_embeds_as_a_literal_match : Bool :=
    let sc : SMatchCase :=
        SMatchCase.mk (Identifier.id "Option.some") [Identifier.id "x"]
            (named_surface 0 "x") Option.none Option.none in
    let expected_case : MatchCase :=
        MatchCase.mk (Identifier.id "Option.some") [Identifier.id "x"]
            (named_var 0 "x") Option.none Option.none in
    let expected : Term :=
        Term.lit (Literal.match_ (named_var 0 "v") [expected_case]) in
    Similar.similar (surface_to_legacy (Surface.match_ (named_surface 0 "v") [sc])) expected

#[test]
def test_surface_struct_lit_embeds_as_a_literal_struct_lit : Bool :=
    let s : Surface :=
        Surface.struct_lit [SStructLitField.mk (Identifier.id "x") (Surface.hole)] Option.none in
    let expected : Term :=
        Term.lit (Literal.struct_lit [StructLitField.mk (Identifier.id "x") Term.hole] Option.none) in
    Similar.similar (surface_to_legacy s) expected

#[test]
def test_surface_struct_update_embeds_as_a_literal_struct_update : Bool :=
    let s : Surface :=
        Surface.struct_update (named_surface 0 "base")
            [SStructLitField.mk (Identifier.id "x") (Surface.hole)] in
    let expected : Term :=
        Term.lit (Literal.struct_update (named_var 0 "base")
            [StructLitField.mk (Identifier.id "x") Term.hole]) in
    Similar.similar (surface_to_legacy s) expected

/// A `let ... in match` does not parse in this position and patterns are
/// flat, so the check lives in two small defs.
def loc_fields_are (l : Location) (off : I64) (line : I64) (col : I64) : Bool :=
    match l {
        Location.mk o li c => I64.beq o off && I64.beq li line && I64.beq c col,
    }

def loc_is (l : Option Location) (off : I64) (line : I64) (col : I64) : Bool :=
    match l {
        Option.some loc => loc_fields_are loc off line col,
        Option.none => false,
    }

/// `Similar Term` peels `ctx`, so this pin reads the wrapper directly.
#[test]
def test_surface_ctx_is_preserved : Bool :=
    let loc : Location := Location.mk 5 2 3 in
    loc_is (term_loc (surface_to_legacy (Surface.ctx loc Surface.hole))) 5 2 3

#[test]
def test_surface_immediates_embed_one_for_one : Bool :=
    Similar.similar (surface_to_legacy (Surface.lit (SLiteral.num 42 NumSuffix.i64)))
        (Term.lit (Literal.num 42 NumSuffix.i64)) &&
    Similar.similar (surface_to_legacy (Surface.lit (SLiteral.str "s")))
        (Term.lit (Literal.str "s")) &&
    Similar.similar (surface_to_legacy (Surface.lit (SLiteral.flt "1.5" NumSuffix.f64)))
        (Term.lit (Literal.flt "1.5" NumSuffix.f64))

#[test]
def test_s_field_access_chain_embeds_like_the_legacy_chain : Bool :=
    Similar.similar
        (surface_to_legacy (s_field_access_chain (named_surface 0 "p")
            [Identifier.id "a", Identifier.id "b"]))
        (field_access_chain (named_var 0 "p")
            [Identifier.id "a", Identifier.id "b"])

#[test]
def test_surface_def_embeds_as_the_same_decl : Bool :=
    let ds : DefS := {
        name := NamePath.mk [Identifier.id "f"],
        typ := Surface.hole,
        term := Surface.hole,
        constraints := List.empty,
        attrs := List.empty,
        vis := Visibility.package_private,
        params := List.empty
    } in
    let expected : Decl :=
        Decl.def_d (Def.mk (NamePath.mk [Identifier.id "f"]) Term.hole Term.hole
            List.empty List.empty Visibility.package_private List.empty) in
    String.beq (show_decl (Decl.def_d (surface_def_to_legacy ds))) (show_decl expected)
