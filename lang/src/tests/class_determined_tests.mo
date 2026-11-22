/// A class head's `{S : Type}` binder is an instance-determined variable:
/// parsed into `Class.determined`, never into `params`. `{u : Universe}`
/// and `{u}` stay level binders and are dropped.
use lang::types {Class, Decl, Identifier, Param}
use parsec::core {ParseResult}
use lang::parser {decls_parser}
use lang::pretty {show_class}
use std::list {List.intercalate}

def first_class (src : String) : Option Class :=
    match decls_parser src {
        ParseResult.success _ decls =>
            match decls {
                List.cons d _ =>
                    match d {
                        Decl.class_d c => Option.some c,
                        _ => Option.none,
                    },
                List.empty => Option.none,
            },
        ParseResult.fail _ => Option.none,
    }

def names (ps : List Param) : List String :=
    List.map (fn (p : Param) => match p.name { Identifier.id s => s }) ps

def names_are (ps : List Param) (want : List String) : Bool :=
    String.beq (List.intercalate "," (names ps)) (List.intercalate "," want)

#[test]
def test_a_braced_type_binder_is_determined_not_a_param : Bool :=
    match first_class "class Ms {S : Type} (M : Type -> Type) {\n    def get : M S\n}\n" {
        Option.some c => names_are c.determined ["S"] && names_are c.params ["M"],
        Option.none => false,
    }

#[test]
def test_a_universe_binder_is_still_dropped : Bool :=
    match first_class "class Inh {u : Universe} (a : Sort u) : Sort (max 1 u) {\n    def dflt : a\n}\n" {
        Option.some c => names_are c.determined [] && names_are c.params ["a"],
        Option.none => false,
    }

#[test]
def test_level_and_determined_binders_mix : Bool :=
    match first_class "class Mx {u} {S : Type} {W : Type} (M : Type -> Type) {\n    def put (s : S) (w : W) : M Unit\n}\n" {
        Option.some c => names_are c.determined ["S", "W"] && names_are c.params ["M"],
        Option.none => false,
    }

#[test]
def test_a_class_without_braces_has_none : Bool :=
    match first_class "class Sh A {\n    def sh (a : A) : String\n}\n" {
        Option.some c => I64.beq (List.length c.determined) 0 && names_are c.params ["A"],
        Option.none => false,
    }

#[test]
def test_the_pretty_printer_shows_the_binder : Bool :=
    match first_class "class Ms {S : Type} (M : Type -> Type) {\n    def get : M S\n}\n" {
        Option.some c => String.starts_with "class Ms {S : Type} (M : " (show_class c),
        Option.none => false,
    }

#[test]
def test_a_determined_binder_missing_its_brace_is_an_error : Bool :=
    match first_class "class Ms {S : Type (M : Type -> Type) {\n    def get : M S\n}\n" {
        Option.some _ => false,
        Option.none => true,
    }
