/// Parse -> pretty-print -> re-parse round-trip tests for the `use`/`open`
/// brace syntax. Moved here from `slow_tests/parser_file_tests.mo`: these
/// parse tiny inline snippets (sub-millisecond each), not real files, so
/// they don't belong in the directory reserved for expensive whole-file
/// parses -- they were just sitting outside the fast pre-commit sweep for
/// no reason.

use lang::types {
    DebugName, Decl, Def, Identifier, ParseDecl, Term, term_peel,
    show_identifier, show_name_path,
}
use lib::module {parse_all_decls}
use lib::parser {open_parser, use_parser}
use lib::parser::lower_parse {lower_parse_decl, lower_ctx_bare}
use parsec::core {ParseResult}
use lib::pretty {show_decl}

open ParseResult {fail, success}

/// The `Def` named `name` in a parsed module, if any.
#[terminating]
def parsed_def_typ (name : String) (decls : List Decl) : Option Term :=
    match decls {
        List.empty => Option.none,
        List.cons d rest =>
            match d {
                Decl.def_d df =>
                    match df {
                        Def.mk { name := np, typ, .. } =>
                            if String.beq (show_name_path np) name
                            then Option.some typ
                            else parsed_def_typ name rest,
                    },
                _ => parsed_def_typ name rest,
            },
    }

/// The domain of the first leading binder named `target`.
#[terminating]
def binder_domain_named (target : String) (t : Term) : Option Term :=
    match term_peel t {
        Term.pi b arg ret =>
            match b.name {
                DebugName.named id =>
                    if String.beq (show_identifier id) target
                    then Option.some arg
                    else binder_domain_named target ret,
                DebugName.unnamed => binder_domain_named target ret,
            },
        _ => Option.none,
    }

/// Do `t`'s leading Pi binders spell `names`, in order?
#[terminating]
def starts_with_binder_names (names : List String) (t : Term) : Bool :=
    match names {
        List.empty => true,
        List.cons nm rest =>
            match term_peel t {
                Term.pi b _ ret =>
                    match b.name {
                        DebugName.named id =>
                            if String.beq (show_identifier id) nm
                            then starts_with_binder_names rest ret
                            else false,
                        DebugName.unnamed => false,
                    },
                _ => false,
            },
    }

/// Multiple implicit clauses bind in SOURCE order. The param loop reverses
/// its accumulated list once at exit, which also flipped the relative order
/// of separate clauses: `{A : Type} {B : A -> Type}` used to emit
/// `B` before the `A` its own domain mentions.
#[test]
def test_implicit_clauses_keep_source_order : Bool :=
    match parse_all_decls "def two {A : Type} {B : A -> Type} (p : I64) : I64 := 1" {
        success _ decls =>
            match parsed_def_typ "two" decls {
                Option.some typ => starts_with_binder_names ["A", "B"] typ,
                Option.none => false,
            },
        fail _ => false,
    }

/// Is `t` a variable occurrence spelled `name` (at any de Bruijn index)?
def is_var_named (name : String) (t : Term) : Bool :=
    match t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => String.beq (show_identifier id) name,
                DebugName.unnamed => false,
            },
        _ => false,
    }

/// An implicit clause must keep its DECLARED type: `{a : A}` becomes a
/// `forall a : A` binder, not a name elaboration re-invents with the
/// `Sort 1`/`Sort 0` placeholder. This is what lets a term-level implicit
/// parameter (`proofs/src/paths.mo`'s `{a b : A}`) be used at its real
/// element type.
#[test]
def test_implicit_clause_keeps_its_declared_type : Bool :=
    match parse_all_decls "def keep {A : Type} {a : A} (x : A) : A := x" {
        success _ decls =>
            match parsed_def_typ "keep" decls {
                Option.some typ =>
                    match binder_domain_named "a" typ {
                        Option.some dom => is_var_named "A" dom,
                        Option.none => false,
                    },
                Option.none => false,
            },
        fail _ => false,
    }

#[partial]
def parse_decl_succeeds (r : ParseResult ParseDecl) : Bool :=
    match r {
        success _ _ => true,
        fail _ => false
    }

#[test]
def test_roundtrip_use_glob : Bool :=
    match use_parser "use init::io {*}" {
        success _ out => parse_decl_succeeds (use_parser (show_decl (lower_parse_decl lower_ctx_bare out))),
        fail _ => false
    }

#[test]
def test_roundtrip_use_nested : Bool :=
    match use_parser "use init::io {file {read}}" {
        success _ out => parse_decl_succeeds (use_parser (show_decl (lower_parse_decl lower_ctx_bare out))),
        fail _ => false
    }

#[test]
def test_roundtrip_use_nested_rename : Bool :=
    match use_parser "use init::io {file as f {read}}" {
        success _ out => parse_decl_succeeds (use_parser (show_decl (lower_parse_decl lower_ctx_bare out))),
        fail _ => false
    }

/// A DOTTED brace item (`{List.length}`) names ONE dotted declaration, not
/// a sub-module -- `use_brace_item_name_dotted` keeps the item whole, so
/// it must survive parse -> print -> re-parse unchanged.
#[test]
def test_roundtrip_use_dotted_item : Bool :=
    match use_parser "use std::list {List.length}" {
        success _ out => parse_decl_succeeds (use_parser (show_decl (lower_parse_decl lower_ctx_bare out))),
        fail _ => false
    }

/// The same, renamed (`{List.length as len}`) -- the `as` arm goes through
/// its own parser entry point, so it needs its own round trip.
#[test]
def test_roundtrip_use_dotted_item_rename : Bool :=
    match use_parser "use std::list {List.length as len}" {
        success _ out => parse_decl_succeeds (use_parser (show_decl (lower_parse_decl lower_ctx_bare out))),
        fail _ => false
    }

/// The sub-module arm still wins over the dotted-name arm when what follows
/// the identifier is a brace list: `file {read}` is a sub-module filter,
/// `List.length` is a name. Both must keep parsing (alt ordering in
/// `use_brace_item`).
#[test]
def test_roundtrip_use_dotted_and_sub_together : Bool :=
    match use_parser "use init::io {file {read}, String.length}" {
        success _ out => parse_decl_succeeds (use_parser (show_decl (lower_parse_decl lower_ctx_bare out))),
        fail _ => false
    }

#[test]
def test_roundtrip_open_filtered : Bool :=

    match open_parser "open io {println}" {
        success _ out => parse_decl_succeeds (open_parser (show_decl (lower_parse_decl lower_ctx_bare out))),
        fail _ => false
    }

#[test]
def test_roundtrip_scoped_open : Bool :=
    match open_parser "open io {println} in def main : IO Unit := println \"hi\"" {
        success _ out => parse_decl_succeeds (open_parser (show_decl (lower_parse_decl lower_ctx_bare out))),
        fail _ => false
    }
