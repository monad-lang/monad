/// Module loading infrastructure for the self-hosted compiler.
/// Parses source text and builds scope data from declarations.

use lang.types
use lang.parser
use lang.scope
use std.list

open types
open parser
open scope

/// Parse all declarations from source text.
/// Repeatedly consumes whitespace and parses one declaration,
/// accumulating into a List Decl. Stops when no more declarations
/// can be parsed.
@[partial]
def parse_all_decls (input : String) : ParseResult (List Decl) :=
    let decl_parser : (String -> ParseResult Decl) := fn s => lang.parser.t2_decl_parser (lang.parser.skip_spaces s) in
    lang.parser.many0 decl_parser input

/// Parse source text, returning the parsed declarations or none on parse error.
@[partial]
def try_parse_decls (input : String) : Option (List Decl) :=
    match parse_all_decls input {
        success _ decls => Option.some decls,
        fail _ => Option.none,
    }

/// Parse source text and build scope data for a module.
/// Does not resolve `use` dependencies — only parses and builds
/// scope for the declarations in the given text.
@[partial]
def parse_module (path : ModulePath) (text : String) : ScopeData :=
    let empty_decls : List Decl := List.empty in
    match parse_all_decls text {
        success _ decls => build_scope_from_decls path decls,
        fail _ => build_scope_from_decls path empty_decls
    }

@[test]
def test_parse_all_decls_empty : Bool :=
    match parse_all_decls "" {
        success _ _ => true,
        fail _ => false
    }

// --- Integration: parse source text, build scope, resolve names ---

@[test]
def test_parse_def_resolve : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    match parse_all_decls "def foo : Bool := true" {
        success _ decls =>
            let sd : ScopeData := build_scope_from_decls path decls in
            let no_parent : Option Scope := Option.none in
            let scope : Scope := {
                module_id := path,
                scope := sd,
                parent := no_parent,
            } in
            let foo_ref : NameRef := NameRef.nid (Identifier.id "foo") in
            let no_vars : List LocalVar := List.empty in
            let no_loc_parent : Option LocalScope := Option.none in
            let empty_locals : LocalScope := {
                vars := no_vars,
                parent := no_loc_parent,
            } in
            match scope_resolve_name foo_ref scope empty_locals {
                ok _ => true,
                err _ => false
            },
        fail _ => false
    }

@[test]
def test_parse_type_resolve_inductive : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    match parse_all_decls "type Color { red, green }" {
        success _ decls =>
            let sd : ScopeData := build_scope_from_decls path decls in
            let no_parent : Option Scope := Option.none in
            let scope : Scope := {
                module_id := path,
                scope := sd,
                parent := no_parent,
            } in
            let color_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Color") List.empty) in
            match scope_find_inductive color_path scope {
                ok _ => true,
                err _ => false
            },
        fail _ => false
    }

@[test]
def test_parse_type_constructor_resolves : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    match parse_all_decls "type Color { red, green }" {
        success _ decls =>
            let sd : ScopeData := build_scope_from_decls path decls in
            let no_parent : Option Scope := Option.none in
            let scope : Scope := {
                module_id := path,
                scope := sd,
                parent := no_parent,
            } in
            let red_ref : NameRef := NameRef.nid (Identifier.id "red") in
            let no_vars : List LocalVar := List.empty in
            let no_loc_parent : Option LocalScope := Option.none in
            let empty_locals : LocalScope := {
                vars := no_vars,
                parent := no_loc_parent,
            } in
            match scope_resolve_name red_ref scope empty_locals {
                ok _ => true,
                err _ => false
            },
        fail _ => false
    }

@[test]
def test_parse_if_body_def_resolves : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    match parse_all_decls "def test_bool_true : Bool := if true then true else false" {
        success _ decls =>
            let sd : ScopeData := build_scope_from_decls path decls in
            let no_parent : Option Scope := Option.none in
            let scope : Scope := {
                module_id := path,
                scope := sd,
                parent := no_parent,
            } in
            let name_ref : NameRef := NameRef.nid (Identifier.id "test_bool_true") in
            let no_vars : List LocalVar := List.empty in
            let no_loc_parent : Option LocalScope := Option.none in
            let empty_locals : LocalScope := {
                vars := no_vars,
                parent := no_loc_parent,
            } in
            match scope_resolve_name name_ref scope empty_locals {
                ok _ => true,
                err _ => false
            },
        fail _ => false
    }

@[test]
def test_parse_multiple_decls_resolve : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    match parse_all_decls "def a : Bool := true type T { mk }" {
        success _ decls =>
            let sd : ScopeData := build_scope_from_decls path decls in
            let no_parent : Option Scope := Option.none in
            let scope : Scope := {
                module_id := path,
                scope := sd,
                parent := no_parent,
            } in
            let a_ref : NameRef := NameRef.nid (Identifier.id "a") in
            let no_vars : List LocalVar := List.empty in
            let no_loc_parent : Option LocalScope := Option.none in
            let empty_locals : LocalScope := {
                vars := no_vars,
                parent := no_loc_parent,
            } in
            match scope_resolve_name a_ref scope empty_locals {
                ok _ => true,
                err _ => false
            },
        fail _ => false
    }

@[test]
def test_parse_module_builds_scope : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    let sd : ScopeData := parse_module path "def hello : Bool := true" in
    let no_parent : Option Scope := Option.none in
    let scope : Scope := {
        module_id := path,
        scope := sd,
        parent := no_parent,
    } in
    let hello_ref : NameRef := NameRef.nid (Identifier.id "hello") in
    let no_vars : List LocalVar := List.empty in
    let no_loc_parent : Option LocalScope := Option.none in
    let empty_locals : LocalScope := {
        vars := no_vars,
        parent := no_loc_parent,
    } in
    match scope_resolve_name hello_ref scope empty_locals {
        ok _ => true,
        err _ => false
    }

@[test]
def test_parse_use_decl_ignored_in_scope : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    match parse_all_decls "use prelude def bar : Bool := true" {
        success _ decls =>
            let sd : ScopeData := build_scope_from_decls path decls in
            let no_parent : Option Scope := Option.none in
            let scope : Scope := {
                module_id := path,
                scope := sd,
                parent := no_parent,
            } in
            let bar_ref : NameRef := NameRef.nid (Identifier.id "bar") in
            let no_vars : List LocalVar := List.empty in
            let no_loc_parent : Option LocalScope := Option.none in
            let empty_locals : LocalScope := {
                vars := no_vars,
                parent := no_loc_parent,
            } in
            match scope_resolve_name bar_ref scope empty_locals {
                ok _ => true,
                err _ => false
            },
        fail _ => false
    }
