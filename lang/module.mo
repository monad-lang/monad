/// Module loading infrastructure for the self-hosted compiler.
/// Parses source text and builds scope data from declarations.

use io
use lang.types
use lang.parser
use lang.parser.core
use lang.scope
use lang.typecheck.infer
use std.list

open IO
open types
open parser
open parser.core
open ParseResult
open scope
open infer

/// Module path for the init directory
@[partial]
def init_module_path (name : String) : String := String.concat (String.concat "init/" name) ".mo"

/// Module path for the std directory
@[partial]
def std_module_path (name : String) : String := String.concat (String.concat "std/" name) ".mo"

/// Module path for the examples directory
@[partial]
def examples_module_path (name : String) : String := String.concat (String.concat "examples/" name) ".mo"

/// Module path for the lang directory
@[partial]
def lang_module_path (name : String) : String := String.concat (String.concat "lang/" name) ".mo"

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

// --- Module dependency loading ---

/// Extract use declarations from a list of declarations
@[partial]
def extract_use_decls (decls : List Decl) : List ModulePath := 
    extract_use_decls_go decls List.empty

@[partial]
def extract_use_decls_go (decls : List Decl) (acc : List ModulePath) : List ModulePath := 
    match decls {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Decl.use_d path => extract_use_decls_go rest (List.cons path acc),
                _ => extract_use_decls_go rest acc
            }
    }

/// Convert an Identifier to a String
@[partial]
def identifier_to_string (id : Identifier) : String := 
    match id {
        Identifier.id s => s
    }

/// Convert a ModulePath to a file path string (without .mo extension)
@[terminating]
def module_path_to_file (mp : ModulePath) : String := 
    match mp {
        ModulePath.mp ids => 
            match ids {
                List.empty => "",
                List.cons hd rest =>
                    let hd_str : String := identifier_to_string hd in
                    let rest_str : String := module_path_to_file (ModulePath.mp rest) in
                    if String.beq rest_str "" 
                    then hd_str 
                    else String.concat (String.concat hd_str "/") rest_str
            }
    }

/// Check if a file exists using native IO
@[partial]
def file_exists (path : String) : Bool := IO.file_exists path

/// Resolve a module path to a file path, trying different directories
@[partial]
def resolve_module_file (mp : ModulePath) : String := 
    let mp_str : String := module_path_to_file mp in
    let with_extension : String := String.concat mp_str ".mo" in
    // Try different directories in order of preference
    // 1. Try with mp_str as a relative path (e.g., "init/io" -> "init/io.mo")
    let direct_path : String := with_extension in
    if file_exists direct_path then
        direct_path
    else
        // 2. Try init/ directory
        let init_path : String := String.concat "init/" with_extension in
        if file_exists init_path then
            init_path
        else
            // 3. Try std/ directory
            let std_path : String := String.concat "std/" with_extension in
            if file_exists std_path then
                std_path
            else
                // 4. Try lang/ directory
                let lang_path : String := String.concat "lang/" with_extension in
                if file_exists lang_path then
                    lang_path
                else
                    // 5. Try examples/ directory
                    let examples_path : String := String.concat "examples/" with_extension in
                    if file_exists examples_path then
                        examples_path
                    else
                        // Default to init/ (should not happen if file exists)
                        init_path

/// Try to read a module file from disk
@[partial]
def try_read_module_file (mp : ModulePath) : Option String := 
    let resolved := resolve_module_file mp in
    if IO.file_exists resolved then
        Option.some (IO.read_file_sync resolved)
    else
        Option.none

/// Load a module by its ModulePath, returning parsed declarations or none
@[partial]
def load_module_decls (mp : ModulePath) : Option (List Decl) := 
    match try_read_module_file mp {
        Option.some content => 
            match parse_all_decls content {
                success _ decls => Option.some decls,
                fail _ => Option.none
            },
        Option.none => Option.none
    }

/// Build a Scope from a ModulePath by loading and parsing the file
@[partial]
def load_module_scope (mp : ModulePath) : Option ScopeData := 
    match load_module_decls mp {
        Option.some decls => 
            let sd : ScopeData := build_scope_from_decls mp decls in
            Option.some sd,
        Option.none => Option.none
    }

/// Extract all transitive dependencies from a list of declarations
@[partial]
def extract_all_dependencies (decls : List Decl) : List ModulePath := 
    let direct_deps : List ModulePath := extract_use_decls decls in
    extract_all_dependencies_go direct_deps List.empty

@[partial]
def extract_all_dependencies_go (to_visit : List ModulePath) (visited : List ModulePath) : List ModulePath := 
    match to_visit {
        List.empty => visited,
        List.cons mp rest =>
            if list_contains visited mp then
                extract_all_dependencies_go rest visited
            else
                match load_module_decls mp {
                    Option.some dep_decls =>
                        let dep_deps : List ModulePath := extract_use_decls dep_decls in
                        let new_to_visit : List ModulePath := List.append dep_deps rest in
                        let new_visited : List ModulePath := List.cons mp visited in
                        extract_all_dependencies_go new_to_visit new_visited,
                    Option.none =>
                        extract_all_dependencies_go rest visited
                }
    }

/// Check if a list contains a specific ModulePath
@[partial]
def list_contains (xs : List ModulePath) (x : ModulePath) : Bool := 
    match xs {
        List.empty => false,
        List.cons hd rest =>
            if modpath_eq hd x then
                true
            else
                list_contains rest x
    }

/// Load all dependencies for a module and merge their scopes
@[partial]
def load_module_with_dependencies (mp : ModulePath) : Option Scope := 
    match load_module_decls mp {
        Option.some decls =>
            let all_deps : List ModulePath := extract_all_dependencies decls in
            let loaded_deps : List ScopeData := load_dependency_scopes all_deps List.empty in
            let merged_scope : ScopeData := merge_scope_data_list loaded_deps in
            let this_scope : ScopeData := build_scope_from_decls mp decls in
            let final_scope : ScopeData := merge_scope_data merged_scope this_scope in
            let scope : Scope := {
                module_id := mp,
                scope := final_scope,
                parent := Option.none,
            } in
            Option.some scope,
        Option.none => Option.none
    }

/// Load scope data for a list of module paths
@[partial]
def load_dependency_scopes (deps : List ModulePath) (acc : List ScopeData) : List ScopeData := 
    match deps {
        List.empty => acc,
        List.cons mp rest =>
            match load_module_scope mp {
                Option.some sd => load_dependency_scopes rest (List.cons sd acc),
                Option.none => load_dependency_scopes rest acc
            }
    }

/// Merge two ScopeData structures
@[partial]
def merge_scope_data (sd1 : ScopeData) (sd2 : ScopeData) : ScopeData := 
    match sd1 {
        mk dr1 cd1 ins1 ind1 cls1 inf1 conf1 =>
            match sd2 {
                mk dr2 cd2 ins2 ind2 cls2 inf2 conf2 =>
                    {
                        def_refs := list_append dr1 dr2,
                        class_defs := list_append cd1 cd2,
                        instances := merge_instances ins1 ins2,
                        inductives := list_append ind1 ind2,
                        classes := list_append cls1 cls2,
                        infixes := list_append inf1 inf2,
                        conflicts := list_append conf1 conf2,
                    }
            }
    }

/// Merge lists of ScopeData
@[partial]
def merge_scope_data_list (sds : List ScopeData) : ScopeData := 
    let empty : ScopeData := scope_data_empty in
    merge_scope_data_list_go sds empty

@[partial]
def merge_scope_data_list_go (sds : List ScopeData) (acc : ScopeData) : ScopeData := 
    match sds {
        List.empty => acc,
        List.cons sd rest =>
            let merged : ScopeData := merge_scope_data acc sd in
            merge_scope_data_list_go rest merged
    }

/// Merge two lists of ScopeInstance
@[partial]
def merge_instances (ins1 : List ScopeInstance) (ins2 : List ScopeInstance) : List ScopeInstance := 
    match ins1 {
        List.empty => ins2,
        List.cons si1 rest1 =>
            let merged_rest : List ScopeInstance := merge_instances rest1 ins2 in
            List.cons si1 merged_rest
    }

/// Helper: append two lists
@[partial]
def list_append (xs : List A) (ys : List A) : List A := 
    match xs {
        List.empty => ys,
        List.cons x rest => List.cons x (list_append rest ys)
    }

// --- Module resolution for type checking ---

/// Build a scope with all dependencies loaded for type checking a file
@[partial]
def build_scope_with_deps (file_path : String) (mod_name : String) : Option Scope := 
    let mp : ModulePath := ModulePath.mp (List.cons (Identifier.id mod_name) List.empty) in
    load_module_with_dependencies mp

/// Build scope and type check a file with its dependencies loaded
@[partial]
def typecheck_file_with_deps (file_path : String) (mod_name : String) : Bool := 
    if IO.file_exists file_path then
        let content : String := IO.read_file_sync file_path in
        match build_scope_with_deps file_path mod_name {
            Option.some scope =>
                match parse_all_decls content {
                    success _ decls =>
                        let empty_locs : LocalScope := {
                            vars := List.empty,
                            parent := Option.none,
                        } in
                        typecheck_module_with_scope scope decls empty_locs,
                    fail _ => false
                },
            Option.none => false
        }
    else
        false

/// Type check all declarations in a module with a given scope
@[partial]
def typecheck_module_with_scope (scope : Scope) (decls : List Decl) (locals : LocalScope) : Bool := 
    match decls {
        List.empty => true,
        List.cons d rest =>
            match typecheck_decl_with_scope d scope locals {
                true => typecheck_module_with_scope scope rest locals,
                false => false
            }
    }

/// Type check a single declaration with scope
@[partial]
def typecheck_decl_with_scope (d : Decl) (scope : Scope) (locals : LocalScope) : Bool := 
    match d {
        Decl.def_d df => typecheck_def_with_scope df scope locals,
        Decl.inductive_d ind => typecheck_inductive_with_scope ind scope locals,
        _ => true  // Skip use, open, infix, class, instance for now
    }

/// Type check a definition with scope
@[partial]
def typecheck_def_with_scope (df : Def) (scope : Scope) (locals : LocalScope) : Bool := 
    match df {
        mk _name typ body _constraints _attrs =>
            // Skip native/abstract definitions (body is Term.hole)
            if is_term_hole body then
                true
            else
                match type_check body Term.hole scope empty_local_types locals {
                    ok _ => true,
                    err _ => false
                }
    }

/// Check if a term is a hole
@[partial]
def is_term_hole (t : Term) : Bool := 
    match t {
        Term.hole => true,
        _ => false
    }

/// Type check an inductive with scope
@[partial]
def typecheck_inductive_with_scope (ind : Inductive) (scope : Scope) (locals : LocalScope) : Bool := 
    match ind {
        mk _name _params _typ constructors _attrs =>
            typecheck_constructors_with_scope constructors scope locals
    }

/// Type check all constructors with scope
@[partial]
def typecheck_constructors_with_scope (cons : List InductConstructor) (scope : Scope) (locals : LocalScope) : Bool := 
    match cons {
        List.empty => true,
        List.cons c rest =>
            match typecheck_constructor_with_scope c scope locals {
                true => typecheck_constructors_with_scope rest scope locals,
                false => false
            }
    }

/// Type check a single constructor with scope
@[partial]
def typecheck_constructor_with_scope (c : InductConstructor) (scope : Scope) (locals : LocalScope) : Bool := 
    match c {
        mk _name params typ =>
            match type_check typ Term.hole scope empty_local_types locals {
                ok _ => true,
                err _ => false
            }
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
