/// Module loading infrastructure for the self-hosted compiler.
/// Parses source text and builds scope data from declarations.

use io
use lang.types
use lang.parser
use lang.parser.core
use lang.parser.combinators
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

/// Module path for the prelude
@[partial]
def prelude_module_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "'prelude") List.empty)

/// Parse all declarations from source text.
/// Uses t2_decls_parser which properly handles docstrings.
@[partial]
def parse_all_decls (input : String) : ParseResult (List Decl) :=
    lang.parser.t2_decls_parser input

/// Parse source text, returning the parsed declarations or none on parse error.
@[partial]
def try_parse_decls (input : String) : Option (List Decl) :=
    match parse_all_decls input {
        ParseResult.success _ decls => Option.some decls,
        ParseResult.fail _ => Option.none,
    }

/// Parse source text and build scope data for a module.
/// Does not resolve `use` dependencies — only parses and builds
/// scope for the declarations in the given text.
@[partial]
def parse_module (path : ModulePath) (text : String) : ScopeData :=
    let empty_decls : List Decl := List.empty in
    match parse_all_decls text {
        ParseResult.success _ decls => build_scope_from_decls path decls,
        ParseResult.fail _ => build_scope_from_decls path empty_decls
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
                    else String.concat (String.concat hd_str "/") rest_str,
                _ => ""
            },
        _ => ""
    }

/// Check if a file exists using native IO
@[partial]
def file_exists_b (path : String) : Bool := match IO.file_exists path {
    IO.io b => b // TODO avoid unwrapping
}

/// Convert a ModulePath to a string representation
@[partial]
def module_path_to_string (mp : ModulePath) : String := 
    match mp {
        ModulePath.mp ids => 
            match ids {
                List.empty => "",
                List.cons hd rest =>
                    let hd_str : String := identifier_to_string hd in
                    let rest_str : String := module_path_to_string (ModulePath.mp rest) in
                    if String.beq rest_str "" 
                    then hd_str 
                    else String.concat (String.concat hd_str ".") rest_str,
                _ => ""
            },
        _ => ""
    }

/// Find the last index of the '/' character in a string, returning -1 if not found
@[partial]
def string_find_last_slash (s : String) : I64 := 
    string_find_last_slash_go s (String.length s)

/// '/' character as U8
@[partial]
def slash_byte : U8 := 47u8

@[partial]
def string_find_last_slash_go (s : String) (idx : I64) : I64 := 
    if I64.lt 0 idx then
        match String.get s (idx - 1) {
            Option.some byte_val =>
                // '/' is ASCII 47
                if U8.beq byte_val slash_byte then
                    idx - 1
                else
                    string_find_last_slash_go s (idx - 1),
            Option.none => -1
        }
    else
        -1

/// Extract the directory from a file path
/// e.g., "init/process.mo" -> "init/"
@[partial]
def extract_directory (file_path : String) : String := 
    let last_slash_idx : I64 := string_find_last_slash file_path in
    if I64.lt last_slash_idx 0 then
        ""
    else
        String.slice file_path 0 last_slash_idx

/// Join two path components with a separator
@[partial]
def path_join (a : String) (b : String) : String := 
    if String.beq a "" then
        b
    else if String.beq b "" then
        a
    else if String.ends_with a "/" then
        String.concat a b
    else
        String.concat (String.concat a "/") b

/// Resolve a module path to a file path, trying different directories
/// First tries relative to base_dir, then falls back to standard locations
@[partial]
def resolve_module_file (base_dir : String) (mp : ModulePath) : Option String := 
    let mp_str : String := module_path_to_file mp in
    let with_extension : String := String.concat mp_str ".mo" in
    
    // Special case: 'prelude maps to init/prelude.mo
    if String.beq mp_str "'prelude" then
        let prelude_path : String := "init/prelude.mo" in
        if file_exists_b prelude_path then
            Option.some prelude_path
        else
            Option.none
    else
        // 1. Try relative to base directory
        let relative_path : String := path_join base_dir with_extension in
        if file_exists_b relative_path then
            Option.some relative_path
        else
            // 2. Try direct path (for fully qualified paths like "init/io")
        let direct_path : String := with_extension in
        if file_exists_b direct_path then
            Option.some direct_path
        else
            // 3. Try init/ directory
            let init_path : String := String.concat "init/" with_extension in
            if file_exists_b init_path then
                Option.some init_path
            else
                // 4. Try std/ directory
                let std_path : String := String.concat "std/" with_extension in
                if file_exists_b std_path then
                    Option.some std_path
                else
                    // 5. Try lang/ directory
                    let lang_path : String := String.concat "lang/" with_extension in
                    if file_exists_b lang_path then
                        Option.some lang_path
                    else
                        // 6. Try examples/ directory
                        let examples_path : String := String.concat "examples/" with_extension in
                        if file_exists_b examples_path then
                            Option.some examples_path
                        else
                            Option.none

/// Try to read a module file from disk, relative to a base directory
@[partial]
def try_read_module_file (base_dir : String) (mp : ModulePath) : Option String := 
    match resolve_module_file base_dir mp {
        Option.some resolved => match IO.read_file resolved { io s => Option.some s },
        Option.none => Option.none
    }

/// Try to read a module file from disk (default base directory is empty)
@[partial]
def try_read_module_file_default (mp : ModulePath) : Option String := 
    try_read_module_file "" mp

/// Load a module by its ModulePath, returning parsed declarations or none
/// base_dir is the directory to resolve relative imports from
@[partial]
def load_module_decls (base_dir : String) (mp : ModulePath) : Option (List Decl) := 
    match try_read_module_file base_dir mp {
        Option.some content => 
            match parse_all_decls content {
                ParseResult.success _ decls => Option.some decls,
                ParseResult.fail _ => Option.none
            },
        Option.none => Option.none
    }

/// Load a module by its ModulePath with default base directory
@[partial]
def load_module_decls_default (mp : ModulePath) : Option (List Decl) := 
    load_module_decls "" mp

/// Build a Scope from a ModulePath by loading and parsing the file
/// base_dir is the directory to resolve relative imports from
@[partial]
def load_module_scope (base_dir : String) (mp : ModulePath) : Option ScopeData := 
    match load_module_decls base_dir mp {
        Option.some decls => 
            let sd : ScopeData := build_scope_from_decls mp decls in
            Option.some sd,
        Option.none => Option.none
    }

/// Build a Scope from a ModulePath with default base directory
@[partial]
def load_module_scope_default (mp : ModulePath) : Option ScopeData := 
    load_module_scope "" mp

/// Extract all transitive dependencies from a list of declarations
/// with a base directory for resolving relative imports
@[partial]
def extract_all_dependencies (base_dir : String) (decls : List Decl) : List ModulePath := 
    let direct_deps : List ModulePath := extract_use_decls decls in
    let empty_mp_list : List ModulePath := List.empty in
    extract_all_dependencies_go base_dir direct_deps empty_mp_list empty_mp_list

/// Extract all transitive dependencies with cycle detection
/// visiting: modules currently being visited (for cycle detection)
/// visited: modules already fully processed
@[partial]
def extract_all_dependencies_go 
    (base_dir : String) 
    (to_visit : List ModulePath) 
    (visiting : List ModulePath) 
    (visited : List ModulePath) : 
    List ModulePath := 
    match to_visit {
        List.empty => visited,
        List.cons head tail =>
            if list_contains visiting head then
                // Circular dependency detected - skip to avoid infinite loop
                extract_all_dependencies_go base_dir tail visiting visited
            else if list_contains visited head then
                // Already processed, skip
                extract_all_dependencies_go base_dir tail visiting visited
            else
                // Process this module
                let new_visiting : List ModulePath := List.cons head visiting in
                match load_module_decls base_dir head {
                    Option.some dep_decls =>
                        // First, find the actual file path for this module
                        let resolved_path : Option String := resolve_module_file base_dir head in
                        let new_base_dir : String := 
                            match resolved_path {
                                Option.some fp => extract_directory fp,
                                Option.none => base_dir
                            } in
                        let dep_deps : List ModulePath := extract_use_decls dep_decls in
                        let new_to_visit : List ModulePath := List.append dep_deps tail in
                        let new_visited : List ModulePath := List.cons head visited in
                        extract_all_dependencies_go new_base_dir new_to_visit new_visiting new_visited,
                    Option.none =>
                        // Module not found, skip but continue with tail
                        extract_all_dependencies_go base_dir tail new_visiting visited
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
                list_contains rest x,
        _ => false
    }

/// Load all dependencies for a module and merge their scopes
/// base_dir is the directory to resolve the initial module from
@[partial]
def load_module_with_dependencies (base_dir : String) (mp : ModulePath) : Option Scope := 
    match load_module_decls base_dir mp {
        Option.some decls =>
            // Get the actual file path for this module to determine its directory
            let resolved_path : Option String := resolve_module_file base_dir mp in
            let module_base_dir : String := 
                match resolved_path {
                    Option.some fp => extract_directory fp,
                    Option.none => base_dir
                } in
            let all_deps : List ModulePath := extract_all_dependencies module_base_dir decls in
            let loaded_deps : List ScopeData := load_dependency_scopes module_base_dir all_deps List.empty in
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

/// Load all dependencies for a module with default base directory
@[partial]
def load_module_with_dependencies_default (mp : ModulePath) : Option Scope := 
    load_module_with_dependencies "" mp

/// Load all declarations for a module and its transitive dependencies.
/// Returns Option (List Decl) where the list contains all declarations from
/// the module and all its dependencies, suitable for compilation.
@[partial]
def load_module_decls_with_dependencies (base_dir : String) (mp : ModulePath) : Option (List Decl) := 
    // First load the main module's declarations
    match load_module_decls base_dir mp {
        Option.some main_decls =>
            // Get the actual file path for this module to determine its directory
            let resolved_path : Option String := resolve_module_file base_dir mp in
            let module_base_dir : String := 
                match resolved_path {
                    Option.some fp => extract_directory fp,
                    Option.none => base_dir
                } in
            // Extract all transitive dependencies
            let all_deps : List ModulePath := extract_all_dependencies module_base_dir main_decls in
            // Always include prelude as a default dependency
            let all_deps_with_prelude : List ModulePath := List.cons prelude_module_path all_deps in
            // Load all dependency declarations
            let dep_decls : List Decl := load_dependency_decls module_base_dir all_deps_with_prelude List.empty in
            // Combine: dependencies first, then main module
            let all_decls : List Decl := list_append dep_decls main_decls in
            Option.some all_decls,
        Option.none => Option.none
    }

/// Load declarations for a list of module paths
@[partial]
def load_dependency_decls (base_dir : String) (deps : List ModulePath) (acc : List Decl) : List Decl := 
    match deps {
        List.empty => acc,
        List.cons head tail =>
            // Try to resolve and load each dependency
            match load_module_decls base_dir head {
                Option.some decls => load_dependency_decls base_dir tail (list_append decls acc),
                Option.none => 
                    // If not found with base_dir, try with empty base_dir (global search)
                    match load_module_decls_default head {
                        Option.some decls => load_dependency_decls base_dir tail (list_append decls acc),
                        Option.none => load_dependency_decls base_dir tail acc
                    }
            }
    }

/// Load all declarations for a module and its dependencies with default base directory
@[partial]
def load_module_decls_with_dependencies_default (mp : ModulePath) : Option (List Decl) := 
    load_module_decls_with_dependencies "" mp

/// Load scope data for a list of module paths, with base directory for resolution
/// Each module is loaded once, and we try to resolve it from the base_dir
@[partial]
def load_dependency_scopes (base_dir : String) (deps : List ModulePath) (acc : List ScopeData) : List ScopeData := 
    match deps {
        List.empty => acc,
        List.cons head tail =>
            // Try to resolve and load each dependency
            match load_module_scope base_dir head {
                Option.some sd => load_dependency_scopes base_dir tail (List.cons sd acc),
                Option.none => 
                    // If not found with base_dir, try with empty base_dir (global search)
                    match load_module_scope_default head {
                        Option.some sd => load_dependency_scopes base_dir tail (List.cons sd acc),
                        Option.none => load_dependency_scopes base_dir tail acc
                    }
            }
    }

/// Merge two ScopeData structures
@[partial]
def merge_scope_data (sd1 : ScopeData) (sd2 : ScopeData) : ScopeData := 
    match sd1 {
        ScopeData.mk dr1 cd1 ins1 ind1 cls1 inf1 conf1 =>
            match sd2 {
                ScopeData.mk dr2 cd2 ins2 ind2 cls2 inf2 conf2 =>
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
/// The file_path is used to determine the directory for resolving relative imports
@[partial]
def build_scope_with_deps (file_path : String) (mod_name : String) : Option Scope := 
    let base_dir : String := extract_directory file_path in
    let mp : ModulePath := ModulePath.mp (List.cons (Identifier.id mod_name) List.empty) in
    load_module_with_dependencies base_dir mp

/// Build scope and type check a file with its dependencies loaded
@[partial]
def typecheck_file_with_deps (file_path : String) (mod_name : String) : Bool := 
    if file_exists_b file_path then
        let content : String := match IO.read_file file_path { io c => c } in
        let base_dir : String := extract_directory file_path in
        let mp : ModulePath := ModulePath.mp (List.cons (Identifier.id mod_name) List.empty) in
        match load_module_with_dependencies base_dir mp {
            Option.some scope =>
                match parse_all_decls content {
                    ParseResult.success _ decls =>
                        let empty_locs : LocalScope := {
                            vars := List.empty,
                            parent := Option.none,
                        } in
                        typecheck_module_with_scope scope decls empty_locs,
                    ParseResult.fail _ => false
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
        Def.mk _name typ body _constraints _attrs =>
            // Skip native/abstract definitions (body is Term.hole)
            if is_term_hole body then
                true
            else
                match type_check body Term.hole scope empty_local_types locals {
                    Result.ok _ => true,
                    Result.err _ => false
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
        Inductive.mk _name _params _typ constructors _attrs =>
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
        InductConstructor.mk _name params typ =>
            match type_check typ Term.hole scope empty_local_types locals {
                Result.ok _ => true,
                Result.err _ => false
            }
    }

@[test]
def test_parse_all_decls_empty : Bool :=
    match parse_all_decls "" {
        ParseResult.success _ _ => true,
        ParseResult.fail _ => false
    }

// --- Integration: parse source text, build scope, resolve names ---

@[test]
def test_parse_def_resolve : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    match parse_all_decls "def foo : Bool := true" {
        ParseResult.success _ decls =>
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
                Result.ok _ => true,
                Result.err _ => false
            },
        ParseResult.fail _ => false
    }

@[test]
def test_parse_type_resolve_inductive : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    match parse_all_decls "type Color { red, green }" {
        ParseResult.success _ decls =>
            let sd : ScopeData := build_scope_from_decls path decls in
            let no_parent : Option Scope := Option.none in
            let scope : Scope := {
                module_id := path,
                scope := sd,
                parent := no_parent,
            } in
            let color_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Color") List.empty) in
            match scope_find_inductive color_path scope {
                Result.ok _ => true,
                Result.err _ => false
            },
        ParseResult.fail _ => false
    }

@[test]
def test_parse_type_constructor_resolves : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    match parse_all_decls "type Color { red, green }" {
        ParseResult.success _ decls =>
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
                Result.ok _ => true,
                Result.err _ => false
            },
        ParseResult.fail _ => false
    }

@[test]
def test_parse_if_body_def_resolves : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    match parse_all_decls "def test_bool_true : Bool := if true then true else false" {
        ParseResult.success _ decls =>
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
                Result.ok _ => true,
                Result.err _ => false
            },
        ParseResult.fail _ => false
    }

@[test]
def test_parse_multiple_decls_resolve : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    match parse_all_decls "def a : Bool := true type T { mk }" {
        ParseResult.success _ decls =>
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
                Result.ok _ => true,
                Result.err _ => false
            },
        ParseResult.fail _ => false
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
        Result.ok _ => true,
        Result.err _ => false
    }

@[test]
def test_parse_use_decl_ignored_in_scope : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    match parse_all_decls "use prelude def bar : Bool := true" {
        ParseResult.success _ decls =>
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
                Result.ok _ => true,
                Result.err _ => false
            },
        ParseResult.fail _ => false
    }
