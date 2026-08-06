/// Module loading infrastructure for the self-hosted compiler.
/// Parses source text and builds scope data from declarations.

use io {IO, file_exists, println, read_file}
use lang.types {
  Decl, Def, Identifier, InductConstructor, Inductive, LoadedModules, LocalScope,
  LocalVar, ModulePath, NameRef, Scope, ScopeData, ScopeInstance, Term, def_d,
  hole, id, inductive_d, mk, mp, name, nid, to_name, use_d,
}
use lang.parser {decls_parser, module_path_to_string}
use lang.parser.core {ParseResult, fail, mk, success}
use lang.scope {
  build_scope_from_decls, list_append, modpath_eq, scope_data_empty,
  scope_find_inductive, scope_resolve_name,
}
use lang.typecheck.infer {empty_local_types, empty_locals, mk, type_check}
use std.list {Show, all, length}
use std.show {Show}

open IO {file_exists, println, read_file}
open types {}
open parser {}
open parser.core {}
open ParseResult {fail, success}
open scope {}
open infer {}

/// Module path for the init directory
def init_module_file_path (name : String) : String := "init/" ++ name ++ ".mo"

/// Module path for the std directory
def std_module_path (name : String) : String := "std/" ++ name ++ ".mo"

/// Module path for the examples directory
def examples_module_path (name : String) : String := "examples/" ++ name ++ ".mo"

/// Module path for the lang directory
def lang_module_path (name : String) : String := "lang/" ++ name ++ ".mo"

/// Module path for the prelude
def prelude_module_path : ModulePath := ModulePath.mp [Identifier.id "prelude"]

def init_module_path : ModulePath := ModulePath.mp [Identifier.id "init"]

/// Parse all declarations from source text.
/// Uses decls_parser which properly handles docstrings.
def parse_all_decls (input : String) : ParseResult (List Decl) :=
    lang.parser.decls_parser input

/// Parse source text, returning the parsed declarations or none on parse error.
def try_parse_decls (input : String) : Option (List Decl) :=
    let result : ParseResult (List Decl) := parse_all_decls input in
    match result {
        ParseResult.success _ decls => Option.some decls,
        ParseResult.fail _ => Option.none,
    }

/// Parse source text and build scope data for a module.
/// Does not resolve `use` dependencies — only parses and builds
/// scope for the declarations in the given text.
def parse_module (path : ModulePath) (text : String) : ScopeData :=
    let empty_decls : List Decl := List.empty in
    let result : ParseResult (List Decl) := parse_all_decls text in
    match result {
        ParseResult.success _ decls => build_scope_from_decls path decls,
        ParseResult.fail _ => build_scope_from_decls path empty_decls
    }

// --- Module dependency loading ---

/// Extract use declarations from a list of declarations
def extract_use_decls (decls : List Decl) : List ModulePath :=
    extract_use_decls_go decls List.empty

#[partial]
def extract_use_decls_go (decls : List Decl) (acc : List ModulePath) : List ModulePath :=
    match decls {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Decl.use_d path _ => extract_use_decls_go rest (List.cons path acc),
                _ => extract_use_decls_go rest acc
            }
    }

/// Convert an Identifier to a String
def identifier_to_string (id : Identifier) : String :=
    match id {
        Identifier.id s => s
    }

/// Convert a ModulePath to a file path string (without .mo extension)
#[terminating]
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
def file_exists (path : String) : IO Bool := IO.file_exists path

/// Convert a ModulePath to a string representation
#[partial]
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
                    else String.concat (String.concat hd_str ".") rest_str
            }
    }

/// Convert a file path to a ModulePath
#[partial]
def file_path_to_module_path (path : String) : ModulePath :=
    let last_slash : I64 := string_find_last_slash path in
    let file_name : String :=
        if I64.lt 0 last_slash then
            String.slice path 0 (String.length path)
        else
            String.slice path (last_slash + 1) (String.length path) in
    let name_without_ext : String :=
        if String.ends_with file_name ".mo" then
            String.slice file_name 0 (String.length file_name - 3)
        else
            file_name in
    ModulePath.mp [Identifier.id name_without_ext]

/// Find the last index of the '/' character in a string, returning -1 if not found
def string_find_last_slash (s : String) : I64 :=
    string_find_last_slash_go s (String.length s)

/// '/' character as U8
def slash_byte : U8 := 47u8

#[terminating]
def string_find_last_slash_go (s : String) (idx : I64) : I64 :=
    if I64.lt 0 idx then
        match (String.get s (idx - 1) : Option U8) {
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
def extract_directory (file_path : String) : String :=
    let last_slash_idx : I64 := string_find_last_slash file_path in
    if I64.lt last_slash_idx 0 then
        ""
    else
        String.slice file_path 0 last_slash_idx

/// Join two path components with a separator
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
#[partial]
def resolve_module_file (base_dir : String) (mp : ModulePath) : IO (Option String) {
    let mp_str := module_path_to_file mp;
    let with_extension := String.concat mp_str ".mo";
    let prelude_path := "init/prelude.mo";
    let relative_path := path_join base_dir with_extension;
    let direct_path := with_extension;
    let init_path := String.concat "init/" with_extension;
    let std_path := String.concat "std/" with_extension;
    let lang_path := String.concat "lang/" with_extension;
    let examples_path := String.concat "examples/" with_extension;

    if String.beq mp_str "prelude" then do {
        let exists : Bool <- file_exists prelude_path;
        if exists then do {
            return Option.some prelude_path
        } else do {
            return Option.none
        }
    } else do {
        let exists : Bool <- file_exists relative_path;
        if exists then do {
            return Option.some relative_path
        } else do {
            let exists : Bool <- file_exists direct_path;
            if exists then do {
                return Option.some direct_path
            } else do {
                let exists <- file_exists init_path;
                if exists then do {
                    return Option.some init_path
                } else do {
                    let exists <- file_exists std_path;
                    if exists then do {
                        return Option.some std_path
                    } else do {
                        let exists <- file_exists lang_path;
                        if exists then do {
                            return Option.some lang_path
                        } else do {
                            let exists <- file_exists examples_path;
                            if exists then do {
                                return Option.some examples_path
                            } else do {
                                return Option.none
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Try to read a module file from disk, relative to a base directory
#[partial]
def try_read_module_file (base_dir : String) (mp : ModulePath) : IO (Option String) {
    let resolved : Option String <- resolve_module_file base_dir mp;
    match resolved {
        Option.some resolved_path => do {
            let s : String <- IO.read_file resolved_path;
            return Option.some s
        },
        Option.none => do {
            return Option.none
        }
    }
}

/// Try to read a module file from disk (default base directory is empty)
#[partial]
def try_read_module_file_default (mp : ModulePath) : IO (Option String) :=
    try_read_module_file "" mp

/// Load a module by its ModulePath, returning parsed declarations or none
/// base_dir is the directory to resolve relative imports from
#[partial]
def load_module_decls (base_dir : String) (mp : ModulePath) : IO (Option (List Decl)) {
    let file : Option String <- try_read_module_file base_dir mp;
    match file {
        Option.some content => do {
            let result : ParseResult (List Decl) := parse_all_decls content;
            match result {
                ParseResult.success _ decls => do { return Option.some decls },
                ParseResult.fail _ => do { return Option.none }
            }
        },
        Option.none => do {
            return Option.none
        }
    }
}


/// Load a module by its ModulePath with default base directory
#[partial]
def load_module_decls_default (mp : ModulePath) : IO (Option (List Decl)) :=
    load_module_decls "" mp

/// Build a Scope from a ModulePath by loading and parsing the file
/// base_dir is the directory to resolve relative imports from
#[partial]
def load_module_scope (base_dir : String) (mp : ModulePath) : IO (Option ScopeData) {
    let opt_decls : Option (List Decl) <- load_module_decls base_dir mp;
    match opt_decls {
        Option.some decls => do {
            let sd : ScopeData := build_scope_from_decls mp decls;
            return Option.some sd
        },
        Option.none => do {
            return Option.none
        }
    }
}

/// Build a Scope from a ModulePath with default base directory
#[partial]
def load_module_scope_default (mp : ModulePath) : IO (Option ScopeData) :=
    load_module_scope "" mp

/// Extract all transitive dependencies from a list of declarations
/// with a base directory for resolving relative imports
#[partial]
def extract_all_dependencies (base_dir : String) (decls : List Decl) : IO (List ModulePath) :=
    let direct_deps : List ModulePath := extract_use_decls decls in
    let empty_mp_list : List ModulePath := List.empty in
    extract_all_dependencies_go base_dir direct_deps empty_mp_list empty_mp_list


/// Extract all transitive dependencies with cycle detection
/// visiting: modules currently being visited (for cycle detection)
/// visited: modules already fully processed
#[partial]
def extract_all_dependencies_go
    (base_dir : String)
    (to_visit : List ModulePath)
    (visiting : List ModulePath)
    (visited : List ModulePath) :
    IO (List ModulePath) :=
    match to_visit {
        List.empty => do {
            return visited
        },
        List.cons head tail =>
            if list_contains visiting head then
                // Circular dependency detected - skip to avoid infinite loop
                extract_all_dependencies_go base_dir tail visiting visited
            else if list_contains visited head then
                // Already processed, skip
                extract_all_dependencies_go base_dir tail visiting visited
            else do {
                // Process this module
                let new_visiting : List ModulePath := List.cons head visiting;
                let dep_decls_opt : Option (List Decl) <- load_module_decls base_dir head;
                match dep_decls_opt {
                    Option.some dep_decls => do {
                        // First, find the actual file path for this module
                        let resolved_path_opt : Option String <- resolve_module_file base_dir head;
                        let new_base_dir : String :=
                            match resolved_path_opt {
                                Option.some fp => extract_directory fp,
                                Option.none => base_dir
                            };
                        let dep_deps : List ModulePath := extract_use_decls dep_decls;
                        let new_to_visit : List ModulePath := List.append dep_deps tail;
                        let new_visited : List ModulePath := List.cons head visited;
                        extract_all_dependencies_go new_base_dir new_to_visit new_visiting new_visited
                    },
                    Option.none =>
                        // Module not found, skip but continue with tail
                        extract_all_dependencies_go base_dir tail new_visiting visited
                }
            }
    }

/// Check if a list contains a specific ModulePath
#[partial]
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
/// base_dir is the directory to resolve the initial module from
def load_module_with_dependencies (base_dir : String) (mp : ModulePath) : IO (Option Scope) {
    let opt_decls : Option (List Decl) <- load_module_decls base_dir mp;
    match opt_decls {
        Option.some decls => do {
            // Get the actual file path for this module to determine its directory
            let resolved_path_opt : Option String <- resolve_module_file base_dir mp;
            let module_base_dir : String :=
                match resolved_path_opt {
                    Option.some fp => extract_directory fp,
                    Option.none => base_dir
                };
            let all_deps : List ModulePath <- extract_all_dependencies module_base_dir decls;
            let loaded_deps : List ScopeData <- load_dependency_scopes module_base_dir all_deps List.empty;
            let merged_scope : ScopeData := merge_scope_data_list loaded_deps;
            let this_scope : ScopeData := build_scope_from_decls mp decls;
            let final_scope : ScopeData := merge_scope_data merged_scope this_scope;
            let scope : Scope := {
                module_id := mp,
                scope := final_scope,
                parent := Option.none,
            };
            return Option.some scope
        },
        Option.none => do {
            return Option.none
        }
    }
}

/// Load all dependencies for a module with default base directory
#[partial]
def load_module_with_dependencies_default (mp : ModulePath) : IO (Option Scope) :=
    load_module_with_dependencies "" mp

/// Load all declarations for a module and its transitive dependencies.
/// Returns Option (List Decl) where the list contains all declarations from
/// the module and all its dependencies, suitable for compilation.
#[partial]
def load_module_decls_with_dependencies (base_dir : String) (mp : ModulePath) : IO (Option (List Decl)) {
    // First load the main module's declarations
    let opt_decls : Option (List Decl) <- load_module_decls base_dir mp;
    match opt_decls {
        Option.some main_decls => do {
            // Get the actual file path for this module to determine its directory
            let resolved_path_opt : Option String <- resolve_module_file base_dir mp;
            let module_base_dir : String :=
                match resolved_path_opt {
                    Option.some fp => extract_directory fp,
                    Option.none => base_dir
                };
            // Extract all transitive dependencies
            let all_deps : List ModulePath <- extract_all_dependencies module_base_dir main_decls;
            // Always include prelude as a default dependency
            let all_deps_with_prelude : List ModulePath := List.cons prelude_module_path all_deps;
            // Load all dependency declarations
            let dep_decls : List Decl <- load_dependency_decls module_base_dir all_deps_with_prelude List.empty;
            // Combine: dependencies first, then main module
            let all_decls : List Decl := list_append dep_decls main_decls;
            return Option.some all_decls
        },
        Option.none => do {
            return Option.none
        }
    }
}

/// Load declarations for a list of module paths
#[partial]
def load_dependency_decls (base_dir : String) (deps : List ModulePath) (acc : List Decl) : IO (List Decl) :=
    match deps {
        List.empty => do {
            return acc
        },
        List.cons head tail => do {
            // Try to resolve and load each dependency
            let decls_opt : Option (List Decl) <- load_module_decls base_dir head;
            match decls_opt {
                Option.some decls => do {
                    let new_acc : List Decl := list_append decls acc;
                    load_dependency_decls base_dir tail new_acc
                },
                Option.none => do {
                    // If not found with base_dir, try with empty base_dir (global search)
                    let decls_opt : Option (List Decl) <- load_module_decls_default head;
                    match decls_opt {
                        Option.some decls => do {
                            let new_acc : List Decl := list_append decls acc;
                            load_dependency_decls base_dir tail new_acc
                        },
                        Option.none => load_dependency_decls base_dir tail acc
                    }
                }
            }
        }
    }

/// Load all declarations for a module and its dependencies with default base directory
def load_module_decls_with_dependencies_default (mp : ModulePath) : IO (Option (List Decl)) :=
    load_module_decls_with_dependencies "" mp

/// Load scope data for a list of module paths, with base directory for resolution
/// Each module is loaded once, and we try to resolve it from the base_dir
#[partial]
def load_dependency_scopes (base_dir : String) (deps : List ModulePath) (acc : List ScopeData) : IO (List ScopeData) :=
    match deps {
        List.empty => do {
            return acc
        },
        List.cons head tail => do {
            // Try to resolve and load each dependency
            let sd_opt : Option ScopeData <- load_module_scope base_dir head;
            match sd_opt {
                Option.some sd => do {
                    let new_acc : List ScopeData := List.cons sd acc;
                    load_dependency_scopes base_dir tail new_acc
                },
                Option.none => do {
                    // If not found with base_dir, try with empty base_dir (global search)
                    let sd_opt2 : Option ScopeData <- load_module_scope_default head;
                    match sd_opt2 {
                        Option.some sd => do {
                            let new_acc : List ScopeData := List.cons sd acc;
                            load_dependency_scopes base_dir tail new_acc
                        },
                        Option.none => load_dependency_scopes base_dir tail acc
                    }
                }
            }
        }
    }

/// Merge two ScopeData structures
#[partial]
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
#[partial]
def merge_scope_data_list (sds : List ScopeData) : ScopeData :=
    let empty : ScopeData := scope_data_empty in
    merge_scope_data_list_go sds empty

#[partial]
def merge_scope_data_list_go (sds : List ScopeData) (acc : ScopeData) : ScopeData :=
    match sds {
        List.empty => acc,
        List.cons sd rest =>
            let merged : ScopeData := merge_scope_data acc sd in
            merge_scope_data_list_go rest merged
    }

/// Merge two lists of ScopeInstance
#[partial]
def merge_instances (ins1 : List ScopeInstance) (ins2 : List ScopeInstance) : List ScopeInstance :=
    match ins1 {
        List.empty => ins2,
        List.cons si1 rest1 =>
            let merged_rest : List ScopeInstance := merge_instances rest1 ins2 in
            List.cons si1 merged_rest
    }

/// Helper: append two lists
#[partial]
def list_append (xs : List A) (ys : List A) : List A :=
    match xs {
        List.empty => ys,
        List.cons x rest => List.cons x (list_append rest ys)
    }

// --- Module resolution for type checking ---

/// Build a scope with all dependencies loaded for type checking a file
/// The file_path is used to determine the directory for resolving relative imports
#[partial]
def build_scope_with_deps (file_path : String) (mod_name : String) : IO (Option Scope) :=
    let base_dir : String := extract_directory file_path in
    let mp : ModulePath := ModulePath.mp [Identifier.id mod_name] in
    load_module_with_dependencies base_dir mp

/// Build scope and type check a file with its dependencies loaded
#[partial]
def typecheck_file_with_deps (file_path : String) (mod_name : String) : IO Bool {
    let exists : Bool <- file_exists file_path;
    if exists then do {
        // TODO load file once
        let content : String <- IO.read_file file_path;
        let base_dir : String := extract_directory file_path;
        let mp : ModulePath := ModulePath.mp [Identifier.id mod_name];
        let scope_opt : Option Scope <- load_module_with_dependencies base_dir mp;
        match scope_opt {
            Option.some scope =>
                let result : ParseResult (List Decl) := parse_all_decls content in
                match result {
                    ParseResult.success _ decls => do {
                        let empty_locs : LocalScope := {
                            vars := List.empty,
                            parent := Option.none,
                        };
                        return typecheck_module_with_scope scope decls empty_locs
                    },
                    ParseResult.fail _ => do {
                        return false
                    }
                },
            Option.none => do {
                return false
            }
        }
    } else do {
        return false
    }
}


/// Type check all declarations in a module with a given scope
#[partial]
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
#[partial]
def typecheck_decl_with_scope (d : Decl) (scope : Scope) (locals : LocalScope) : Bool :=
    match d {
        Decl.def_d df => typecheck_def_with_scope df scope locals,
        Decl.inductive_d ind => typecheck_inductive_with_scope ind scope locals,
        _ => true  // Skip use, open, scoped_open, infix, class, instance for now
    }

/// Type check a definition with scope
#[partial]
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
#[partial]
def is_term_hole (t : Term) : Bool :=
    match t {
        Term.hole => true,
        _ => false
    }

/// Type check an inductive with scope
#[partial]
def typecheck_inductive_with_scope (ind : Inductive) (scope : Scope) (locals : LocalScope) : Bool :=
    match ind {
        Inductive.mk _name _params _typ constructors _attrs =>
            typecheck_constructors_with_scope constructors scope locals
    }

/// Type check all constructors with scope
#[partial]
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
#[partial]
def typecheck_constructor_with_scope (c : InductConstructor) (scope : Scope) (locals : LocalScope) : Bool :=
    match c {
        InductConstructor.mk _name params typ =>
            match type_check typ Term.hole scope empty_local_types locals {
                Result.ok _ => true,
                Result.err _ => false
            }
    }

#[test]
def test_parse_all_decls_empty : Bool :=
    let result : ParseResult (List Decl) := parse_all_decls "" in
    match result {
        ParseResult.success _ _ => true,
        ParseResult.fail _ => false
    }

// --- Integration: parse source text, build scope, resolve names ---

#[test]
def test_parse_def_resolve : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    let result : ParseResult (List Decl) := parse_all_decls "def foo : Bool := true" in
    match result {
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

#[test]
def test_parse_type_resolve_inductive : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    let result : ParseResult (List Decl) := parse_all_decls "type Color { red, green }" in
    match result {
        ParseResult.success _ decls =>
            let sd : ScopeData := build_scope_from_decls path decls in
            let no_parent : Option Scope := Option.none in
            let scope : Scope := {
                module_id := path,
                scope := sd,
                parent := no_parent,
            } in
            let color_path : ModulePath := ModulePath.mp [Identifier.id "Color"] in
            match scope_find_inductive color_path scope {
                Result.ok _ => true,
                Result.err _ => false
            },
        ParseResult.fail _ => false
    }

#[test]
def test_parse_type_constructor_resolves : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    let result : ParseResult (List Decl) := parse_all_decls "type Color { red, green }" in
    match result {
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

#[test]
def test_parse_if_body_def_resolves : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    let result : ParseResult (List Decl) := parse_all_decls "def test_bool_true : Bool := if true then true else false" in
    match result {
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

#[test]
def test_parse_multiple_decls_resolve : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    let result : ParseResult (List Decl) := parse_all_decls "def a : Bool := true type T { mk }" in
    match result {
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

#[test]
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

#[test]
def test_parse_use_decl_ignored_in_scope : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    let result : ParseResult (List Decl) := parse_all_decls "use prelude def bar : Bool := true" in
    match result {
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

// === Multi-module loading with boundary preservation ===

struct ModuleInfo {
    path : ModulePath,
    file_path : String,
    decls : List Decl,
}

def show_module_info (m : ModuleInfo) : String :=
    match m {
        mk path file decls =>
            "module: " ++ Show.show path ++
            "\n\tpath: " ++ file ++
            "\n\tdecls: " ++ Show.show (List.map Decl.to_name decls : List ModulePath)
    }

instance Show ModuleInfo {
    def show (m : ModuleInfo) : String := show_module_info m
}

struct LoadedModules {
    main_module : ModuleInfo,
    all_modules : List ModuleInfo,
}

def show_loaded_modules (m : LoadedModules) : String :=
    match m {
        mk main all => "main: " ++ Show.show main ++ "\nall: " ++ Show.show all
    }

instance Show LoadedModules {
    def show (m : LoadedModules) : String := show_loaded_modules m
}

#[partial]
def get_loaded_main (loaded : LoadedModules) : ModuleInfo :=
    match loaded {
        LoadedModules.mk main_module all_modules => main_module
    }

#[partial]
def get_loaded_all (loaded : LoadedModules) : List ModuleInfo :=
    match loaded {
        LoadedModules.mk main_module all_modules => all_modules
    }

#[partial]
def list_contains_module_info (modules : List ModuleInfo) (mp : ModulePath) : Bool :=
    match modules {
        List.empty => false,
        List.cons hd rest =>
            match hd {
                ModuleInfo.mk path file_path decls =>
                    if modpath_eq path mp then
                        true
                    else
                        list_contains_module_info rest mp
            }
    }

#[partial]
def get_module_info_path (mi : ModuleInfo) : ModulePath :=
    match mi {
        ModuleInfo.mk path file_path decls => path
    }

def get_module_info_file_path (mi : ModuleInfo) : String :=
    match mi {
        ModuleInfo.mk path file_path decls => file_path
    }

def get_module_info_decls (mi : ModuleInfo) : List Decl :=
    match mi {
        ModuleInfo.mk path file_path decls => decls
    }

#[partial]
def load_module_with_info (base_dir : String) (mp : ModulePath) : IO (Option ModuleInfo) {
    let resolved_path_opt : Option String <- resolve_module_file base_dir mp;
    let actual_base_dir : String :=
        match resolved_path_opt {
            Option.some fp => extract_directory fp,
            Option.none => base_dir
        };
    let decls : Option (List Decl) <- load_module_decls actual_base_dir mp;
    return match decls {
        Option.some decls =>
            let file_path : String :=
                match resolved_path_opt {
                    Option.some fp => fp,
                    Option.none => String.concat (module_path_to_file mp) ".mo"
                } in
            Option.some { path := mp, file_path := file_path, decls := decls },
        Option.none => Option.none
    }
}

#[partial]
def load_file_modules (file_path : String) : IO (Result String LoadedModules) {
    let base_dir : String := extract_directory file_path;
    let last_slash : I64 := string_find_last_slash file_path;
    let file_name_only :=
        if I64.lt last_slash 0 then
            file_path
        else
            String.slice file_path (last_slash + 1) (String.length file_path);
    let module_name : String :=
        if String.ends_with file_name_only ".mo" then
            String.slice file_name_only 0 (String.length file_name_only - 3)
        else
            file_name_only;
    let mp : ModulePath := ModulePath.mp [Identifier.id module_name];
    println <| "loading module: " ++ module_name;
    let module : Option ModuleInfo <- load_module_with_info base_dir mp;
    match module {
        Option.some main_module =>
            match main_module {
                ModuleInfo.mk mp_path file_path decls => do {
                    let main_base_dir : String := extract_directory file_path;
                    let all_dep_paths : List ModulePath <- extract_all_dependencies main_base_dir decls;
                    let all_dep_paths_with_prelude : List ModulePath := [prelude_module_path, init_module_path] ++ all_dep_paths;
                    let dep_modules_result : Result String (List ModuleInfo) <- load_dependencies_with_info main_base_dir all_dep_paths_with_prelude List.empty;
                    return match dep_modules_result {
                      Result.ok dep_modules => 
                        let all_modules : List ModuleInfo := List.cons main_module dep_modules in
                        Result.ok { main_module := ModuleInfo.mk mp_path file_path decls, all_modules := all_modules },
                      Result.err e => Result.err e
                    }
                }
            },
        Option.none => do {
            return Result.err ("Failed to load" ++ Show.show mp)
        }
    }
}

#[partial]
def load_dependencies_with_info (base_dir : String) (deps : List ModulePath) (acc : List ModuleInfo) : IO (Result String (List ModuleInfo)) :=
    match deps {
        List.empty => do {
            return (Result.ok acc)
        },
        List.cons head tail =>
            if list_contains_module_info acc head then
                load_dependencies_with_info base_dir tail acc
            else do {
                let mi_opt : Option ModuleInfo <- load_module_with_info base_dir head;
                match mi_opt {
                    Option.some mi =>
                        match mi {
                            ModuleInfo.mk mp_path file_path decls => do {
                                let dep_base_dir : String := extract_directory file_path;
                                let dep_deps <- extract_all_dependencies dep_base_dir decls;
                                let new_acc : List ModuleInfo := List.cons mi acc;
                                let loaded_deps_result <- load_dependencies_with_info dep_base_dir dep_deps new_acc;
                                match loaded_deps_result {
                                    Result.ok loaded_deps =>
                                        load_dependencies_with_info base_dir tail loaded_deps,
                                    Result.err e => do {
                                        return Result.err e
                                    }
                                }
                            }
                        },
                    Option.none => do {
                        let module_path_str := module_path_to_string head;
                        let err_msg := "Failed to load module: " ++ module_path_str;
                        return Result.err err_msg
                    }
                }
            },
    }

