/// Module loading infrastructure for the self-hosted compiler.
/// Parses source text and builds scope data from declarations.

use io {IO, file_exists, is_dir, list_dir, println, read_file}
use lang.elaborate {free_vars}
use lang.types {
  Class, ClassDef, Decl, Def, Identifier, InductConstructor, Inductive,
  LoadedModules, LocalScope, LocalVar, ModulePath, Multiplicity, NameRef, Scope,
  ScopeData, ScopeInstance, Struct, StructField, Term, def_d, hole, id,
  inductive_d, mk, mp, name, nid, to_name, union_ids, use_d,
}
use lang.parser {decls_parser, decls_parser_strict, module_path_to_string}
use lang.parser.core {ParseResult, fail, mk, success}
use lang.parser.diagnostic {render_parse_error}
use lang.scope {
  build_scope_from_decls, list_append, modpath_eq, scope_data_add_def,
  scope_data_empty, scope_find_inductive, scope_push_local, scope_resolve_name,
}
use lang.typecheck.diagnostic {render_type_error}
use lang.typecheck.infer {empty_local_types, empty_locals, mk, type_check}
use std.list {Show, all, length}
use std.show {Show}
// `ScopeData.def_refs` is a `std.map` `HashMap ModulePath ScopeDef` (see
// `lang/scope.mo`'s own `use std.map {}` doc comment for why the import
// is empty).
use std.map {}
use std.bench {now, report}

open IO {file_exists, is_dir, list_dir, println, read_file}
open ParseResult {fail, success}

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

/// A `try_parse_decls` twin built on `decls_parser_strict` instead of
/// the lenient `decls_parser` — where `try_parse_decls` silently returns
/// `Option.none` on ANY failure (indistinguishable from "the file is
/// just empty" and, thanks to `decls_parser`'s own leniency, in
/// practice almost never even reached — see `decls_parser_strict`'s doc
/// comment, lang/parser.mo), this surfaces a real, rendered,
/// Rust-diag.rs-style diagnostic on a genuine parse failure. `path` is
/// threaded through only for the `--> path:L:C` line — pass
/// `Option.none` if unknown.
def try_parse_decls_strict (input : String) (path : Option String) : Result String (List Decl) :=
    match decls_parser_strict input {
        ParseResult.success _ decls => Result.ok decls,
        ParseResult.fail e => Result.err (render_parse_error input path e),
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
                Decl.use_d path _ _ => extract_use_decls_go rest (List.cons path acc),
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

/// Derive a module name from a file path — e.g. "examples/foo.mo" -> "foo".
/// Factored out of `load_file_modules` (below) so `check_file` can reuse
/// the exact same convention without a caller-supplied `mod_name`.
def module_name_from_path (file_path : String) : String :=
    let last_slash : I64 := string_find_last_slash file_path in
    let file_name_only : String :=
        if I64.lt last_slash 0 then
            file_path
        else
            String.slice file_path (last_slash + 1) (String.length file_path)
    in
    if String.ends_with file_name_only ".mo" then
        String.slice file_name_only 0 (String.length file_name_only - 3)
    else
        file_name_only

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

/// Same as `load_module_with_dependencies`, but always includes
/// `prelude`/`init` as implicit dependencies — matching
/// `load_file_modules`'s own convention (its
/// `all_dep_paths_with_prelude`, used by `compile`/`pretty`) — instead
/// of relying purely on the file's own explicit `use` statements.
/// `load_module_with_dependencies` itself (and `typecheck_file_with_deps`,
/// which is built on it) deliberately keep their existing, narrower
/// behavior — this is a separate function, not a replacement, so
/// nothing that already depends on that behavior changes. Needed for
/// `check_file`: almost every real `.mo` file relies on prelude/init
/// implicitly (`String`, `Bool`, `List`, `FromListLiteral`, ...)
/// without an explicit `use prelude`/`use init` line, and without
/// this, `check` would report a wall of false-positive "unknown
/// variable"/"unknown type" errors for nearly every file.
#[partial]
def load_module_with_dependencies_and_prelude (base_dir : String) (mp : ModulePath) : IO (Option Scope) {
    let opt_decls : Option (List Decl) <- load_module_decls base_dir mp;
    match opt_decls {
        Option.some decls => do {
            let resolved_path_opt : Option String <- resolve_module_file base_dir mp;
            let module_base_dir : String :=
                match resolved_path_opt {
                    Option.some fp => extract_directory fp,
                    Option.none => base_dir
                };
            let direct_deps : List ModulePath := extract_use_decls decls;
            let direct_deps_with_prelude : List ModulePath := [prelude_module_path, init_module_path] ++ direct_deps;
            let no_visited : List ModulePath := List.empty;
            let all_deps : List ModulePath <- extract_all_dependencies_go module_base_dir direct_deps_with_prelude no_visited no_visited;
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

/// The `check`-flavored twin of `build_scope_with_deps` — see
/// `load_module_with_dependencies_and_prelude`'s doc comment for why.
#[partial]
def build_scope_with_deps_and_prelude (file_path : String) (mod_name : String) : IO (Option Scope) :=
    let base_dir : String := extract_directory file_path in
    let mp : ModulePath := ModulePath.mp [Identifier.id mod_name] in
    load_module_with_dependencies_and_prelude base_dir mp

// --- Corpus-check caching: build prelude+init once, reuse across files ---
//
// `check_file`/`load_module_with_dependencies_and_prelude` above always
// walk, parse, and rebuild `ScopeData` for `prelude`+`init`'s full
// transitive closure from scratch — correct for a single file, but
// `lang/main.mo`'s `run_check_loop` calls `check_file` independently
// once per file in a corpus run, so a 47-file `check init std examples`
// redundantly repeats that same prelude/init load 47 times over (an
// O(N·D) cost, N files times D shared-dependency size, instead of
// O(D+N)) — and since this all runs *interpreted*, that redundancy is
// the dominant cost of a corpus-check run, not `scope.mo`'s per-lookup
// cost. `PreludeInitBase` + `build_prelude_init_base` below compute
// that shared closure exactly once; `covered` (the module paths it
// already resolved) seeds `extract_all_dependencies_go`'s `visited`
// set for each subsequent per-file load, so a file's own transitive
// walk correctly skips anything the shared base already covers instead
// of rediscovering and reloading it.
struct PreludeInitBase {
    scope_data : ScopeData,
    covered : List ModulePath,
}

#[partial]
def build_prelude_init_base : IO PreludeInitBase := do {
    let no_visiting : List ModulePath := List.empty;
    let no_visited : List ModulePath := List.empty;
    let roots : List ModulePath := [prelude_module_path, init_module_path];
    let all_deps : List ModulePath <- extract_all_dependencies_go "" roots no_visiting no_visited;
    let loaded_deps : List ScopeData <- load_dependency_scopes "" all_deps List.empty;
    return { scope_data := merge_scope_data_list loaded_deps, covered := all_deps }
}

/// Same shape as `load_module_with_dependencies_and_prelude`, but reuses
/// an already-built `PreludeInitBase` instead of loading prelude/init
/// from scratch — only `mp`'s own additional `use` dependencies (beyond
/// whatever `base` already covers) get freshly walked/loaded.
#[partial]
def load_module_with_dependencies_and_prelude_cached (base : PreludeInitBase) (base_dir : String) (mp : ModulePath) : IO (Option Scope) :=
    match base {
        PreludeInitBase.mk base_sd base_covered => do {
            let opt_decls : Option (List Decl) <- load_module_decls base_dir mp;
            match opt_decls {
                Option.some decls => do {
                    let resolved_path_opt : Option String <- resolve_module_file base_dir mp;
                    let module_base_dir : String :=
                        match resolved_path_opt {
                            Option.some fp => extract_directory fp,
                            Option.none => base_dir
                        };
                    let direct_deps : List ModulePath := extract_use_decls decls;
                    // Seed `visiting` (not `visited`) with `base_covered`: this
                    // function returns `visited` verbatim once `to_visit` is
                    // exhausted (line ~362), so seeding `visited` with
                    // `base_covered` (as this used to do) made every call
                    // return the ENTIRE base back to the caller as "extra"
                    // deps -- `load_dependency_scopes` below then reloaded
                    // all of prelude+init from scratch, on every single file,
                    // defeating the whole point of `PreludeInitBase` caching
                    // (measured directly, self-hosted-compiler-perf.md Step
                    // 4: this was the dominant cost of the "scope" phase,
                    // ~75% of it on a representative file). `visiting` and
                    // `visited` are both monotonically-growing "already seen"
                    // sets in this non-backtracking walk (neither is ever
                    // popped/shrunk — a dependency's own subtree is walked
                    // via the SAME sequential recursive call that continues
                    // on to its siblings, not a separate stack frame), so
                    // seeding `visiting` instead has the identical
                    // skip-if-already-covered effect during the walk (a
                    // `base_covered` entry now hits the "circular, skip"
                    // branch rather than the "already processed, skip"
                    // branch — same outcome) while leaving the returned
                    // `visited` to correctly start empty and accumulate only
                    // genuinely new, not-yet-loaded dependencies.
                    let no_visited : List ModulePath := List.empty;
                    let extra_deps : List ModulePath <- extract_all_dependencies_go module_base_dir direct_deps base_covered no_visited;
                    let loaded_extra : List ScopeData <- load_dependency_scopes module_base_dir extra_deps List.empty;
                    let merged_extra : ScopeData := merge_scope_data_list loaded_extra;
                    let merged_with_base : ScopeData := merge_scope_data base_sd merged_extra;
                    let this_scope : ScopeData := build_scope_from_decls mp decls;
                    let final_scope : ScopeData := merge_scope_data merged_with_base this_scope;
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
    }

/// The `check_file`-flavored twin of `load_module_with_dependencies_and_prelude_cached`.
#[partial]
def build_scope_with_deps_and_prelude_cached (base : PreludeInitBase) (file_path : String) (mod_name : String) : IO (Option Scope) :=
    let base_dir : String := extract_directory file_path in
    let mp : ModulePath := ModulePath.mp [Identifier.id mod_name] in
    load_module_with_dependencies_and_prelude_cached base base_dir mp

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

/// Fold `pairs` (a `HashMap.to_list` of one `ScopeData`'s `def_refs`)
/// into `acc`'s `def_refs`, via `scope_data_add_def` — each entry
/// present in both wins over whatever `acc` already had, matching
/// `merge_scope_data`'s "`sd1` wins" precedence (`sd1`'s entries are
/// the ones folded in, last).
///
/// Deliberately goes through `scope_data_add_def` (single `Map.insert`
/// call embedded directly in a `ScopeData` struct literal, already
/// proven to work) rather than returning a bare `HashMap ModulePath
/// ScopeDef` from a standalone helper and assigning that to
/// `merge_scope_data`'s own `def_refs :=` field directly — the latter
/// hits a genuine, reproducible Rust-reference-checker bug: a
/// user-defined function whose signature mentions a fully-applied
/// generic type (`HashMap ModulePath ScopeDef`) returns a result that
/// fails `type mismatch: HashMap vs. <unknown>` when placed into a
/// struct-literal field of that same declared type, even though the
/// exact same call succeeds as an ordinary `let`-bound value, and a
/// direct `Map.insert ...` call (not wrapped in a user function)
/// succeeds in that same field position. Isolated via bisection
/// (`/home/anderscs/.claude/jobs/af024b08/tmp/module_merge_isolate*.mo`,
/// not part of this repo) rather than assumed.
#[terminating]
def merge_def_refs_into (acc : ScopeData) (pairs : List (Pair ModulePath ScopeDef)) : ScopeData :=
    match pairs {
        List.empty => acc,
        List.cons p rest =>
            match p {
                Pair.pair _ v => merge_def_refs_into (scope_data_add_def acc v) rest
            }
    }

/// Merge two ScopeData structures. `sd1`'s entries win on conflict
/// (folded into `sd2` last — see `merge_def_refs_into`'s doc comment).
///
/// Short-circuits when `sd2`'s `def_refs` is empty: the general path
/// below pays `HashMap.to_list dr1` (an O(|dr1|) walk) followed by
/// |dr1| individual `Map.insert` calls into `sd2` — each one rebuilding
/// `Buckets16`'s full 16-field record (see `std/map.mo`'s
/// `HashMap.set_bucket`) — even when `sd2` starts with nothing to
/// resolve against, in which case the answer is trivially `dr1` itself,
/// no walk or reinsertion needed. Real, if secondary, win: the dominant
/// fix for this call site's actual cost was `load_module_with_
/// dependencies_and_prelude_cached`'s own `extract_all_dependencies_go`
/// seeding bug (see that call site's comment) — once `merged_extra`
/// stopped being a full reload of `base_sd`, this short-circuit is what
/// makes `merge_scope_data base_sd merged_extra` actually cheap for the
/// common case of a file with no extra (non-prelude/init) dependencies,
/// rather than still walking+reinserting `base_sd`'s several hundred
/// entries into a now-genuinely-empty `merged_extra`.
#[partial]
def merge_scope_data (sd1 : ScopeData) (sd2 : ScopeData) : ScopeData :=
    match sd1 {
        ScopeData.mk dr1 cd1 ins1 ind1 cls1 inf1 conf1 =>
            match sd2 {
                ScopeData.mk dr2 cd2 ins2 ind2 cls2 inf2 conf2 =>
                    if HashMap.is_empty dr2 then
                        {
                            def_refs := dr1,
                            class_defs := list_append cd1 cd2,
                            instances := merge_instances ins1 ins2,
                            inductives := list_append ind1 ind2,
                            classes := list_append cls1 cls2,
                            infixes := list_append inf1 inf2,
                            conflicts := list_append conf1 conf2,
                        }
                    else
                        match merge_def_refs_into sd2 (HashMap.to_list dr1) {
                            ScopeData.mk merged_dr _ _ _ _ _ _ => {
                                def_refs := merged_dr,
                                class_defs := list_append cd1 cd2,
                                instances := merge_instances ins1 ins2,
                                inductives := list_append ind1 ind2,
                                classes := list_append cls1 cls2,
                                infixes := list_append inf1 inf2,
                                conflicts := list_append conf1 conf2,
                            }
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
        Def.mk _name typ body _constraints _attrs _vis =>
            // Skip native/abstract definitions (body is Term.hole)
            if is_term_hole body then
                true
            else
                match type_check body Term.hole scope empty_local_types locals {
                    Result.ok _ => true,
                    Result.err _ => false
                }
    }

/// Check if a term is a hole. Bodyless defs with params still have their
/// `Term.hole` body wrapped in one lambda per param (`lam_params` in
/// lang/parser.mo always wraps, even around a hole) — unwrap those first,
/// or every such def looks like it has a real body and gets sent through
/// `type_check` needlessly (see the identical fix and its rationale in
/// slow_tests/typecheck_init_tests.mo's own `is_hole`).
#[partial]
def is_term_hole (t : Term) : Bool :=
    match t {
        Term.hole => true,
        Term.lam _dbg _typ body => is_term_hole body,
        _ => false
    }

// --- Implicit type-parameter skolemization for `check` ---
//
// The self-hosted `check` pipeline never runs `lang.elaborate`'s
// `elaborate_decls` (nothing in `lang/module.mo` calls it — confirmed
// by grep), so a def's/struct's/class's own free type-parameter names
// (`A`/`K`/`V`-style, e.g. `init/id.mo`'s `def Id.run (a : Id A) : A`)
// never get `Forall`-wrapped, and even if they did, `check_def_with_
// scope`'s `type_check body Term.hole scope empty_local_types locals`
// call ignores the def's own `typ` field entirely (checks `body` in
// pure infer mode) — so there'd be nowhere for a `Forall` on `typ` to
// take effect anyway. Fully wiring elaboration through the whole
// module-loading pipeline (so every downstream consumer sees Forall-
// wrapped types) is real, separate design work; this instead solves
// the immediate, narrower problem directly at each `check_*_with_scope`
// call site: find the names that LOOK like implicit type parameters in
// a def's parameter annotations, and — only for the ones that don't
// already resolve as a real global name — bind them as ordinary locals
// before checking, exactly what a proper Forall-skolemization step
// would do.
//
// `collect_param_annotation_names` deliberately only walks the leading
// `Term.lam` chain `lam_params` (lang/parser.mo) desugars a param list
// into — i.e. each param's own type ANNOTATION — and stops at the
// first non-`Lam` node (the actual computational body). This is a
// deliberately narrow scope: it must NOT descend into the body's own
// value-level references, or a genuinely misspelled/unbound name used
// as a VALUE would get silently accepted as a bogus implicit local
// instead of correctly reporting `unknown_var` — the whole point is to
// only rescue names that only ever appear in TYPE position.
#[partial]
def collect_param_annotation_names (t : Term) : List Identifier :=
    match t {
        Term.lam _dbg typ_ body =>
            union_ids (free_vars typ_ List.empty) (collect_param_annotation_names body),
        _ => List.empty
    }

/// For each candidate name that does NOT already resolve as a real
/// global (`scope_resolve_name` fails), bind it as an ordinary local —
/// the skolemization step. Names that DO resolve globally (`String`,
/// `Id`, a same-module type, ...) are left alone; `type_check` will
/// resolve them the normal way.
#[partial]
def bind_unresolved_as_local_typevars (names : List Identifier) (scope : Scope) (locals : LocalScope) : LocalScope :=
    match names {
        List.empty => locals,
        List.cons n rest =>
            let nref : NameRef := NameRef.nid n in
            match scope_resolve_name nref scope locals {
                Result.ok _ => bind_unresolved_as_local_typevars rest scope locals,
                Result.err _ =>
                    let lv : LocalVar := { name := n, typ := Term.type_ 0, multiplicity := Multiplicity.many } in
                    let extended : LocalScope := scope_push_local lv locals in
                    bind_unresolved_as_local_typevars rest scope extended
            }
    }

/// Skolemize `df`'s implicit type parameters (from both its declared
/// `typ` and its parameters' own annotations) into `locals`, ready for
/// `type_check`ing `df`'s body against.
#[partial]
def locals_with_def_typevars (df_typ : Term) (body : Term) (scope : Scope) (locals : LocalScope) : LocalScope :=
    let candidates : List Identifier := union_ids (free_vars df_typ List.empty) (collect_param_annotation_names body) in
    bind_unresolved_as_local_typevars candidates scope locals

/// Type check an inductive with scope
#[partial]
def typecheck_inductive_with_scope (ind : Inductive) (scope : Scope) (locals : LocalScope) : Bool :=
    match ind {
        Inductive.mk _name _params _typ constructors _attrs _vis =>
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

// --- `check`: multi-error typecheck pass (lang/main.mo's `check` command) ---
//
// Same per-decl walk as `typecheck_module_with_scope`/
// `typecheck_decl_with_scope` above, but rendering and *accumulating*
// every failing declaration's `TypeError` (via
// `lang.typecheck.diagnostic`'s `render_type_error`) instead of
// short-circuiting on the first `false`. Safe to accumulate here —
// unlike a parse failure, each decl already type-checks independently
// in sequence, so one failing `def` doesn't affect whether the next
// one can still be checked.
//
// KNOWN GAP, PARTIALLY FIXED: any `def` with at least one parameter
// used to report a `TypeError.unknown_var` for its OWN parameter's
// type annotation whenever that annotation referenced an inductive or
// native type by name (`Color`-style user types AND `String`/`U8`-style
// native types alike, since `init/prelude.mo` declares native
// primitive types as ordinary zero-constructor `type X {}` inductives
// that go through the exact same registration path) — root cause was
// `lang/scope.mo`'s `build_scope_inductive` registering an inductive's
// CONSTRUCTORS into scope but never the type's own NAME, so
// `scope_resolve_name` (which only ever searches the def-lookup
// namespace, never the separate `.inductives` list) couldn't resolve a
// bare type name used as an ordinary term — e.g. a `def`'s parameter
// type annotation, checked via `type_check_lam`'s infer-mode branch in
// `lang.typecheck.infer`. Fixed there (mirroring `add_builtins`' own
// `add_builtin_type`, which already did this correctly for the one
// hardcoded `Type` pseudo-type) — confirmed via `examples/hello.mo`
// dropping its two `unknown variable 'String'` errors. `struct Foo {
// ... }` declarations had the identical gap (worse: `Decl.struct_d _ =>
// acc` added NOTHING to scope at all, not even constructors) — fixed
// the same way, `build_scope_struct` in `lang/scope.mo`, which also
// synthesizes a one-constructor `Inductive` for the struct's implicit
// `mk` so match-arm validation (`find_inductive_for_cases`/
// `validate_cases_against_inductive`) has something real to check
// against instead of silently skipping (see that function's own doc
// comment for why "skip" was never a hard error, hence this was a
// soundness gap rather than a blocker for already-passing files).
// `examples/structs.mo`/`optics.mo` still fail `check` today, but for
// an unrelated, more fundamental reason: the self-hosted PARSER doesn't
// accept struct-literal (`{ field := value, ... }`) syntax yet, so
// those two files never get past parsing to exercise this fix at all —
// confirmed via a scratch file matching a struct's `mk` pattern without
// any literal syntax, which resolves and checks cleanly now.
//
// STILL OPEN: bare Forall-bound type-PARAMETER names (`A`/`B`/`C` —
// implicit/universal type variables, e.g. `init/id.mo`'s `def Id.run (a
// : Id A) : A := ...`, confirmed still failing with `unknown variable
// 'A'`) are a separate, harder gap — `A` is never a global scope name
// OR an inductive; it only exists as a `Forall`-bound name in the def's
// own (separately elaborated) `typ` field, and nothing in this
// `type_check body Term.hole scope empty_local_types locals` call ever
// walks `df`'s `typ` to skolemize its Forall binders into `locals`
// before checking `body`. Needs real design work (walk the elaborated
// `typ`'s `Forall` chain and push each bound name into `locals` as a
// `Term.type_ 0`-typed `LocalVar` before checking the body — or thread
// the declared `typ` through as `expected_type` instead of `Term.hole`
// and let `type_check_lam`'s Pi-branch handle it), not a small patch
// like the fix above — tracked as a follow-up, not fixed here.
// `check`'s *parse* phase (strict, via `try_parse_decls_strict`) is
// unaffected either way and is where most everyday syntax-error bugs
// actually get caught; the type-check phase is only as complete as
// `lang.typecheck.infer` currently is.

/// Wider coverage than `typecheck_decl_with_scope`'s `def_d`/
/// `inductive_d`-only: also checks `struct_d` (each field's type
/// annotation) and `class_d` (each method's signature type). `use_d`/
/// `open_d`/`scoped_open_d`/`infix_d` stay skipped — `use`/`open`
/// targets are already resolved (or rejected) upstream during
/// dependency/scope loading (`build_scope_with_deps_and_prelude`), so
/// there's nothing left for a per-decl pass to add; `infix_d` has no
/// body of its own to type-check. `instance_d` also stays skipped —
/// matching the Rust reference `core_check_module.rs`'s own documented
/// limitation ("`Decl::Ins` (instance) bodies are NOT checked by this
/// path"), not a self-hosted-specific shortfall to close here.
///
/// Note: class method signatures routinely reference the class's own
/// implicit type parameter (e.g. `class Show A { def show (a : A) :
/// String }`'s `A`) — the same still-open Forall-bound-type-parameter
/// gap documented above (`check_def_with_scope`'s `unknown_var 'A'`
/// case) applies here too, so most classes are expected to report an
/// error for that same, already-tracked reason until that gap closes,
/// not a new one introduced by checking classes at all.
///
/// `verbose` threads a per-declaration progress trace (which def/type/
/// constructor is currently being checked) down through every level —
/// these all became `IO`-returning (were pure `Bool`/`List String`)
/// purely to allow that `println`; the accumulation logic itself is
/// unchanged.
#[partial]
def check_module_with_scope (scope : Scope) (decls : List Decl) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match decls {
        List.empty => do { return List.empty },
        List.cons d rest => do {
            let here : List String <- check_decl_with_scope d scope locals path verbose;
            let there : List String <- check_module_with_scope scope rest locals path verbose;
            return (list_append here there)
        }
    }

#[partial]
def check_decl_with_scope (d : Decl) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match d {
        Decl.def_d df => check_def_with_scope df scope locals path verbose,
        Decl.inductive_d ind => check_inductive_with_scope ind scope locals path verbose,
        Decl.struct_d s => check_struct_with_scope s scope locals path verbose,
        Decl.class_d cls => check_class_with_scope cls scope locals path verbose,
        _ => do { return List.empty }
    }

#[partial]
def check_struct_with_scope (s : Struct) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match s {
        Struct.mk name fields _vis => do {
            if verbose then println ("  checking struct " ++ identifier_to_string name) else do { return unit };
            check_struct_fields_with_scope fields scope locals path verbose
        }
    }

#[partial]
def check_struct_fields_with_scope (fields : List StructField) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match fields {
        List.empty => do { return List.empty },
        List.cons f rest => do {
            let here : List String <- check_struct_field_with_scope f scope locals path verbose;
            let there : List String <- check_struct_fields_with_scope rest scope locals path verbose;
            return (list_append here there)
        }
    }

#[partial]
def check_struct_field_with_scope (f : StructField) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match f {
        StructField.mk name typ _default _mult => do {
            if verbose then println ("    checking field " ++ identifier_to_string name) else do { return unit };
            return (match type_check typ Term.hole scope empty_local_types locals {
                Result.ok _ => List.empty,
                Result.err e => [render_type_error (identifier_to_string name) path e]
            })
        }
    }

#[partial]
def check_class_with_scope (cls : Class) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match cls {
        Class.mk name _params _constraints methods _vis => do {
            if verbose then println ("  checking class " ++ identifier_to_string name) else do { return unit };
            check_class_methods_with_scope methods scope locals path verbose
        }
    }

#[partial]
def check_class_methods_with_scope (methods : List ClassDef) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match methods {
        List.empty => do { return List.empty },
        List.cons m rest => do {
            let here : List String <- check_class_method_with_scope m scope locals path verbose;
            let there : List String <- check_class_methods_with_scope rest scope locals path verbose;
            return (list_append here there)
        }
    }

#[partial]
def check_class_method_with_scope (m : ClassDef) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match m {
        ClassDef.mk name typ _default => do {
            if verbose then println ("    checking method " ++ identifier_to_string name) else do { return unit };
            return (match type_check typ Term.hole scope empty_local_types locals {
                Result.ok _ => List.empty,
                Result.err e => [render_type_error (identifier_to_string name) path e]
            })
        }
    }

#[partial]
def check_def_with_scope (df : Def) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match df {
        Def.mk name typ body _constraints _attrs _vis => do {
            if verbose then println ("  checking def " ++ module_path_to_string name) else do { return unit };
            if is_term_hole body then do {
                return List.empty
            } else do {
                let locals_ : LocalScope := locals_with_def_typevars typ body scope locals;
                return (match type_check body Term.hole scope empty_local_types locals_ {
                    Result.ok _ => List.empty,
                    Result.err e => [render_type_error (module_path_to_string name) path e]
                })
            }
        }
    }

#[partial]
def check_inductive_with_scope (ind : Inductive) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match ind {
        Inductive.mk name _params _typ constructors _attrs _vis => do {
            if verbose then println ("  checking type " ++ module_path_to_string name) else do { return unit };
            check_constructors_with_scope constructors scope locals path verbose
        }
    }

#[partial]
def check_constructors_with_scope (cons : List InductConstructor) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match cons {
        List.empty => do { return List.empty },
        List.cons c rest => do {
            let here : List String <- check_constructor_with_scope c scope locals path verbose;
            let there : List String <- check_constructors_with_scope rest scope locals path verbose;
            return (list_append here there)
        }
    }

#[partial]
def check_constructor_with_scope (c : InductConstructor) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match c {
        InductConstructor.mk name _params typ => do {
            if verbose then println ("    checking constructor " ++ module_path_to_string name) else do { return unit };
            return (match type_check typ Term.hole scope empty_local_types locals {
                Result.ok _ => List.empty,
                Result.err e => [render_type_error (module_path_to_string name) path e]
            })
        }
    }

struct FileCheckResult {
    path : String,
    diagnostics : List String,
}

/// The `check`-flavored twin of `typecheck_file_with_deps` above —
/// unlike that function (which uses the lenient `decls_parser` and
/// collapses everything to a bare `Bool`), this uses
/// `try_parse_decls_strict` on the target file's own content, so a
/// genuine parse failure produces a real, rendered diagnostic instead
/// of `false`, and it accumulates every failing declaration's rendered
/// type-error message instead of stopping at the first one.
/// Dependency resolution goes through `build_scope_with_deps_and_prelude`
/// (prelude/init always implicitly included, matching `compile`'s own
/// `load_file_modules` convention) rather than the narrower, existing
/// `build_scope_with_deps` — only the file being checked itself gets
/// strict *parse* treatment, keeping this change's blast radius
/// contained to what `check` needs.
#[partial]
def check_file (file_path : String) (verbose : Bool) : IO FileCheckResult {
    let exists : Bool <- file_exists file_path;
    if exists then do {
        if verbose then println ("checking " ++ file_path) else do { return unit };
        let content : String <- IO.read_file file_path;
        let mod_name : String := module_name_from_path file_path;
        let scope_opt : Option Scope <- build_scope_with_deps_and_prelude file_path mod_name;
        match scope_opt {
            Option.some scope =>
                match try_parse_decls_strict content (Option.some file_path) {
                    Result.ok decls => do {
                        let empty_locs : LocalScope := {
                            vars := List.empty,
                            parent := Option.none,
                        };
                        let diags : List String <- check_module_with_scope scope decls empty_locs (Option.some file_path) verbose;
                        return { path := file_path, diagnostics := diags }
                    },
                    Result.err diagnostic => do {
                        return { path := file_path, diagnostics := [diagnostic] }
                    }
                },
            Option.none => do {
                return { path := file_path, diagnostics := ["error: failed to load dependencies for " ++ file_path ++ " (a `use`d module failed to resolve or parse — re-run with a narrower file list, or check each `use`/`open` target under this file's search path, to isolate which one)"] }
            }
        }
    } else do {
        return { path := file_path, diagnostics := ["error: file not found: " ++ file_path] }
    }
}

/// The `PreludeInitBase`-reusing twin of `check_file` — identical
/// behavior, just avoids reloading prelude/init from scratch. This is
/// what `lang/main.mo`'s `run_check_loop` actually calls now, building
/// one `PreludeInitBase` up front and threading it through every file
/// in a corpus run instead of each `check_file` call independently
/// re-paying that cost — see `PreludeInitBase`'s own doc comment above
/// for why this matters.
#[partial]
def check_file_cached (base : PreludeInitBase) (file_path : String) (verbose : Bool) : IO FileCheckResult {
    let exists : Bool <- file_exists file_path;
    if exists then do {
        if verbose then println ("checking " ++ file_path) else do { return unit };
        let content : String <- IO.read_file file_path;
        let mod_name : String := module_name_from_path file_path;
        // Self-hosted phase-timing (silent unless `--verbose`): `Bench.now`
        // is a cheap native syscall, always taken; `Bench.report` (which
        // does the actual `println!`) is gated on `verbose` so this adds
        // no visible output — and no measurable cost — by default. Lets
        // `--verbose` runs answer "which of scope/parse/check dominates
        // wall time" directly, distinct from the Rust-level `--benchmark`
        // flag (which only times the outer per-file load).
        let scope_start : I64 := Bench.now;
        let scope_opt : Option Scope <- build_scope_with_deps_and_prelude_cached base file_path mod_name;
        let scope_elapsed : I64 := I64.sub Bench.now scope_start;
        let scope_logged : Bool := if verbose then Bench.report ("scope  " ++ file_path) scope_elapsed else true;
        match scope_opt {
            Option.some scope =>
                do {
                    let parse_start : I64 := Bench.now;
                    let parse_result : Result String (List Decl) := try_parse_decls_strict content (Option.some file_path);
                    let parse_elapsed : I64 := I64.sub Bench.now parse_start;
                    let parse_logged : Bool := if verbose then Bench.report ("parse  " ++ file_path) parse_elapsed else true;
                    match parse_result {
                        Result.ok decls => do {
                            let empty_locs : LocalScope := {
                                vars := List.empty,
                                parent := Option.none,
                            };
                            let check_start : I64 := Bench.now;
                            let diags : List String <- check_module_with_scope scope decls empty_locs (Option.some file_path) verbose;
                            let check_elapsed : I64 := I64.sub Bench.now check_start;
                            let check_logged : Bool := if verbose then Bench.report ("check  " ++ file_path) check_elapsed else true;
                            return { path := file_path, diagnostics := diags }
                        },
                        Result.err diagnostic => do {
                            return { path := file_path, diagnostics := [diagnostic] }
                        }
                    }
                },
            Option.none => do {
                return { path := file_path, diagnostics := ["error: failed to load dependencies for " ++ file_path ++ " (a `use`d module failed to resolve or parse — re-run with a narrower file list, or check each `use`/`open` target under this file's search path, to isolate which one)"] }
            }
        }
    } else do {
        return { path := file_path, diagnostics := ["error: file not found: " ++ file_path] }
    }
}

// --- Directory-recursive corpus collection (self-hosted `find *.mo`) ---
//
// `IO.list_dir`/`IO.is_dir` are directory-listing natives — one level,
// bare entry names, sorted. Everything below builds a recursive walk on
// top of them, giving `check` (via `expand_check_paths`) parity with the
// Rust reference's `check --workspace`/directory-argument support
// without shelling out to `find`.

/// Recursively collect every `*.mo` file under `dir`.
#[partial]
def collect_mo_files (dir : String) : IO (List String) := do {
    let entries : List String <- list_dir dir;
    collect_mo_files_entries dir entries
}

/// Walk `dir`'s own entries (as returned by `IO.list_dir`), recursing
/// into subdirectories and keeping `.mo`-suffixed files.
#[partial]
def collect_mo_files_entries (dir : String) (entries : List String) : IO (List String) :=
    match entries {
        List.empty => do { return List.empty },
        List.cons name rest => do {
            let path : String := dir ++ "/" ++ name;
            let is_directory : Bool <- is_dir path;
            let here : List String <- if is_directory then
                    collect_mo_files path
                else if String.ends_with path ".mo" then do {
                    return [path]
                } else do {
                    return List.empty
                };
            let there : List String <- collect_mo_files_entries dir rest;
            return (list_append here there)
        }
    }

/// Expand a list of CLI path arguments into a flat file list — any
/// entry that's a directory is recursively walked for `.mo` files via
/// `collect_mo_files`; a plain file argument is kept as-is (even if it
/// doesn't end in `.mo`, matching `check`'s existing behavior of
/// trusting an explicit file argument literally).
#[partial]
def expand_check_paths (paths : List String) : IO (List String) :=
    match paths {
        List.empty => do { return List.empty },
        List.cons p rest => do {
            let is_directory : Bool <- is_dir p;
            let here : List String <- if is_directory then collect_mo_files p else do { return [p] };
            let there : List String <- expand_check_paths rest;
            return (list_append here there)
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

// --- try_parse_decls_strict: real diagnostics on genuine parse failure ---

#[test]
def test_try_parse_decls_strict_ok_on_clean_input : Bool :=
    match try_parse_decls_strict "use prelude open IO" Option.none {
        Result.ok decls => I64.gt (List.length decls) 0,
        Result.err _ => false
    }

/// Where `try_parse_decls` silently swallows this exact failure into
/// `Option.none` with zero diagnostic content, the strict twin reports
/// a real, rendered message with position.
#[test]
def test_try_parse_decls_strict_err_has_rendered_diagnostic : Bool :=
    match try_parse_decls_strict "use prelude\n\ngarbage here" Option.none {
        Result.ok _ => false,
        Result.err msg => string_contains msg "at 3:1"
    }

#[partial]
def string_contains (haystack : String) (needle : String) : Bool :=
    if I64.gt (String.length needle) (String.length haystack)
    then false
    else if String.beq (String.slice haystack 0 (String.length needle)) needle
    then true
    else if String.is_empty haystack
    then false
    else string_contains (String.drop 1 haystack) needle

#[test]
def test_try_parse_decls_strict_err_includes_path : Bool :=
    match try_parse_decls_strict "garbage" (Option.some "examples/broken.mo") {
        Result.ok _ => false,
        Result.err msg => string_contains msg "--> examples/broken.mo:1:1"
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
    let module_name : String := module_name_from_path file_path;
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

// --- Tests: check_module_with_scope / check_file ---

#[partial]
def string_contains_helper (haystack : String) (needle : String) : Bool :=
    if I64.gt (String.length needle) (String.length haystack)
    then false
    else if String.beq (String.slice haystack 0 (String.length needle)) needle
    then true
    else if String.is_empty haystack
    then false
    else string_contains_helper (String.drop 1 haystack) needle

#[test]
def test_check_module_with_scope_all_pass : IO Bool := do {
    let path : ModulePath := ModulePath.mp List.empty;
    let result : ParseResult (List Decl) := parse_all_decls "type Color { red, green }\ndef c : Color := red";
    match result {
        ParseResult.success _ decls => do {
            let sd : ScopeData := build_scope_from_decls path decls;
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags : List String <- check_module_with_scope scope decls locals Option.none false;
            return (match diags {
                List.empty => true,
                List.cons _ _ => false
            })
        },
        ParseResult.fail _ => do { return false }
    }
}

/// Confirms `check_module_with_scope` *accumulates* — the failing
/// `bad` def doesn't stop `good` (before it) from being reported as
/// fine, and doesn't stop the walk from completing.
#[test]
def test_check_module_with_scope_accumulates_failures : IO Bool := do {
    let path : ModulePath := ModulePath.mp List.empty;
    let result : ParseResult (List Decl) := parse_all_decls "type Color { red, green }\ndef good : Color := red\ndef bad : Color := nonexistent_name";
    match result {
        ParseResult.success _ decls => do {
            let sd : ScopeData := build_scope_from_decls path decls;
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags : List String <- check_module_with_scope scope decls locals Option.none false;
            return (match diags {
                List.cons msg rest =>
                    string_contains_helper msg "unknown variable" &&
                    match rest {
                        List.empty => true,
                        List.cons _ _ => false
                    },
                List.empty => false
            })
        },
        ParseResult.fail _ => do { return false }
    }
}

#[test]
def test_check_file_reports_missing_file : Bool :=
    match check_file "definitely/does/not/exist.mo" false {
        IO.io result =>
            match result {
                FileCheckResult.mk _path diags =>
                    match diags {
                        List.cons msg rest =>
                            string_contains_helper msg "file not found" &&
                            match rest {
                                List.empty => true,
                                List.cons _ _ => false
                            },
                        List.empty => false
                    }
            }
    }

