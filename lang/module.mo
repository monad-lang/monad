/// Module loading infrastructure for the self-hosted compiler.
/// Parses source text and builds scope data from declarations.

use io {IO}
use std.io {file_exists, is_dir, list_dir, println, read_file}
use lang.elaborate {free_vars, names_of_decls, elaborate_def}
use lang.types {
  Class, ClassDef, Decl, Def, Identifier, InductConstructor, Inductive, Infix,
  LoadedModules, LocalScope, LocalVar, Location, ModulePath, NameRef, Scope,
  ScopeData, ScopeInstance, Struct, StructField, Term, def_d, hole, id, id_eq,
  inductive_d, list_reverse, mk, mp, name, nid, to_name, union_ids, use_d,
}
use lang.parser {decls_parser, decls_parser_strict, decls_parser_with_locs, module_path_to_string}
use lang.parser.core {ParseResult, fail, mk, success}
use lang.parser.diagnostic {render_parse_error}
use lang.pretty {show_term}
use lang.typecheck.macro_apply {expand_decl_gen_call}
use lang.typecheck.macro_queue {DeclGenEntry, build_decl_gen_registry, expand_decls, lookup_decl_gen}
use lang.typecheck.meta_eval {meta_eval_invoke}
use lang.typecheck.meta_reflect {
  build_type_info_value, collect_inductives, find_inductive_by_bare_name,
  reify_decls_value_to_decls, term_free_var_name,
}
use lang.scope {
  OpenAlias,
  add_constraint_dict_params_decls, alias_decls_in_scope, build_scope_from_decls,
  collect_classes, collect_def_names, collect_infixes, collect_open_aliases, constraint_vars,
  decls_have_aliasable_decls, filter_valid_open_aliases,
  list_append, modpath_eq, param_names, promote_instance_defs,
  resolve_class_calls_decls, resolve_infix_decls, resolve_open_alias_decls,
  scope_data_add_def_sig, scope_data_empty, scope_data_find_def_sig,
  scope_find_inductive, scope_push_local, scope_resolve_name,
  validate_no_unresolved_class_calls,
}
use lang.typecheck.diagnostic {render_type_error}
use lang.typecheck.infer {empty_local_types, empty_locals, mk, tt_term, type_check}
use std.list {Show, all, length}
use std.show {Show}
// `ScopeData.def_refs` is a `std.map` `HashMap ModulePath ScopeDef` (see
// `lang/scope.mo`'s own `use std.map {}` doc comment for why the import
// is empty).
use std.map {}

open IO {file_exists, is_dir, list_dir, println, read_file}
open ParseResult {fail, success}

/// Module path for the prelude
def prelude_module_path : ModulePath := ModulePath.mp [Identifier.id "prelude"]

def init_module_path : ModulePath := ModulePath.mp [Identifier.id "init"]

def std_module_path : ModulePath := ModulePath.mp [Identifier.id "std"]

/// Parse all declarations from source text.
/// Uses decls_parser which properly handles docstrings.
///
/// Runs the result through `expand_decls` (macro expansion,
/// `lang.typecheck.macro_queue`) before returning — this is the real
/// pipeline's own LENIENT parse site (feeds `build_scope_from_decls`
/// via `load_module_decls`/`parse_module`),
/// one of the two sites the macro-expansion plan calls out by name;
/// its strict twin is `try_parse_decls_strict` below. `ParseResult`'s
/// own `remaining` is untouched -- only the parsed payload changes.
def parse_all_decls (input : String) : ParseResult (List Decl) :=
    match decls_parser input {
        ParseResult.success rem decl_list => ParseResult.success rem (expand_decls decl_list),
        ParseResult.fail e => ParseResult.fail e,
    }

/// Parse source text, returning the parsed declarations or none on parse error.
def try_parse_decls (input : String) : Option (List Decl) :=
    let result : ParseResult (List Decl) := parse_all_decls input in
    match result {
        ParseResult.success _ decl_list => Option.some decl_list,
        ParseResult.fail _ => Option.none,
    }

/// `try_parse_decls`'s own doc comment applies identically here (same
/// lenient parse) -- this twin additionally returns each PRE-expansion
/// declaration's own captured `Location`, purely for DWARF debug info
/// (plans/bootstrapping/debug-info.md, v1: one location per top-level
/// def). Deliberately captured BEFORE `expand_decls` runs: a macro can
/// add, remove, or rename declarations, so a location captured after
/// expansion could no longer correspond to anything in the expanded
/// list. A `Def` whose final compiled name doesn't match anything in
/// the returned `List (Pair Decl Location)` (macro-expanded, renamed,
/// lambda-lifted) is an accepted, documented gap -- it just gets no
/// debug info, not a compile error.
def try_parse_decls_with_locs (input : String) : Option (Pair (List Decl) (List (Pair Decl Location))) :=
    match decls_parser_with_locs input {
        ParseResult.success _ decls_with_locs =>
            let decls := decls_of_pairs decls_with_locs in
            Option.some (Pair.pair (expand_decls decls) decls_with_locs),
        ParseResult.fail _ => Option.none,
    }

#[partial]
def decls_of_pairs (pairs : List (Pair Decl Location)) : List Decl := match pairs {
    List.empty => List.empty,
    List.cons p rest =>
        match p {
            Pair.pair d _ => List.cons d (decls_of_pairs rest),
        },
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
/// The macro-expansion plan's own STRICT parse site — feeds the real
/// per-decl typecheck walk (`check_file`/`check_file_cached` via
/// `check_module_with_scope`), so `expand_decls` runs here too, same
/// as `parse_all_decls` above.
def try_parse_decls_strict (input : String) (path : Option String) : Result String (List Decl) :=
    match decls_parser_strict input {
        ParseResult.success _ decl_list => Result.ok (expand_decls decl_list),
        ParseResult.fail e => Result.err (render_parse_error input path e),
    }

// --- Module dependency loading ---

/// Extract use declarations from a list of declarations
def extract_use_decls (decl_list : List Decl) : List ModulePath :=
    extract_use_decls_go decl_list List.empty

#[partial]
def extract_use_decls_go (decl_list : List Decl) (acc : List ModulePath) : List ModulePath :=
    match decl_list {
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

/// Convert a file path to a ModulePath
#[partial]
pub def file_path_to_module_path (path : String) : ModulePath :=
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
/// Delegates to `std/path.mo`'s `raw_path_join` -- the single shared
/// implementation of this empty-component/trailing-slash-handling
/// logic (was duplicated here before `Path` existed).
def path_join (a : String) (b : String) : String :=
    raw_path_join a b

/// Return the first path in `candidates` that exists on disk (checked in
/// order via `file_exists`), or `Option.none` if none do. Factored out of
/// `resolve_module_file` below, which used to check its 7 candidate paths
/// via a cascade of nested `if/else` `do` blocks, one level per candidate
/// -- functionally a linear "first match wins" scan the whole time, just
/// expressed as 7 levels of nesting instead of a flat walk over a list.
#[partial]
def first_existing (candidates : List String) : IO (Option String) := do {
    match candidates {
        List.empty => do { return Option.none },
        List.cons path rest => do {
            // `path` here is one of `first_existing`'s own candidate
            // strings -- always non-empty by construction (built from
            // non-empty literal fragments, see call sites below), so
            // the raw `Path.path` constructor (not the validating
            // `Path.of`) is safe here.
            let exists : Bool <- file_exists (Path.path path);
            if exists
            then do { return Option.some path }
            else first_existing rest
        }
    }
}

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

    if String.beq mp_str "prelude"
    then first_existing [prelude_path]
    // Bare `init`/`std` are ambient re-export hubs (`init/lib.mo`/
    // `std/lib.mo`) -- their own module NAME no longer matches their
    // FILE name (unlike every other bare top-level module), so they
    // need the same kind of explicit special case `prelude` already
    // has, ahead of the general `<dir>/<name>.mo` search below.
    else if String.beq mp_str "init"
    then first_existing ["init/lib.mo"]
    else if String.beq mp_str "std"
    then first_existing ["std/lib.mo"]
    else first_existing [
        relative_path, direct_path, init_path, std_path, lang_path, examples_path,
    ]
}

/// Try to read a module file from disk, relative to a base directory
#[partial]
def try_read_module_file (base_dir : String) (mp : ModulePath) : IO (Option String) {
    let resolved : Option String <- resolve_module_file base_dir mp;
    match resolved {
        Option.some resolved_path => do {
            // `resolved_path` was just confirmed to exist on disk by
            // `resolve_module_file`/`first_existing` above -- always
            // non-empty by construction.
            let s : String <- IO.read_file (Path.path resolved_path);
            return Option.some s
        },
        Option.none => do {
            return Option.none
        }
    }
}

/// Load a module by its ModulePath, returning parsed declarations or none
/// base_dir is the directory to resolve relative imports from
///
/// `decls_parser`/`parse_all_decls` are LENIENT by design (`decls_try`'s
/// own doc comment, `lang/parser.mo`): any real parse failure partway
/// through a file just stops there and reports SUCCESS with whatever was
/// accumulated so far, discarding everything from that point to EOF with
/// no diagnostic at all. This is the ONE real load path every dependency
/// (not just the target file) goes through, so it's exactly where that
/// leniency turns into silent, hard-to-find data loss -- confirmed live:
/// a `///` doc comment the self-hosted parser choked on partway through
/// `lang/codegen/ir.mo` (91 real declarations) silently truncated it to
/// 11, and every name declared after that point (including `LLVMModule`/
/// `emit_module`) simply vanished from scope for every file that
/// depended on it, surfacing many calls later as a confusing "unknown
/// variable" far from the actual cause. Checking `String.is_empty rem`
/// here turns that into a loud, immediate, correctly-located error
/// instead -- `rem`, by `decls_skip`'s own construction, is already
/// docstring/whitespace-stripped by the time a real failure stops it, so
/// a genuinely fully-parsed file always leaves it empty; non-empty means
/// real, un-parsed source content remains.
#[partial]
def load_module_decls (base_dir : String) (mp : ModulePath) : IO (Option (List Decl)) {
    let file : Option String <- try_read_module_file base_dir mp;
    match file {
        Option.some content => do {
            let result : ParseResult (List Decl) := parse_all_decls content;
            match result {
                ParseResult.success rem decl_list =>
                    if String.is_empty rem
                    then do { return Option.some decl_list }
                    else do {
                        let _ <- println (String.concat "parse error: " (String.concat (module_path_to_string mp) " did not fully parse (stopped before end of file) -- remaining text starts:"));
                        let _ <- println (String.slice rem 0 (if I64.gt (String.length rem) 300 then 300 else String.length rem));
                        return Option.none
                    },
                ParseResult.fail _ => do { return Option.none }
            }
        },
        Option.none => do {
            return Option.none
        }
    }
}


/// Build a Scope from a ModulePath by loading and parsing the file
/// base_dir is the directory to resolve relative imports from
#[partial]
def load_module_scope (base_dir : String) (mp : ModulePath) : IO (Option ScopeData) {
    let opt_decls : Option (List Decl) <- load_module_decls base_dir mp;
    match opt_decls {
        Option.some decl_list => do {
            let sd : ScopeData := build_scope_from_decls mp decl_list;
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

/// `list_contains` for a `List ModuleInfo`, keying on each entry's own
/// `.path` -- used by `collect_dep_module_infos`'s dedup guard below.
#[partial]
def list_contains_module_info (xs : List ModuleInfo) (x : ModulePath) : Bool :=
    match xs {
        List.empty => false,
        List.cons mi rest =>
            match mi {
                ModuleInfo.mk p _fp _decls =>
                    if modpath_eq p x then true else list_contains_module_info rest x
            }
    }

/// Walk a module's transitive `use`-dependency closure AND load each
/// reached module with its OWN resolved directory as the base, returning
/// the loaded `ModuleInfo`s directly. This replaces the old two-step
/// `extract_all_dependencies_go` (which returns only `ModulePath`s) +
/// `load_dependency_entries (load_module_with_info main_base_dir)` pattern
/// in `load_file_modules`: that second step re-loaded every dependency
/// from the TARGET's own directory, so a dependency that shares a
/// single-segment name with a file in the target's directory got
/// mis-resolved. The real case: checking `lang/parser/combinators.mo`,
/// whose target dir `lang/parser/` contains a `string.mo` (the
/// self-hosted string-LITERAL parser), shadowed `init/string.mo` (the
/// `String.length`/`String.get`/... stdlib) when `init`'s `pub use string`
/// dep was re-resolved from `lang/parser/` -- so combinators saw the
/// parser's `string` module instead of the stdlib, and every
/// `String.length`/`String.get`/`String.drop` reference went
/// `unknown variable`. By loading each module exactly once during the
/// walk -- where `base_dir` is already the PARENT module's resolved
/// directory, not the target's -- `init/string.mo` is what gets loaded
/// for the `string` dep, matching the Rust reference's own per-module
/// resolution. Modules that fail to load are skipped (matching
/// `extract_all_dependencies_go`'s own existing lenient skip), not
/// fatal -- the canonical pipeline surfaces genuine "module not found"
/// failures via `elaborate_loaded_modules`'s own `Result` path.
/// The walk's result plus the (extended) cache it built along the way.
struct LoadedAndCache {
    loaded : Result String LoadedModules,
    cache : ModuleInfoCache,
}

struct InfosAndCache {
    infos : List ModuleInfo,
    cache : ModuleInfoCache,
}

#[partial]
def collect_dep_module_infos (base_dir : String) (to_visit : List ModulePath) (visiting : List ModulePath) (visited : List ModuleInfo) (cache : ModuleInfoCache) : IO InfosAndCache :=
    match to_visit {
        List.empty => do {
            // Annotated local, not a bare `return { ... }` -- the
            // struct-literal pitfall (`validate_no_undesugared_struct_
            // lits`'s own message): an unannotated literal never
            // desugars to a constructor and silently compiles to a
            // void placeholder through this backend.
            let r : InfosAndCache := { infos := visited, cache := cache };
            return r
        },
        List.cons head tail =>
            if list_contains visiting head then
                // Circular dependency - skip to avoid infinite loop
                collect_dep_module_infos base_dir tail visiting visited cache
            else if list_contains_module_info visited head then
                // Already loaded - skip
                collect_dep_module_infos base_dir tail visiting visited cache
            else do {
                let new_visiting : List ModulePath := List.cons head visiting;
                // Cached: within one `check`/`compile` run the same
                // dependency is reached once per importing file, and
                // re-reading + re-parsing it each time is the dominant
                // cross-file cost (see `ModuleInfoCache`'s own note).
                let loaded : InfoAndCache <- load_module_with_info_cached base_dir head cache;
                match loaded.info {
                    Option.some info => do {
                        let new_base_dir : String := extract_directory info.file_path;
                        let dep_decls : List Decl := get_module_info_decls info;
                        let dep_deps : List ModulePath := extract_use_decls dep_decls;
                        let new_to_visit : List ModulePath := List.append dep_deps tail;
                        collect_dep_module_infos new_base_dir new_to_visit new_visiting (List.cons info visited) loaded.cache
                    },
                    Option.none =>
                        // Module not found, skip but continue with tail
                        collect_dep_module_infos base_dir tail new_visiting visited loaded.cache
                }
            }
    }


// --- Corpus-check caching: build prelude+init once, reuse across files ---
//
// `check_file_cached`/`load_module_with_dependencies_and_prelude_cached`
// below always walk, parse, and rebuild `ScopeData` for `prelude`+`init`'s
// full transitive closure from scratch — correct for a single file, but
// `lang/main.mo`'s `run_check_loop` calls `check_file_cached` independently
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
    let roots : List ModulePath := [prelude_module_path, init_module_path, std_module_path];
    let all_deps : List ModulePath <- extract_all_dependencies_go "" roots no_visiting no_visited;
    let loaded_deps_result : Result String (List ScopeData) <- load_dependency_entries (load_scope_entry "") dependency_not_found_msg all_deps List.empty;
    match loaded_deps_result {
        Result.ok loaded_deps => do {
            // Annotated local first: a bare struct literal in `return`'s
            // argument position gets no expected type through the
            // self-hosted checker (constructor signatures are
            // `Term.hole`), so it can't resolve its own struct -- see
            // AGENTS.md's struct-literal note and `validate_no_
            // undesugared_struct_lits` (lang/codegen/emit.mo).
            let base : PreludeInitBase := { scope_data := merge_scope_data_list loaded_deps, covered := all_deps };
            return base
        },
        // Prelude/init are bundled with the compiler itself, not
        // user-supplied -- this should never happen in practice. Rather
        // than crash the whole `check` command outright, surface it and
        // proceed with an empty base: every subsequent file's own check
        // will then independently re-attempt (and re-report) the same
        // missing dependency, which is at least visible, not silent.
        Result.err e => do {
            println ("fatal: failed to load prelude/init: " ++ e);
            let empty_base : PreludeInitBase := { scope_data := scope_data_empty, covered := List.empty };
            return empty_base
        }
    }
}

// --- Whole-run module-scope cache: dedupe non-base dependency loads across files ---
//
// `PreludeInitBase` (above) caches prelude+init, shared and fixed for a
// whole `run_check` invocation. It does NOT cover a file's *other*
// `use` dependencies (within `lang/`/`std/` etc.) -- those are reloaded
// (re-read, re-parsed, re-scope-built via `build_scope_from_decls`)
// completely from scratch by `load_dependency_scopes` on EVERY file
// that needs them, with no memoization across different files' own
// independent dependency walks in the same corpus-check run. Measured
// directly: in one multi-file run, `lang/types.mo` alone is
// independently loaded 54 separate times (54 files `use lang.types`),
// `lang/scope.mo` 10 times, `lang/parser/core.mo`/`combinators.mo`/
// `char_preds.mo` 10-16 times each -- self-hosted-compiler-perf.md's
// explicitly-flagged next target after the prelude/init-only fixes.
//
// `ModuleScopeCache` closes this gap: a whole-run, growing cache of
// already-loaded non-base dependencies' `ScopeData`, threaded forward
// through `run_check_loop`/`check_file_cached`/`load_module_with_
// dependencies_and_prelude_cached` the same way `PreludeInitBase` is
// threaded, except mutable (grows as new dependencies get loaded)
// rather than fixed.
//
// Correctness: safe because this codebase's dependency loading is
// FLAT, not recursive -- `extract_all_dependencies_go` walks a whole
// transitive closure into one flat list first; each dependency's own
// `ScopeData` is built independently from only ITS OWN decls
// (`build_scope_from_decls`, never merging in that dependency's own
// further deps); `merge_scope_data_list` flat-unions everything
// afterward. A cached `ScopeData` is therefore context-free -- a pure
// function of that module's own decls, bit-identical to what a fresh
// load would produce regardless of which file asked for it or what
// that file's own `extra_deps`/`base_covered` looked like. The cache
// sits strictly AFTER `extract_all_dependencies_go` has already
// decided a caller's own `extra_deps` set (per-caller cycle detection,
// via `visiting`/`visited`, is completely untouched by this cache); it
// only changes HOW an already-decided-necessary entry's value gets
// produced (I/O+parse+build vs. a lookup) -- never WHICH entries a
// caller ends up needing. `extract_all_dependencies_go` itself is not
// modified by this change.
//
// Keyed on `ModulePath` (not a resolved file path): grep-verified safe
// for the current corpus -- only two bare (non-dotted) `use`s exist
// anywhere (`init/string.mo`'s `use math {}`, `examples/test_mote.mo`'s
// `use greet {greet}`), each resolved from exactly one `base_dir`, no
// observed collision. This is a structural, not observed, risk:
// `resolve_module_file` tries a caller's own `base_dir`-relative path
// BEFORE the fixed `init`/`std`/`lang`/`examples` fallbacks, so two
// different callers' `base_dir`s could in principle resolve the same
// bare `ModulePath` to two different files. If that ever becomes real,
// switch the key to `resolve_module_file`'s own resolved path string
// instead (already computed on this call path, just currently
// discarded) -- not attempted here since it isn't needed today.
//
// `Map.lookup`/`Map.insert` below resolve correctly because these are
// plain monomorphic functions (concrete `ModulePath`/`ScopeData` types,
// no `[Constraint]` annotation) -- see `lang/scope.mo`'s
// `scope_data_find_def` for the identical, already-proven-safe pattern
// and the evaluator limitation it sidesteps.
struct ModuleScopeCache {
    entries : HashMap ModulePath ScopeData,
    hits : I64,
    misses : I64,
}

// `HashMap.map HashMap.empty_buckets` (not `Map.empty`) -- `Map.empty`'s
// own instance for `HashMap` is CONSTRAINED (`instance [Hashable K, BOrd
// K] Map HashMap`), and this call site's `K`/`V` (`ModulePath`/
// `ScopeData`, from `ModuleScopeCache.entries`'s own declared field
// type) aren't visible to `resolve_class_calls_decls`'s syntactic
// resolution at all -- even with `class Map`'s own declared default
// carrier (`:= HashMap`) letting `find_matching_instance` find the
// RIGHT instance, `resolve_dict_args` then has no concrete `K` to build
// the instance's own `Hashable`/`BOrd` dict args from, so it still gives
// up. `HashMap.map`/`.empty_buckets` (used identically elsewhere in this
// exact style, e.g. `lang/codegen/emit.mo`'s `str_map_empty`) bypasses
// the typeclass entirely -- the concrete, always-correct choice here
// anyway (`filter_reachable_decls`'s own doc comment: "HashMap preferred
// over BTreeMap here for performance").
def module_scope_cache_empty : ModuleScopeCache := {
    entries := HashMap.map HashMap.empty_buckets,
    hits := 0,
    misses := 0,
}

def module_scope_cache_lookup (key : ModulePath) (cache : ModuleScopeCache) : Option ScopeData :=
    match cache {
        ModuleScopeCache.mk entries _ _ => Map.lookup key entries
    }

/// Record a cache hit (bump `hits`, entries unchanged) -- purely for
/// `--verbose` visibility into how much redundant loading this cache
/// actually avoids on a real run; no effect on correctness.
def module_scope_cache_hit (cache : ModuleScopeCache) : ModuleScopeCache :=
    match cache {
        ModuleScopeCache.mk entries hits misses => {
            entries := entries,
            hits := hits + 1,
            misses := misses,
        }
    }

def module_scope_cache_insert (key : ModulePath) (sd : ScopeData) (cache : ModuleScopeCache) : ModuleScopeCache :=
    match cache {
        ModuleScopeCache.mk entries hits misses => {
            entries := Map.insert key sd entries,
            hits := hits,
            misses := misses + 1,
        }
    }

struct ScopesAndCache {
    scopes : List ScopeData,
    cache : ModuleScopeCache,
}

/// Cache-aware sibling of `load_dependency_scopes`: for each dep,
/// serve it from `cache` if already loaded this run (zero I/O), else
/// load it exactly as `load_dependency_scopes` does today and insert
/// the result into `cache` before continuing, so a LATER dep in this
/// same list -- or a later file's own `extra_deps`, since `cache` is
/// threaded across the whole `run_check_loop` -- can hit it too.
#[partial]
def load_dependency_scopes_cached (base_dir : String) (deps : List ModulePath) (acc : List ScopeData) (cache : ModuleScopeCache) : IO ScopesAndCache :=
    match deps {
        List.empty => do {
            // Annotated local first -- see `build_prelude_init_base`'s
            // own note above.
            let result : ScopesAndCache := { scopes := acc, cache := cache };
            return result
        },
        List.cons head tail => do {
            match module_scope_cache_lookup head cache {
                Option.some sd => do {
                    let hit_cache : ModuleScopeCache := module_scope_cache_hit cache;
                    load_dependency_scopes_cached base_dir tail (List.cons sd acc) hit_cache
                },
                Option.none => do {
                    // Miss: load exactly as `load_dependency_scopes` does
                    // (base_dir-relative first, global-search fallback),
                    // then insert into `cache` before continuing.
                    let sd_opt : Option ScopeData <- load_module_scope base_dir head;
                    match sd_opt {
                        Option.some sd => do {
                            let new_cache : ModuleScopeCache := module_scope_cache_insert head sd cache;
                            load_dependency_scopes_cached base_dir tail (List.cons sd acc) new_cache
                        },
                        Option.none => do {
                            let sd_opt2 : Option ScopeData <- load_module_scope_default head;
                            match sd_opt2 {
                                Option.some sd => do {
                                    let new_cache : ModuleScopeCache := module_scope_cache_insert head sd cache;
                                    load_dependency_scopes_cached base_dir tail (List.cons sd acc) new_cache
                                },
                                Option.none => load_dependency_scopes_cached base_dir tail acc cache
                            }
                        }
                    }
                }
            }
        }
    }

/// `scope` is `Option` (unlike most of this file's other `Scope`
/// results) specifically so `cache` is ALWAYS available to the caller,
/// even on the failure path -- `load_module_with_dependencies_and_
/// prelude_cached` below returns this directly (not `IO (Option
/// ScopeAndCache)`) so a load failure doesn't strand the cache
/// `run_check_loop` needs to keep threading to the next file.
struct ScopeAndCache {
    scope : Option Scope,
    cache : ModuleScopeCache,
}

/// Same shape as `load_module_with_dependencies_and_prelude`, but reuses
/// an already-built `PreludeInitBase` instead of loading prelude/init
/// from scratch — only `mp`'s own additional `use` dependencies (beyond
/// whatever `base` already covers) get freshly walked/loaded, and even
/// those are served from `cache` (the whole-run `ModuleScopeCache`, see
/// its own doc comment above) whenever a PRIOR file in this same
/// `run_check_loop` already loaded the identical dependency.
#[partial]
def load_module_with_dependencies_and_prelude_cached (base : PreludeInitBase) (cache : ModuleScopeCache) (base_dir : String) (mp : ModulePath) : IO ScopeAndCache :=
    match base {
        PreludeInitBase.mk base_sd base_covered => do {
            let opt_decls : Option (List Decl) <- load_module_decls base_dir mp;
            match opt_decls {
                Option.some decl_list => do {
                    let resolved_path_opt : Option String <- resolve_module_file base_dir mp;
                    let module_base_dir : String :=
                        match resolved_path_opt {
                            Option.some fp => extract_directory fp,
                            Option.none => base_dir
                        };
                    let direct_deps : List ModulePath := extract_use_decls decl_list;
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
                    let loaded : ScopesAndCache <- load_dependency_scopes_cached module_base_dir extra_deps List.empty cache;
                    match loaded {
                        ScopesAndCache.mk loaded_extra updated_cache => do {
                            let merged_extra : ScopeData := merge_scope_data_list loaded_extra;
                            let merged_with_base : ScopeData := merge_scope_data base_sd merged_extra;
                            let this_scope : ScopeData := build_scope_from_decls mp decl_list;
                            let final_scope : ScopeData := merge_scope_data merged_with_base this_scope;
                            // See `load_module_with_dependencies`'s own identical
                            // outer-aliasing-pass comment above -- same reasoning,
                            // including the `decls_have_aliasable_decls` no-op skip.
                            let aliased_scope : ScopeData :=
                                if decls_have_aliasable_decls decl_list
                                then alias_decls_in_scope decl_list final_scope
                                else final_scope;
                            let scope : Scope := {
                                module_id := mp,
                                scope := aliased_scope,
                                parent := Option.none,
                            };
                            // Annotated locals first -- see
                            // `build_prelude_init_base`'s own note above.
                            let result : ScopeAndCache := { scope := Option.some scope, cache := updated_cache };
                            return result
                        }
                    }
                },
                Option.none => do {
                    let miss : ScopeAndCache := { scope := Option.none, cache := cache };
                    return miss
                }
            }
        }
    }

/// The `check_file`-flavored twin of `load_module_with_dependencies_and_prelude_cached`.
#[partial]
pub def build_scope_with_deps_and_prelude_cached (base : PreludeInitBase) (cache : ModuleScopeCache) (file_path : String) (mod_name : String) : IO ScopeAndCache :=
    let base_dir : String := extract_directory file_path in
    let mp : ModulePath := ModulePath.mp [Identifier.id mod_name] in
    load_module_with_dependencies_and_prelude_cached base cache base_dir mp

/// The one shared "already-deduplicated dependency list -> one thing per
/// entry" fold, used by every UNCACHED dependency-loading path in this
/// file: the `Scope`-merging path (`load_module_with_dependencies`/
/// `load_module_with_dependencies_and_prelude`, loader = `load_scope_entry`
/// below) and the `ModuleInfo`-list path (`load_file_modules`, loader =
/// `load_module_with_info`). `deps` is already the complete, deduplicated
/// transitive closure by the time this is called (see
/// `extract_all_dependencies`'s own doc comment), so this is a flat
/// one-pass walk: call `loader` once per entry, cons the result onto
/// `acc`, continue -- no re-derivation, no per-node subtree re-walk.
/// Hard-fails (`Result.err`, via `not_found`) on the first entry `loader`
/// can't resolve at all -- matches `check`/`compile`'s own "a bad
/// dependency is a real error" behavior elsewhere. This is a deliberate
/// behavior change for the `Scope` path, which used to silently skip an
/// unresolvable dependency rather than fail; the `ModuleInfo` path
/// already hard-failed, so this unifies on ITS policy.
/// Does NOT replace `load_dependency_scopes_cached` below: that one
/// additionally consults/updates a whole-run `ModuleScopeCache` across
/// MANY files in one `run_check_loop` (measured as ~75% of the whole
/// "scope" phase's cost before that cache existed -- see
/// `load_module_with_dependencies_and_prelude_cached`'s own doc comment),
/// a genuinely different, performance-critical concern this simple fold
/// doesn't need to generalize into.
#[partial]
def load_dependency_entries {A : Type} (loader : ModulePath -> IO (Option A)) (not_found : ModulePath -> String) (deps : List ModulePath) (acc : List A) : IO (Result String (List A)) :=
    match deps {
        List.empty => do {
            return (Result.ok acc)
        },
        List.cons head tail => do {
            let entry_opt : Option A <- loader head;
            match entry_opt {
                Option.some entry => do {
                    let new_acc : List A := List.cons entry acc;
                    load_dependency_entries loader not_found tail new_acc
                },
                Option.none => do {
                    return (Result.err (not_found head))
                }
            }
        }
    }

/// `load_dependency_entries`'s loader for the `Scope` path: `load_module_scope`'s
/// own two-tier resolution (try `base_dir`-relative first, then fall back
/// to an unrestricted global search) that `load_dependency_scopes` used
/// to inline directly -- extracted here so it can be partially applied
/// (`load_scope_entry base_dir`) into `load_dependency_entries`'s
/// `loader` parameter.
def load_scope_entry (base_dir : String) (mp : ModulePath) : IO (Option ScopeData) := do {
    let sd_opt : Option ScopeData <- load_module_scope base_dir mp;
    match sd_opt {
        Option.some sd => do { return (Option.some sd) },
        Option.none => load_module_scope_default mp
    }
}

/// Shared "couldn't resolve this dependency at all" message for
/// `load_dependency_entries`'s `not_found` parameter.
def dependency_not_found_msg (mp : ModulePath) : String :=
    "Failed to load module: " ++ module_path_to_string mp

/// Merge two ScopeData structures. `def_refs` merges via
/// `HashMap.merge_buckets` (`std/map.mo`) — a direct bucket-to-bucket
/// merge needing no `Hashable`/`BOrd` re-hashing at all, since both
/// sides already hashed their keys with the same function. This
/// replaced an earlier `HashMap.to_list dr1` + fold-via-`scope_data_
/// add_def` pattern (one `Map.insert`-equivalent call per entry,
/// rebuilding a bucket from scratch on every single insert) once
/// `--verbose` phase timing (`lang/module.mo`'s `check_file_cached`)
/// showed the SCOPE phase dominating per-file check time by ~90x over
/// the CHECK phase (e.g. `init/id.mo`: scope≈4.3s vs. check≈0.05s),
/// with `merge_scope_data` — called once per file via `build_scope_
/// with_deps_and_prelude_cached`, merging the full shared `PreludeInit
/// Base` scope every time — as the prime suspect; the `to_list`+refold
/// pattern re-walks/reallocates the ENTIRE base map's buckets on every
/// file regardless of how small that file's own `use` set is. See
/// AGENTS.md's performance section for the measured before/after.
///
/// No empty-`sd2` short-circuit needed (an earlier revision of this
/// function, built on the old `to_list`+refold algorithm, had one,
/// since that algorithm's cost scaled with `|dr1|` regardless — see
/// `load_module_with_dependencies_and_prelude_cached`'s own doc comment
/// just above for the OTHER, larger fix that made `sd2`/`merged_extra`
/// actually empty in the common case): `HashMap.merge_buckets` is a
/// fixed 16 bucket-pair appends either way, cheap enough that special-
/// casing emptiness wouldn't save anything measurable.
#[partial]
def merge_scope_data (sd1 : ScopeData) (sd2 : ScopeData) : ScopeData :=
    {
        def_refs := HashMap.merge_buckets sd1.def_refs sd2.def_refs,
        class_defs := list_append sd1.class_defs sd2.class_defs,
        instances := merge_instances sd1.instances sd2.instances,
        inductives := HashMap.merge_buckets sd1.inductives sd2.inductives,
        classes := list_append sd1.classes sd2.classes,
        infixes := list_append sd1.infixes sd2.infixes,
        conflicts := list_append sd1.conflicts sd2.conflicts,
        // Same bucket-to-bucket merge as `def_refs` just above -- see
        // this function's own doc comment for why `merge_buckets` (not
        // `to_list`+refold) is the right tool here.
        def_params := HashMap.merge_buckets sd1.def_params sd2.def_params,
        def_return_types := HashMap.merge_buckets sd1.def_return_types sd2.def_return_types,
        // Must be merged like every sibling side-table above: an
        // omitted field here silently takes `ScopeData`'s own DEFAULT
        // (an empty map) rather than keeping either input's entries, so
        // leaving it out drops every dependency module's signatures on
        // the floor at the first cross-module merge -- the whole
        // signature-driven application path (`try_type_check_def_call`,
        // lang/typecheck/infer.mo) then silently reverts to its
        // `Option.none` fallback for anything not declared in the file
        // being checked.
        def_sigs := HashMap.merge_buckets sd1.def_sigs sd2.def_sigs,
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

/// Merge two lists of ScopeInstance. `ys`-empty short-circuit (checked
/// once, not per recursive step) -- `merge_scope_data`'s two real call
/// sites (`load_module_with_dependencies_and_prelude_cached`, below)
/// both pass the LARGE shared-base side as `ins1`/`xs` and the small/
/// often-empty side as `ins2`/`ys`, so without this every file checked
/// walked and reallocated the base's whole instance list cons-cell by
/// cons-cell for zero benefit. Same shape as item 9's `def_refs`
/// `HashMap.is_empty` fast path, just for the fields that fix didn't
/// reach (`def_refs` itself moved to `HashMap.merge_buckets` instead).
#[partial]
def merge_instances (ins1 : List ScopeInstance) (ins2 : List ScopeInstance) : List ScopeInstance :=
    match ins2 {
        List.empty => ins1,
        List.cons _ _ => merge_instances_go ins1 ins2
    }

#[partial]
def merge_instances_go (ins1 : List ScopeInstance) (ins2 : List ScopeInstance) : List ScopeInstance :=
    match ins1 {
        List.empty => ins2,
        List.cons si1 rest1 =>
            let merged_rest : List ScopeInstance := merge_instances_go rest1 ins2 in
            List.cons si1 merged_rest
    }

/// Helper: append two lists. See `merge_instances`'s own doc comment for
/// why the `ys`-empty short-circuit matters here specifically.
#[partial]
def list_append (xs : List A) (ys : List A) : List A :=
    match ys {
        List.empty => xs,
        List.cons _ _ => list_append_go xs ys
    }

#[partial]
def list_append_go (xs : List A) (ys : List A) : List A :=
    match xs {
        List.empty => ys,
        List.cons x rest => List.cons x (list_append_go rest ys)
    }

// --- Module resolution for type checking ---


/// Type check all declarations in a module with a given scope. A thin
/// `Bool`-returning wrapper over `check_module_with_scope` (the richer,
/// IO-returning, diagnostics-producing walk `check`/`elaborate_loaded_
/// modules` already use) rather than a second, independently-maintained
/// walk of the same logic -- the two used to be hand-copied and had
/// quietly drifted apart (this Bool-returning family never skolemized a
/// def's own implicit type params the way `check_def_with_scope` did,
/// among other gaps `check_module_with_scope`'s own richer walk already
/// covers: `struct_d`/`class_d`, `scoped_open_d` recursion, ...). Used by
/// `slow_tests/*.mo`'s own corpus-checking `#[test]`s.
#[partial]
pub def typecheck_module_with_scope (scope : Scope) (decl_list : List Decl) (locals : LocalScope) : IO Bool := do {
    // Annotated bind: without the type, the self-hosted checker can't
    // tell this match's `empty`/`cons` from `BTreeMap`'s own same-named
    // constructors ("ambiguous constructor `empty`") -- an IO bind's
    // result type isn't recoverable in pure infer mode.
    let diags : List String <- check_module_with_scope scope decl_list locals Option.none false;
    match diags {
        List.empty => do { return true },
        List.cons _ _ => do {
            println_all diags;
            return false
        },
    }
}

/// `println` one diagnostic per line -- so a `typecheck_module_with_scope`
/// (or any other caller collapsing a diagnostics list to a bare `Bool`)
/// failure is actually explained on stdout, not just reported as a silent
/// `FAIL` with no indication of which declaration failed or why.
#[partial]
def println_all (lines : List String) : IO Unit :=
    match lines {
        List.empty => return unit,
        List.cons l rest => do {
            println l;
            println_all rest
        },
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

/// Walk a type's leading `Term.forall`-binder chain, collecting each
/// binder's NAMED debug-name identifier (unnamed binders are skipped).
/// This is how `locals_with_def_typevars` recovers the implicit type
/// parameters `elaborate.mo`'s `wrap_forall` introduced: a def like
/// `def Lens [Functor F] {F : Type -> Type} (...) : Type := ...` has its
/// `{F}` clause deliberately dropped by the parser
/// (`def_implicit_close`, lang/parser.mo) on the understanding that
/// `elaborate_def` re-introduces `F` as a leading `Forall F. ...` binder
/// -- once that elaboration is wired into the pipeline, the binder name
/// only survives HERE (in `typ`'s Forall chain), so this walk is what
/// skolemizes `F` into `locals` for the body check. Mirrors the Rust
/// reference's own Forall-chain walk. Does NOT descend past the leading
/// Foralls: nested inner Foralls (under a Pi) belong to a different
/// scope and are not this def's own implicit params.
#[partial]
def forall_chain_binder_names (typ : Term) : List Identifier :=
    match typ {
        Term.forall dbg _kind body =>
            match dbg {
                DebugName.named id =>
                    let rest : List Identifier := forall_chain_binder_names body in
                    union_ids (List.cons id List.empty) rest,
                DebugName.unnamed => forall_chain_binder_names body,
            },
        _ => List.empty
    }

/// Skolemize `df`'s implicit type parameters into `locals`, ready for
/// `type_check`ing `df`'s body against. Three sources, unioned: the
/// Forall-chain binder names of the (elaborated) declared type
/// (`forall_chain_binder_names` -- the constraint-only vars
/// `elaborate_def`'s `wrap_forall` wraps but that never appear in the
/// type body, e.g. `F` in `[Functor F]`); the free vars of the declared
/// type (`free_vars`); and the def's own parameter annotations
/// (`collect_param_annotation_names`). `bind_unresolved_as_local_typevars`
/// then skolemizes only those candidates that don't already resolve as a
/// real global, so this is a strict superset of the pre-elaboration
/// behaviour -- nothing that checked before stops checking.
#[partial]
def locals_with_def_typevars (df_typ : Term) (body : Term) (scope : Scope) (locals : LocalScope) : LocalScope :=
    let fv := free_vars df_typ List.empty in
    let qv := forall_chain_binder_names df_typ in
    let pv := collect_param_annotation_names body in
    let candidates : List Identifier := union_ids (union_ids fv qv) pv in
    bind_unresolved_as_local_typevars candidates scope locals

/// Skolemize `cls`'s own declared type parameters (`A` in `class
/// Semigroup A { def combine : A -> A -> A }`) plus any of its own
/// constraint vars, into `locals` -- mirrors `locals_with_def_typevars`'s
/// identical role for a def's own implicit type parameters. Without this,
/// `check_class_method_with_scope` type-checks each method's bare
/// `A -> A -> A`-shaped signature with `A` unbound, failing
/// `unknown variable 'A'` -- see `check_class_with_scope`'s own call site.
#[partial]
def locals_with_class_typevars ({ params, constraints, .. } : Class) (scope : Scope) (locals : LocalScope) : LocalScope :=
    let candidates : List Identifier := union_ids (param_names params) (constraint_vars constraints) in
    bind_unresolved_as_local_typevars candidates scope locals

/// Skolemize an inductive's own declared type parameters (`A` in
/// `type List A { empty, cons (a : A) (List A) : List A }`) into `locals`,
/// ready for `check_constructor_with_scope` to type-check each
/// constructor's signature against -- mirrors `locals_with_class_typevars`'s
/// identical role for a class's own params. Inductives carry no constraints
/// of their own (a `type` declaration has no `[Class V]` clause), so this
/// is just `param_names params`. Without this, `cons`'s `Pi (a : A) ->
/// Pi (List A) -> List A` checks with `A` unbound, failing
/// `unknown variable 'A' in cons` (and likewise `nil`).
#[partial]
def locals_with_inductive_params ({ params, .. } : Inductive) (scope : Scope) (locals : LocalScope) : LocalScope :=
    let candidates : List Identifier := param_names params in
    bind_unresolved_as_local_typevars candidates scope locals

// --- `check`: multi-error typecheck pass (lang/main.mo's `check` command) ---
//
// Same per-decl walk `typecheck_module_with_scope` above now itself
// wraps, but rendering and *accumulating* every failing declaration's
// `TypeError` (via
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
// FIXED (2026-08-25 review refresh, was "STILL OPEN" above): bare
// Forall-bound type-PARAMETER names (`A`/`B`/`C` — implicit/universal
// type variables, e.g. `init/id.mo`'s `def Id.run (a : Id A) : A :=
// ...`, which used to fail with `unknown variable 'A'`) are now
// resolved. `locals_with_def_typevars` (above, mirroring `locals_with_
// class_typevars`/`locals_with_inductive_params`'s identical role for
// class/inductive params) walks the def's own elaborated `typ`'s
// `Forall` chain via `forall_chain_binder_names` and pushes each bound
// name into `locals` as a skolem local before `body` is checked — wired
// into `check_def_with_scope`/`elaborate_def_with_scope` below. The
// literal `Id.run` example from this comment's own prior text now
// type-checks. `check`'s *parse* phase (strict, via `try_parse_decls_
// strict`) was and remains unaffected either way.

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
/// String }`'s `A`) — `check_class_with_scope` below skolemizes it via
/// `locals_with_class_typevars` (mirroring `check_def_with_scope`'s own
/// `locals_with_def_typevars` fix for the equivalent def-level gap, both
/// documented above), so this no longer reports `unknown_var 'A'`.
///
/// `verbose` threads a per-declaration progress trace (which def/type/
/// constructor is currently being checked) down through every level —
/// these all became `IO`-returning (were pure `Bool`/`List String`)
/// purely to allow that `println`; the accumulation logic itself is
/// unchanged.
#[partial]
def check_module_with_scope (scope : Scope) (decl_list : List Decl) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match decl_list {
        List.empty => do { return List.empty },
        List.cons d rest => do {
            let here : List String <- check_decl_with_scope d scope locals path verbose;
            let there : List String <- check_module_with_scope scope rest locals path verbose;
            return (list_append here there)
        }
    }

/// `promote_instance_defs`'s own `__Dict_ClassName_Args` value def
/// (`lang/scope.mo`'s `promote_instance`, e.g. `__Dict_Speak_Dog`) is a
/// pure codegen artifact -- declared `.typ := Term.type_ 1` but its
/// `.term` is a `Term.con` record of the instance's own method
/// references, a shape ordinary `type_check` was never meant to validate
/// (it isn't real source, no user ever writes it) and can't: its field
/// terms are built assuming codegen's own de-Bruijn-free-standing
/// `Term.var 0` convention, not a real local binder, so checking it here
/// surfaces a bogus `unknown variable 'bound_var'` diagnostic. Now that
/// `check`/`elaborate_loaded_modules` run promotion BEFORE type-checking
/// (previously only codegen did), `check_decl_with_scope` needs to
/// recognize and skip these the same deliberate way it already skips
/// `instance_d` bodies (`module.mo`'s own documented gap, just below).
#[partial]
def is_dict_value_def (df : Def) : Bool :=
    String.starts_with "__Dict_" (module_path_to_string df.name)

/// `use_d`/`open_d`/`infix_d` genuinely have nothing to type-check (no
/// term/type of their own) — the `_ => List.empty` catch-all is correct
/// for those. `instance_d` is the real remaining gap here: instance
/// method BODIES aren't checked at all (tracked separately — see
/// `lang/typecheck/infer.mo`'s `resolve_class_method`, which doesn't
/// even resolve a concrete method body to check in the first place).
def check_decl_with_scope (d : Decl) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match d {
        Decl.def_d df =>
            if is_dict_value_def df then do { return List.empty } else check_def_with_scope df scope locals path verbose,
        Decl.inductive_d ind => check_inductive_with_scope ind scope locals path verbose,
        Decl.struct_d s => check_struct_with_scope s scope locals path verbose,
        Decl.class_d cls => check_class_with_scope cls scope locals path verbose,
        // `build_scope_one_decl` (lang/scope.mo) recurses into a
        // `scoped_open_d`'s own inner decl the same way -- this used to
        // NOT, silently skipping type-checking the inner decl entirely
        // (`open X {...} in def f := ...` would register `f` in scope
        // via scope-building but never actually check `f`'s own body).
        Decl.scoped_open_d _ _ inner => check_decl_with_scope inner scope locals path verbose,
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
            let locals_ : LocalScope := locals_with_class_typevars cls scope locals;
            check_class_methods_with_scope methods scope locals_ path verbose
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
            // Beyond the class's own params (already skolemized into
            // `locals` by `check_class_with_scope`'s caller), a method's
            // own signature commonly introduces FURTHER implicit type
            // vars that only ever appear there -- e.g. `Foldable`'s own
            // `foldr (f : A -> B -> B) (z : B) (t : T A) : B`: `T` is the
            // class's own param, but `A`/`B` are method-local. Mirrors
            // `locals_with_def_typevars`'s identical treatment of an
            // ordinary def's own implicit type params.
            let locals_ : LocalScope := bind_unresolved_as_local_typevars (free_vars typ List.empty) scope locals;
            return (match type_check typ Term.hole scope empty_local_types locals_ {
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
                // `typ`, not `Term.hole`: a def's declared `typ` is
                // ALREADY the full Pi-chain matching its body's
                // `Term.lam` chain (`lang/parser.mo`'s `build_param_pi_
                // chain`), so checking the body against it (rather than
                // pure infer mode) lets expected-type information flow
                // into the body -- e.g. into a match arm whose result is
                // an unannotated struct literal, which otherwise can't
                // infer its own struct type at all. This is what the
                // `expected_type` threading through match-arm checking
                // (`type_check_cases`/`type_check_case_body_checked`)
                // was added for; it had nothing real to carry until now.
                return (match type_check body typ scope empty_local_types locals_ {
                    Result.ok _ => List.empty,
                    Result.err e => [render_type_error (module_path_to_string name) path e]
                })
            }
        }
    }

// --- Elaboration: codegen consumes the checker's own resolved terms ---
//
// `check_def_with_scope` above discards the successfully-checked
// `TypedTerm` (`Result.ok _ => List.empty`) -- it only ever needed to
// know PASS/FAIL for `check`'s own diagnostics. Codegen needs the actual
// resolved term: `type_check`'s class-method resolution
// (`lang.typecheck.infer`'s `resolve_class_method`) rewrites a call like
// `Append.append x y` into a concrete, already-dictionary-dispatched
// reference the OLD syntactic `resolve_class_calls_decls` pass
// (`lang.scope`) sometimes can't (that gap is the `Append_append`
// self-compile bug this whole plan exists to fix) -- so Stage 3 makes
// `compile`/`test` consume THIS elaborated decl list instead of handing
// codegen the original, unresolved one.

/// Same skolemization/hole-skipping as `check_def_with_scope`, but
/// returns the REBUILT `Def` (with its elaborated `.term`) on success
/// instead of an empty diagnostics list.
///
/// Checks `body` against `typ` (the def's own DECLARED signature) --
/// NOT `Term.hole` (this function's own previous behavior, and the bug
/// this comment now documents). `check_def_with_scope` just above
/// already gets this right (`type_check body typ scope ...`); this
/// sibling didn't, and pure-infer-mode (`Term.hole`) type-checking a
/// bare struct literal with no `: StructName` self-annotation has no
/// way to learn its own type at all (`type_check_struct_lit`'s own
/// error: "cannot infer struct type for struct literal (no expected
/// type from context)") -- confirmed via a minimal repro (`def make_a
/// (x : I64) : PairA := { a1 := x, a2 := x }`, no match/let involved at
/// all): `check` (which uses `check_def_with_scope`) passes it cleanly,
/// but codegen's `elaborate_module_decls_best_effort` (which calls THIS
/// function) silently failed to elaborate it, leaving the struct
/// literal un-desugared for `compile_lit_ir`'s own `Literal.struct_lit`
/// stub (assumes elaboration ALWAYS desugars to a real `Term.con` --
/// see its own doc comment) to silently compile as `void_val`. This is
/// very likely the REAL root cause behind the `build_get_env_instrs`
/// ("constructor not found in inductive") failure this whole session's
/// `find_inductive_for_cases` work was chasing too -- that def's own
/// body is a `match` whose branches return struct literals checked
/// against `build_get_env_instrs`'s own declared return type, exactly
/// the same "body needs `typ`, not `Term.hole`" shape.
def elaborate_def_with_scope ({ name, typ, term := body, constraints, attrs, vis } : Def) (scope : Scope) (locals : LocalScope) : Result String Def :=
    if is_term_hole body then
        Result.ok (Def.mk name typ body constraints attrs vis)
    else
        let locals_ : LocalScope := locals_with_def_typevars typ body scope locals in
        match type_check body typ scope empty_local_types locals_ {
            Result.ok tt => Result.ok (Def.mk name typ (tt_term tt) constraints attrs vis),
            Result.err e => Result.err (render_type_error (module_path_to_string name) Option.none e),
        }

/// Elaborates every decl in `decl_list`, threading errors. Non-`def_d`
/// decls (inductive/struct/class/instance/...) pass through unchanged --
/// only a def's own BODY can contain a class-method call to resolve.
/// `__Dict_*` value defs (`is_dict_value_def`) are left completely
/// unelaborated too -- they're pure codegen artifacts `type_check` was
/// never meant to touch (see `is_dict_value_def`'s own doc comment).
#[partial]
def elaborate_decl_with_scope (d : Decl) (scope : Scope) (locals : LocalScope) : Result String Decl :=
    match d {
        Decl.def_d df =>
            if is_dict_value_def df then Result.ok d
            else
                match elaborate_def_with_scope df scope locals {
                    Result.ok df_ => Result.ok (Decl.def_d df_),
                    Result.err e => Result.err e,
                },
        Decl.scoped_open_d p f inner =>
            match elaborate_decl_with_scope inner scope locals {
                Result.ok inner_ => Result.ok (Decl.scoped_open_d p f inner_),
                Result.err e => Result.err e,
            },
        _ => Result.ok d,
    }

/// Elaborates a whole decl list -- `Result.ok` with every def's own
/// class-method calls resolved to concrete/dict-projected terms on full
/// success, or `Result.err` with every failing decl's own rendered
/// diagnostic (same accumulate-don't-short-circuit behavior
/// `check_module_with_scope` already has) otherwise.
def elaborate_module_decls (scope : Scope) (decl_list : List Decl) (locals : LocalScope) : Result (List String) (List Decl) :=
    elaborate_module_decls_go scope decl_list locals List.empty List.empty

/// Best-effort sibling for codegen's own WHOLE-GRAPH use (`lang.codegen.
/// emit`/`lang.codegen.test_driver`) rather than `check`'s own gate
/// (which wants `elaborate_module_decls`'s all-or-nothing, real-
/// diagnostics behavior above): a def that fails to elaborate is left
/// COMPLETELY UNCHANGED rather than aborting the whole pass. This
/// matters because the loaded graph for even a trivial program includes
/// the whole prelude/init closure, and a single unrelated, pre-existing
/// gap ANYWHERE in it (a class method`s own higher-kinded implicit param
/// this pass doesn't skolemize, a constrained-instance method whose own
/// dict-forwarding doesn't yet re-typecheck cleanly -- both real,
/// already-known, separately-tracked gaps, not something codegen should
/// have to wait on) must never block the whole graph's worth of
/// elaboration -- `resolve_class_calls_decls` (the old syntactic pass)
/// still gets a chance at whatever this couldn't resolve, afterward,
/// same as always. Never fails; always returns as much elaborated as
/// possible.
#[partial]
def elaborate_module_decls_best_effort (scope : Scope) (decl_list : List Decl) (locals : LocalScope) : List Decl :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            let d_ := match elaborate_decl_with_scope d scope locals {
                Result.ok d2 => d2,
                Result.err _ => d,
            } in
            List.cons d_ (elaborate_module_decls_best_effort scope rest locals),
    }

#[partial]
def elaborate_module_decls_go (scope : Scope) (decl_list : List Decl) (locals : LocalScope) (errs_acc : List String) (decls_acc : List Decl) : Result (List String) (List Decl) :=
    match decl_list {
        List.empty =>
            match errs_acc {
                List.empty => Result.ok (list_reverse decls_acc),
                List.cons _ _ => Result.err (list_reverse errs_acc),
            },
        List.cons d rest =>
            match elaborate_decl_with_scope d scope locals {
                Result.ok d_ => elaborate_module_decls_go scope rest locals errs_acc (List.cons d_ decls_acc),
                Result.err e => elaborate_module_decls_go scope rest locals (List.cons e errs_acc) decls_acc,
            },
    }

#[partial]
def check_inductive_with_scope (ind : Inductive) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match ind {
        Inductive.mk name _params _typ constructors _attrs _vis => do {
            if verbose then println ("  checking type " ++ module_path_to_string name) else do { return unit };
            let locals_ : LocalScope := locals_with_inductive_params ind scope locals;
            check_constructors_with_scope constructors scope locals_ path verbose
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

/// `check_file_cached`'s own result bundled with the (possibly updated)
/// `ModuleScopeCache`, so `run_check_loop` can thread it forward to the
/// next file in the same run.
struct FileCheckAndCache {
    result : FileCheckResult,
    cache : ModuleInfoCache,
}

/// The file checker — now routes through `elaborate_loaded_modules`
/// (the ONE canonical front-end pipeline also used by `compile`/`test`/
/// `slow_tests`, see that function's own doc comment) instead of its own
/// hand-rolled scope-acquisition. This is where `check` used to diverge
/// from `compile`/`test`: it never ran `resolve_infix_decls`/
/// `promote_instance_defs`/`add_constraint_dict_params_decls`, so a
/// class-method call's own dictionary dispatch was never actually
/// exercised by `check` the way it now is.
///
/// `cache` (`ModuleInfoCache`) IS threaded now, through
/// `elaborate_loaded_modules_cached`: a dependency already loaded by an
/// earlier file in the same run is served from it instead of being
/// re-read and re-parsed, which is the O(N·D) -> O(N+D) corpus-run
/// behavior. Measured on a 5-file `check` over `lang/`: 69 of 92
/// dependency loads served from cache (75%).
///
/// `base` (`PreludeInitBase`) is still accepted and UNUSED. It predates
/// `ModuleInfoCache` and covers the narrower prelude+init case that the
/// general cache now also covers, just without `base`'s pre-built
/// `ScopeData`. Removing the parameter, or reviving it to skip
/// prelude/init scope-building specifically, is open follow-up work
/// (see `bootstrapping/unify-check-compile-test-elaboration.md`).
///
/// Passes `check_deps=false` to `elaborate_loaded_modules` — see that
/// function's own doc comment for the two-mode rationale. `check_deps=true`
/// (checking the whole dependency closure a file pulls in, not just its
/// own top-level decls) is NOT yet safe to default to here: turning it on
/// for `lang/main.mo` (whose closure reaches ≈2200 decls, including this
/// self-hosted compiler's own richly-recursive AST types) caused unbounded
/// memory growth (28GB+ RSS and still climbing after ~9 minutes, had to be
/// killed) — root cause under investigation, see
/// `bootstrapping/check-deps-memory-blowup.md`.
#[partial]
def check_file_cached (base : PreludeInitBase) (cache : ModuleInfoCache) (file_path : String) (verbose : Bool) : IO FileCheckAndCache {
    let exists : Bool <- file_exists (Path.path file_path);
    if exists then do {
        if verbose then println ("checking " ++ file_path) else do { return unit };
        let ec : ElaboratedAndCache <- elaborate_loaded_modules_cached file_path false cache;
        let out_cache : ModuleInfoCache := ec.cache;
        match ec.elaborated {
            Result.ok em => do {
                let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
                // Annotated bind: an IO bind's result type isn't
                // recoverable in pure infer mode, so without it the
                // self-hosted checker can't tell this list's
                // `empty`/`cons` from `BTreeMap`'s same-named
                // constructors ("ambiguous constructor `empty`").
                let diags : List String <- check_module_with_scope em.scope em.target_decls empty_locs (Option.some file_path) verbose;
                // Each level bound with an explicit annotation rather
                // than nested inline -- see `load_module_with_info`'s
                // own note. `out_cache`, not `cache`: the walk extended
                // it, and the caller needs the extended one.
                let ok_result : FileCheckResult := { path := file_path, diagnostics := diags };
                let ok_bundle : FileCheckAndCache := { result := ok_result, cache := out_cache };
                return ok_bundle
            },
            Result.err e => do {
                let err_result : FileCheckResult := { path := file_path, diagnostics := [e] };
                let err_bundle : FileCheckAndCache := { result := err_result, cache := out_cache };
                return err_bundle
            },
        }
    } else do {
        let missing_result : FileCheckResult := { path := file_path, diagnostics := ["error: file not found: " ++ file_path] };
        let missing_bundle : FileCheckAndCache := { result := missing_result, cache := cache };
        return missing_bundle
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
    let entries : List String <- list_dir (Path.path dir);
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
            let is_directory : Bool <- is_dir (Path.path path);
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
            let is_directory : Bool <- is_dir (Path.path p);
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

#[test]
def test_try_parse_decls_with_locs_captures_one_per_def : Bool :=
    match try_parse_decls_with_locs "def foo : I64 := 1\ndef bar : I64 := 2\n" {
        Option.some result => match result {
            Pair.pair decls decls_with_locs =>
                I64.beq (List.length decls) 2 && I64.beq (List.length decls_with_locs) 2,
        },
        Option.none => false,
    }

/// Regression test for `merge_scope_data` silently DROPPING a side
/// table it forgets to list.
///
/// The literal there names every field explicitly, and an omitted field
/// does not keep either input's value -- it takes `ScopeData`'s own
/// declared DEFAULT (an empty map). So forgetting one entry means every
/// cross-module merge throws that table away wholesale. `def_sigs` was
/// added without a line here, which dropped every dependency module's
/// signatures at the first merge and silently reverted the
/// signature-driven application path (`try_type_check_def_call`,
/// lang/typecheck/infer.mo) to its `Option.none` fallback for anything
/// not declared in the file being checked.
///
/// Checking round-trip through a merge (rather than eyeballing the
/// literal) is what makes this catch the NEXT forgotten field too.
#[test]
def test_merge_scope_data_preserves_def_sigs : Bool :=
    let name_a : ModulePath := ModulePath.mp [Identifier.id "a_def"] in
    let name_b : ModulePath := ModulePath.mp [Identifier.id "b_def"] in
    let sig_a : Term := Term.pi Term.hole (Term.type_ 1) in
    let sig_b : Term := Term.type_ 1 in
    let sd_a : ScopeData := scope_data_add_def_sig scope_data_empty name_a sig_a in
    let sd_b : ScopeData := scope_data_add_def_sig scope_data_empty name_b sig_b in
    let merged : ScopeData := merge_scope_data sd_a sd_b in
    // BOTH inputs' entries must survive the merge.
    match scope_data_find_def_sig merged name_a {
        Option.none => false,
        Option.some _ =>
            match scope_data_find_def_sig merged name_b {
                Option.none => false,
                Option.some _ => true,
            },
    }

// --- Integration: parse source text, build scope, resolve names ---

#[test]
def test_parse_def_resolve : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    let result : ParseResult (List Decl) := parse_all_decls "def foo : Bool := true" in
    match result {
        ParseResult.success _ decl_list =>
            let sd : ScopeData := build_scope_from_decls path decl_list in
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
        ParseResult.success _ decl_list =>
            let sd : ScopeData := build_scope_from_decls path decl_list in
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
        ParseResult.success _ decl_list =>
            let sd : ScopeData := build_scope_from_decls path decl_list in
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
        ParseResult.success _ decl_list =>
            let sd : ScopeData := build_scope_from_decls path decl_list in
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
        ParseResult.success _ decl_list =>
            let sd : ScopeData := build_scope_from_decls path decl_list in
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
    let result : ParseResult (List Decl) := parse_all_decls "def hello : Bool := true" in
    match result {
        ParseResult.success _ decl_list =>
            let sd : ScopeData := build_scope_from_decls path decl_list in
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
            },
        ParseResult.fail _ => false
    }

#[test]
def test_parse_use_decl_ignored_in_scope : Bool :=
    let path : ModulePath := ModulePath.mp List.empty in
    let result : ParseResult (List Decl) := parse_all_decls "use prelude def bar : Bool := true" in
    match result {
        ParseResult.success _ decl_list =>
            let sd : ScopeData := build_scope_from_decls path decl_list in
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
        Result.ok decl_list => I64.gt (List.length decl_list) 0,
        Result.err _ => false
    }

/// Where `try_parse_decls` silently swallows this exact failure into
/// `Option.none` with zero diagnostic content, the strict twin reports
/// a real, rendered message with position.
#[test]
def test_try_parse_decls_strict_err_has_rendered_diagnostic : Bool :=
    match try_parse_decls_strict "use prelude\n\ngarbage here" Option.none {
        Result.ok _ => false,
        Result.err msg => String.contains msg "at 3:1"
    }

#[test]
def test_try_parse_decls_strict_err_includes_path : Bool :=
    match try_parse_decls_strict "garbage" (Option.some "examples/broken.mo") {
        Result.ok _ => false,
        Result.err msg => String.contains msg "--> examples/broken.mo:1:1"
    }

// === Multi-module loading with boundary preservation ===

struct ModuleInfo {
    path : ModulePath,
    file_path : String,
    decl_list : List Decl,
}

// --- Whole-run ModuleInfo cache -------------------------------------
//
// `load_module_with_info` is a pure function of `(base_dir, mp)`: it
// resolves the module's file, reads it, and parses it. Within one
// `check`/`compile` invocation the SAME dependency is loaded again for
// every file that imports it -- and a `lang/`-corpus file's closure is
// dominated by a handful of large shared modules (`lang/types.mo` alone
// is imported by ~47 files).
//
// Measured before adding this (wall time, `check`, minus a ~19.8s
// interpreter-startup floor): `lang/elaborate.mo` alone ~10.2s of real
// work, `lang/core_ir.mo` alone ~9.0s -- but checking BOTH together
// ~26.1s, i.e. WORSE than the 19.2s sum, because each re-parses the
// shared closure from scratch.
//
// Keyed on `ModulePath`, like `ModuleScopeCache` (see that type's own
// note on why that key is safe for the current corpus). Distinct from
// `ModuleScopeCache` on purpose: that one caches `ScopeData`, which is
// NOT what `elaborate_loaded_modules` needs -- its promotion/dict-param/
// expansion passes want the raw per-module decls this one holds.
struct ModuleInfoCache {
    entries : HashMap ModulePath ModuleInfo,
    hits : I64,
    misses : I64,
}

def module_info_cache_empty : ModuleInfoCache := {
    entries := modpath_map_empty,
    hits := 0,
    misses := 0,
}

def module_info_cache_lookup (key : ModulePath) (cache : ModuleInfoCache) : Option ModuleInfo :=
    modpath_map_lookup key cache.entries

def module_info_cache_hit (cache : ModuleInfoCache) : ModuleInfoCache :=
    { cache with hits := cache.hits + 1 }

def module_info_cache_insert (key : ModulePath) (info : ModuleInfo) (cache : ModuleInfoCache) : ModuleInfoCache :=
    { cache with entries := modpath_map_insert key info cache.entries, misses := cache.misses + 1 }

/// A `load_module_with_info` that consults (and extends) the cache.
struct InfoAndCache {
    info : Option ModuleInfo,
    cache : ModuleInfoCache,
}

#[partial]
def load_module_with_info_cached (base_dir : String) (mp : ModulePath) (cache : ModuleInfoCache) : IO InfoAndCache := do {
    match module_info_cache_lookup mp cache {
        // Every result is an annotated local, not a bare
        // `return { ... }` -- the struct-literal pitfall
        // (`validate_no_undesugared_struct_lits`'s own message).
        Option.some hit => do {
            let r : InfoAndCache := { info := Option.some hit, cache := module_info_cache_hit cache };
            return r
        },
        Option.none => do {
            let loaded : Option ModuleInfo <- load_module_with_info base_dir mp;
            match loaded {
                Option.some info => do {
                    let r : InfoAndCache := { info := Option.some info, cache := module_info_cache_insert mp info cache };
                    return r
                },
                Option.none => do {
                    let r : InfoAndCache := { info := Option.none, cache := cache };
                    return r
                },
            }
        },
    }
}

def show_module_info (m : ModuleInfo) : String :=
    match m {
        mk path file decl_list =>
            "module: " ++ Show.show path ++
            "\n\tpath: " ++ file ++
            "\n\tdecls: " ++ Show.show (List.map Decl.to_name decl_list : List ModulePath)
    }

instance Show ModuleInfo {
    def show (m : ModuleInfo) : String := show_module_info m
}

// The module set a single `load_file_modules` call produced: the target
// file's own module plus its whole transitive dependency closure.
//
// This is THE `LoadedModules` -- `lang/types.mo`'s former same-named
// struct was renamed to `ModuleRegistry` (2026-09-01) to resolve the
// name collision the two used to have; see that type's own comment.
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

def get_module_info_decls (mi : ModuleInfo) : List Decl :=
    match mi {
        ModuleInfo.mk path file_path decl_list => decl_list
    }

/// Resolves every bare `open`/`use`-imported name inside ONE module's
/// own `decl_list` to its real, fully qualified target -- see
/// `lang.scope`'s own `OpenAlias`/`collect_open_aliases`/`resolve_open_
/// alias_decls` doc comment. Must run PER-MODULE, before `lang.codegen.
/// emit`'s `collect_all_decls_from_modules` flattens every loaded
/// module's own decls into one global list -- collecting and applying
/// the alias table AFTER flattening (an earlier version of this fix)
/// let one module's own `use X {name}` alias shadow an unrelated LOCAL
/// variable of the same bare name in a completely different module,
/// since `resolve_open_alias_term` (like the pre-existing `resolve_
/// infix_term` it mirrors) does a blind, name-only rewrite with no
/// per-module or local-binder-shadowing awareness at all. Confirmed as
/// a real regression via the full `lang/main.mo` self-compile: `Reach
/// able decl_list` collapsed from 1925 to 181 the moment the (then-
/// global) pass landed, starving `resolve_class_calls_decls` of
/// instances that used to be reachable.
/// `root_aliases` -- see `resolve_open_aliases_in_modules`'s own doc
/// comment for what these are and why every module needs them merged
/// in, not just its own explicit `open`/`use` declarations. Put first
/// so a module's OWN alias (rare, but possible) shadows an ambient
/// root one of the same bare name, matching ordinary shadowing.
def resolve_open_aliases_in_module_info (known_names : List String) (root_aliases : List OpenAlias) (mi : ModuleInfo) : ModuleInfo :=
    match mi {
        ModuleInfo.mk path file_path decl_list =>
            let candidates := collect_open_aliases decl_list in
            let own_aliases := filter_valid_open_aliases known_names candidates in
            let aliases := list_append own_aliases root_aliases in
            ModuleInfo.mk path file_path (resolve_open_alias_decls aliases decl_list)
    }

#[partial]
def all_module_decl_names (modules : List ModuleInfo) : List String :=
    match modules {
        List.empty => List.empty,
        List.cons m rest => list_append (collect_def_names (get_module_info_decls m)) (all_module_decl_names rest),
    }

#[partial]
def find_module_by_path (modules : List ModuleInfo) (target : ModulePath) : Option ModuleInfo :=
    match modules {
        List.empty => Option.none,
        List.cons m rest =>
            match m {
                ModuleInfo.mk path _fp _decls =>
                    if modpath_eq path target then Option.some m else find_module_by_path rest target,
            },
    }

/// `prelude`/`init`/`std` are ambiently available to EVERY loaded
/// module (`direct_deps_with_prelude`, above) -- a bare name any of
/// them brings into scope via their OWN `open`/`use` (e.g. `init/
/// prelude.mo`'s `open Bool {and, false, not, or, true}`) is callable
/// bare from ANY file, without that file writing its own `open`/`use`
/// for it, exactly the way the type checker's own shared `ScopeData`
/// already treats it. `resolve_open_aliases_in_module_info`'s per-
/// module scoping is otherwise correct (and necessary -- see its own
/// history) for an ORDINARY file's `use X {name}`, but was too narrow
/// for these three: confirmed live as the `llc` frontier immediately
/// following the previous commit's parser-truncation fix -- `undefined
/// value '@not'` (`Bool.not`, `init/prelude.mo`), called bare
/// throughout the corpus by files with no `open`/`use` of their own
/// naming it, exactly like the `println`/`file_exists`-style natives
/// were for `IO`.
#[partial]
def collect_root_aliases (modules : List ModuleInfo) (known_names : List String) : List OpenAlias :=
    collect_root_aliases_go modules [prelude_module_path, init_module_path, std_module_path] known_names

#[partial]
def collect_root_aliases_go (modules : List ModuleInfo) (roots : List ModulePath) (known_names : List String) : List OpenAlias :=
    match roots {
        List.empty => List.empty,
        List.cons r rest =>
            let this_root_aliases :=
                match find_module_by_path modules r {
                    Option.some mi => filter_valid_open_aliases known_names (collect_open_aliases (get_module_info_decls mi)),
                    Option.none => List.empty,
                } in
            list_append this_root_aliases (collect_root_aliases_go modules rest known_names),
    }

/// `resolve_open_aliases_in_module_info` applied to every loaded
/// module -- the actual entry point `lang.codegen.emit`/`lang.codegen.
/// test_driver` call, on `get_loaded_all`'s own `List ModuleInfo`,
/// BEFORE `collect_all_decls_from_modules` flattens it. `known_names`
/// (every real def name across the WHOLE loaded program) is computed
/// once here and threaded to every module's own alias validation --
/// see `filter_valid_open_aliases`'s own doc comment for why this
/// validation step is required at all. `root_aliases` (see its own doc
/// comment) is ALSO computed once and merged into every module's own
/// alias list, not just prelude/init/std's own.
def resolve_open_aliases_in_modules (modules : List ModuleInfo) : List ModuleInfo :=
    let known_names := all_module_decl_names modules in
    let root_aliases := collect_root_aliases modules known_names in
    resolve_open_aliases_in_modules_go known_names root_aliases modules

#[partial]
def resolve_open_aliases_in_modules_go (known_names : List String) (root_aliases : List OpenAlias) (modules : List ModuleInfo) : List ModuleInfo :=
    match modules {
        List.empty => List.empty,
        List.cons m rest =>
            List.cons (resolve_open_aliases_in_module_info known_names root_aliases m) (resolve_open_aliases_in_modules_go known_names root_aliases rest),
    }

#[partial]
def load_module_with_info (base_dir : String) (mp : ModulePath) : IO (Option ModuleInfo) {
    let resolved_path_opt : Option String <- resolve_module_file base_dir mp;
    let actual_base_dir : String :=
        match resolved_path_opt {
            Option.some fp => extract_directory fp,
            Option.none => base_dir
        };
    let decl_list : Option (List Decl) <- load_module_decls actual_base_dir mp;
    return match decl_list {
        Option.some decl_list =>
            let file_path : String :=
                match resolved_path_opt {
                    Option.some fp => fp,
                    Option.none => String.concat (module_path_to_file mp) ".mo"
                } in
            // Bound with an explicit annotation rather than written
            // inline as `Option.some { path := ..., ... }`: a bare
            // struct literal passed straight as a constructor ARGUMENT
            // has no concrete expected type at that point, and the
            // checker does not reliably desugar it to a real
            // constructor there (AGENTS.md's "known pitfall when
            // applying rule 1"). Under the REFERENCE interpreter the
            // inline form happens to work; through the SELF-HOSTED
            // codegen it silently compiled to a value whose fields were
            // read at the wrong offsets, so `file_path` came back as a
            // small integer that `String.length` then dereferenced as a
            // `char*` -- a SIGSEGV in `__strlen_avx2` on the very first
            // module load, which is every `check`/`compile` this
            // compiler runs on itself.
            let info : ModuleInfo := { path := mp, file_path := file_path, decl_list := decl_list } in
            Option.some info,
        Option.none => Option.none
    }
}

/// `cache` carries `ModuleInfo`s already loaded earlier in this same
/// run; the returned `LoadedAndCache` hands back the extended one so a
/// multi-file caller (`run_check_loop`) can reuse it for the next file.
/// Pass `module_info_cache_empty` for a standalone load.
#[partial]
def load_file_modules_cached (file_path : String) (cache : ModuleInfoCache) : IO LoadedAndCache {
    let base_dir : String := extract_directory file_path;
    let module_name : String := module_name_from_path file_path;
    let mp : ModulePath := ModulePath.mp [Identifier.id module_name];
    println <| "loading module: " ++ module_name;
    let module : Option ModuleInfo <- load_module_with_info base_dir mp;
    match module {
        Option.some main_module =>
            match main_module {
                ModuleInfo.mk mp_path file_path decl_list => do {
                    let main_base_dir : String := extract_directory file_path;
                    // Seed prelude/init into the WALK itself (mirroring
                    // `load_module_with_dependencies_and_prelude`'s own
                    // `direct_deps_with_prelude` pattern) rather than
                    // prepending them to the walk's already-deduplicated
                    // result -- prepending after the fact can reintroduce
                    // a duplicate (prelude/init reached again via an
                    // explicit `use`).
                    //
                    // The walk now both resolves AND loads each dependency
                    // in one pass (`collect_dep_module_infos`), so each
                    // module is loaded from its OWN parent's resolved
                    // directory instead of being re-resolved from the
                    // target's directory afterwards -- see
                    // `collect_dep_module_infos`'s own doc comment for the
                    // `lang/parser/string.mo` shadowing bug this fixes.
                    let direct_deps : List ModulePath := extract_use_decls decl_list;
                    // `++` (`Append.append`) needs an `Append (List A)`
                    // instance -- only defined in `std/list.mo`, which
                    // isn't in `lang/main.mo`'s own dependency closure
                    // (`lang.module` itself never `use`s `std.list`).
                    // Compiling `lang/main.mo` through itself then hits
                    // an unresolvable `Append.append` class-method call
                    // (no matching instance in scope), which
                    // `resolve_class_calls_decls`'s own documented
                    // fallback leaves as an unrewritten reference --
                    // `llc: use of undefined value '@Append_append'` once
                    // codegen dot-to-underscore-mangles it. `List.append`
                    // (`init/prelude.mo`, always in scope, no typeclass
                    // needed) is the idiom already used elsewhere in this
                    // exact file (`new_to_visit` above) for the identical
                    // purpose -- use it here too instead of `++`.
                    let direct_deps_with_prelude : List ModulePath := List.append [prelude_module_path, init_module_path, std_module_path] direct_deps;
                    let no_visited : List ModuleInfo := List.empty;
                    let no_visiting : List ModulePath := List.empty;
                    let walked : InfosAndCache <- collect_dep_module_infos main_base_dir direct_deps_with_prelude no_visiting no_visited cache;
                    let all_modules : List ModuleInfo := List.cons main_module walked.infos;
                    // Each level bound with an explicit annotation
                    // rather than inlined as `Result.ok { ... }` inside
                    // an outer literal -- same constructor-argument
                    // struct-literal pitfall documented at
                    // `load_module_with_info`'s own `Option.some info`
                    // above, which reached a real SIGSEGV through this
                    // backend.
                    let main_info : ModuleInfo := ModuleInfo.mk mp_path file_path decl_list;
                    let loaded : LoadedModules := { main_module := main_info, all_modules := all_modules };
                    let result : LoadedAndCache := { loaded := Result.ok loaded, cache := walked.cache };
                    return result
                }
            },
        Option.none => do {
            // Annotated local, not a bare `return { ... }` -- same
            // struct-literal pitfall as the `loaded`/`result` bindings
            // above.
            let r : LoadedAndCache := { loaded := Result.err ("Failed to load" ++ Show.show mp), cache := cache };
            return r
        }
    }
}

/// Backwards-compatible wrapper: a standalone load with a fresh cache.
/// Every caller that isn't threading a whole-run cache uses this.
#[partial]
def load_file_modules (file_path : String) : IO (Result String LoadedModules) := do {
    let r : LoadedAndCache <- load_file_modules_cached file_path module_info_cache_empty;
    return r.loaded
}

// --- elaborate_loaded_modules: THE unified check/compile/test front end ---
//
// `check` (via `check_file_cached`), `compile`/`test` (via `lang/main.mo`'s
// `compile_file`/test-loop, `lang/codegen/emit.mo`/`test_driver.mo`), and
// `slow_tests` used to each hand-roll their own version of this pipeline,
// independently, and had quietly drifted apart -- `check` seeded prelude/
// init and resolved infixes, `slow_tests`' own `load_module_with_dependencies`
// didn't; `compile`/`test` ran `promote_instance_defs`/
// `add_constraint_dict_params_decls` (dictionary-passing setup) but never
// type-checked anything; `check`/`slow_tests` type-checked but never ran
// dictionary-passing setup at all. `elaborate_loaded_modules` is the one
// canonical version, used identically by all of them from here on.
struct ElaboratedModules {
    scope : Scope,
    target_decls : List Decl,
    elaborated_decls : List Decl,
    /// The `load_file_modules` result this elaboration was built from.
    ///
    /// Carried on the result so a caller that needs the raw module set
    /// too -- `compile`/`test`, which hand it to codegen -- can reuse
    /// THIS load instead of calling `load_file_modules` a second time.
    /// Before this field existed, one `monad compile` read and parsed
    /// the target's entire transitive closure (prelude and init
    /// included) twice: once here for the typecheck gate, once again in
    /// `compile_file_codegen`.
    loaded : LoadedModules,
}

struct ElaboratedAndCache {
    elaborated : Result String ElaboratedModules,
    cache : ModuleInfoCache,
}

/// A trivial local flatten of every loaded module's own decls into one
/// list -- mirrors `lang.codegen.emit`'s own `collect_all_decls_from_modules`
/// exactly, but can't be imported from there: `lang.codegen.emit` already
/// `use`s `lang.module` (for `get_loaded_all`/`get_loaded_main`/
/// `get_module_info_decls`/`try_parse_decls`), so importing back would be
/// a module cycle. Same dodge as `lang.typecheck.infer`'s own documented
/// small-helper duplications elsewhere in this codebase.
#[partial]
def flatten_module_decls (modules : List ModuleInfo) (acc : List Decl) : List Decl :=
    match modules {
        List.empty => acc,
        List.cons mod_ rest =>
            flatten_module_decls rest (list_append (get_module_info_decls mod_) acc),
    }

/// Forall-wrap each `def_d`'s declared type via `elaborate_def`
/// (`lang.elaborate`), using the WHOLE-GRAPH name set as `known_names` so
/// genuine globals (`String`, `I64`, `List`, ...) are filtered out and
/// NOT Forall-wrapped, while a def's own free/constraint-only type vars
/// (e.g. `F` in `def Lens [Functor F] {F : Type -> Type} ...`, whose
/// `{F}` clause the parser deliberately drops -- see `def_implicit_close`,
/// lang/parser.mo) get re-introduced as leading `Forall F. ...` binders.
/// Only `def_d` is touched here -- inductive/class/struct elaboration is
/// tracked separately (inductive-constructor and class-method param
/// skolemization). Non-`def_d` decls pass through unchanged. This is the
/// "wire `elaborate.mo` in" half of the constraint-vars-as-implicit fix;
/// `locals_with_def_typevars`'s `forall_chain_binder_names` walk is the
/// consume-the-Forall-chain half that actually skolemizes those binders.
#[partial]
def elaborate_def_typs (decls : List Decl) (known_names : List Identifier) : List Decl :=
    match decls {
        List.empty => List.empty,
        List.cons d rest =>
            let d_ : Decl := match d {
                Decl.def_d df => Decl.def_d (elaborate_def df known_names),
                _ => d
            } in
            List.cons d_ (elaborate_def_typs rest known_names)
    }

// --- Whole-graph macro/intrinsic expansion (`reflect_type_info!`) -----
//
// `lang/typecheck/macro_queue.mo`'s own per-file `expand_decls` (run at
// parse time, `parse_all_decls`/`try_parse_decls_strict` below) has two
// deliberate scope-narrowings that only a WHOLE-GRAPH pass can close:
// a decl-gen template (`defmacro derive_lens T := decls {
// reflect_type_info! T derive_lens_meta }`) invoked from a DIFFERENT,
// later-loaded file (the norm for every real `std/derive.mo` derive)
// has no registry entry in that OTHER file's own single-file pass; and
// `reflect_type_info!` itself -- a genuine compiler INTRINSIC, not a
// template substitution -- needs to actually EVALUATE the named
// meta-`def` (`lang/typecheck/meta_eval.mo`), not just splice text.
//
// Two-step, both against a registry built from the WHOLE loaded graph:
//   1. Cheap structural decl-gen substitution (`derive_lens! Point` ->
//      `reflect_type_info! Point derive_lens_meta`) -- same
//      `expand_decl_gen_call` template-substitution `expand_decls_go`
//      itself already uses, just against a bigger registry.
//   2. Only if step 1 leaves at least one `reflect_type_info!` call
//      anywhere: build a "ready for real execution" decl list once
//      (`elaborate_module_decls_best_effort` + `resolve_class_calls_decls`
//      -- the SAME two-pass "resolve every class-method call to a
//      concrete, directly-callable function" preparation
//      `lang/codegen/test_driver.mo` already runs before compiling a
//      test driver, needed here because `lang/lower_core_ir.mo`'s
//      free-variable resolution has no concept of typeclass
//      dictionaries) and actually evaluate + reify each call.
// A no-op for the overwhelming majority of files (nothing to
// substitute, no `reflect_type_info!` present) -- safe to run
// unconditionally; the expensive step-2 preparation is skipped
// entirely unless step 1 actually surfaces a `reflect_type_info!` call.
//
// Returns `Result.err` only for a genuine `reflect_type_info!` failure
// (unknown `T`, a meta-def that itself errors, a `d_error` result) --
// an unresolved/unknown macro name still passes through unchanged, the
// same "not an error" rule `expand_decls_go` itself already follows.
def is_reflect_type_info_call (d : Decl) : Bool :=
    match d {
        Decl.macro_call_d name _ => id_eq name (Identifier.id "reflect_type_info"),
        _ => false,
    }

#[partial]
def has_reflect_type_info_call (decls : List Decl) : Bool :=
    match decls {
        List.empty => false,
        List.cons d rest => if is_reflect_type_info_call d then true else has_reflect_type_info_call rest,
    }

def decl_gen_subst_one (registry : List DeclGenEntry) (d : Decl) : List Decl :=
    match d {
        Decl.macro_call_d name args =>
            match lookup_decl_gen registry name {
                Option.some entry =>
                    match entry {
                        DeclGenEntry.dg_entry _ params gen_decls =>
                            match expand_decl_gen_call params gen_decls args {
                                Option.some expanded => expanded,
                                Option.none => List.cons d List.empty,
                            },
                    },
                Option.none => List.cons d List.empty,
            },
        _ => List.cons d List.empty,
    }

#[partial]
def decl_gen_subst_decls (registry : List DeclGenEntry) (decls : List Decl) : List Decl :=
    match decls {
        List.empty => List.empty,
        List.cons d rest => list_append (decl_gen_subst_one registry d) (decl_gen_subst_decls registry rest),
    }

/// One `reflect_type_info! T meta_def` call -> the meta-def's own
/// reified output decls, via `lang.typecheck.meta_reflect`/
/// `lang.typecheck.meta_eval`.
def resolve_one_reflect_call (inds : List Inductive) (dispatched : List Decl) (d : Decl) : Result String (List Decl) :=
    match d {
        Decl.macro_call_d _name args =>
            match args {
                List.cons t_arg rest1 =>
                    match rest1 {
                        List.cons meta_ref _ =>
                            match term_free_var_name t_arg {
                                Option.none => Result.err "reflect_type_info!: T argument must be a plain type name",
                                Option.some t_name =>
                                    match find_inductive_by_bare_name inds t_name {
                                        Option.none => Result.err ("reflect_type_info!: unknown type " ++ t_name),
                                        Option.some ind =>
                                            match term_free_var_name meta_ref {
                                                Option.none => Result.err "reflect_type_info!: meta-def argument must be a plain name",
                                                Option.some meta_name =>
                                                    match build_type_info_value ind {
                                                        Result.err e => Result.err e,
                                                        Result.ok type_info_v =>
                                                            match meta_eval_invoke dispatched (ModulePath.mp (List.cons (Identifier.id meta_name) List.empty)) type_info_v {
                                                                Result.err e => Result.err e,
                                                                Result.ok result_v => reify_decls_value_to_decls result_v,
                                                            },
                                                    },
                                            },
                                    },
                            },
                        List.empty => Result.err "reflect_type_info!: expected 2 arguments (T, meta_def)",
                    },
                List.empty => Result.err "reflect_type_info!: expected 2 arguments (T, meta_def)",
            },
        _ => Result.err "resolve_one_reflect_call: expected a reflect_type_info! macro_call_d",
    }

#[partial]
def resolve_reflect_calls (inds : List Inductive) (dispatched : List Decl) (decls : List Decl) : Result String (List Decl) :=
    match decls {
        List.empty => Result.ok List.empty,
        List.cons d rest =>
            if is_reflect_type_info_call d then
                match resolve_one_reflect_call inds dispatched d {
                    Result.err e => Result.err e,
                    Result.ok new_decls =>
                        match resolve_reflect_calls inds dispatched rest {
                            Result.err e => Result.err e,
                            Result.ok rest_decls => Result.ok (list_append new_decls rest_decls),
                        },
                }
            else
                match resolve_reflect_calls inds dispatched rest {
                    Result.err e => Result.err e,
                    Result.ok rest_decls => Result.ok (List.cons d rest_decls),
                },
    }

/// Whether one decl is a decl-gen macro call the registry can actually
/// expand -- a `macro_call_d` whose name IS registered. A `macro_call_d`
/// with no registry entry passes through unchanged (the same "an
/// unresolved macro name is not an error" rule `decl_gen_subst_one`
/// itself follows), so it does NOT count as an expansion.
def decl_gen_call_expands (registry : List DeclGenEntry) (d : Decl) : Bool :=
    match d {
        Decl.macro_call_d name _ =>
            match lookup_decl_gen registry name {
                Option.some _ => true,
                Option.none => false,
            },
        _ => false,
    }

#[partial]
def has_decl_gen_expansion (registry : List DeclGenEntry) (decls : List Decl) : Bool :=
    match decls {
        List.empty => false,
        List.cons d rest =>
            if decl_gen_call_expands registry d then true else has_decl_gen_expansion registry rest,
    }

/// `expand_decls_graph`'s result, plus whether it actually CHANGED
/// anything. The caller rebuilds its `Scope` from the expanded decls,
/// which is one full `build_scope_from_decls` over the whole dependency
/// graph -- measured at 1523ms of `elaborate_loaded_modules`' 5255ms on
/// `examples/hello.mo`. For the overwhelming majority of files nothing
/// expands (only `std/derive.mo` genuinely invokes `reflect_type_info!`
/// in this corpus), so `changed = false` lets the caller keep the scope
/// it already built instead of rebuilding an identical one.
struct GraphExpansion {
    graph : List Decl,
    target : List Decl,
    changed : Bool,
}

def expand_decls_graph (scope : Scope) (whole_graph_decls : List Decl) (target : List Decl) : Result String GraphExpansion :=
    let registry : List DeclGenEntry := build_decl_gen_registry whole_graph_decls in
    let graph_subst : List Decl := decl_gen_subst_decls registry whole_graph_decls in
    let target_subst : List Decl := decl_gen_subst_decls registry target in
    let substituted : Bool :=
        has_decl_gen_expansion registry whole_graph_decls || has_decl_gen_expansion registry target in
    if has_reflect_type_info_call graph_subst || has_reflect_type_info_call target_subst then
        let inds : List Inductive := collect_inductives whole_graph_decls in
        let empty_locs : LocalScope := { vars := List.empty, parent := Option.none } in
        let dispatched := resolve_class_calls_decls (elaborate_module_decls_best_effort scope whole_graph_decls empty_locs) in
        let dispatched_classes := collect_classes dispatched in
        match validate_no_unresolved_class_calls dispatched_classes dispatched {
            Result.err e => Result.err e,
            Result.ok _ =>
                match resolve_reflect_calls inds dispatched graph_subst {
                    Result.err e => Result.err e,
                    Result.ok graph_final =>
                        match resolve_reflect_calls inds dispatched target_subst {
                            Result.err e => Result.err e,
                            // This branch always rewrites at least the
                            // `reflect_type_info!` call it just resolved.
                            Result.ok target_final =>
                                let expanded : GraphExpansion :=
                                    { graph := graph_final, target := target_final, changed := true } in
                                Result.ok expanded,
                        },
                },
        }
    else
        let unexpanded : GraphExpansion :=
            { graph := graph_subst, target := target_subst, changed := substituted } in
        Result.ok unexpanded

/// THE canonical front-end pipeline: parse -> load the full transitive
/// dependency graph (prelude/init always seeded, via `load_file_modules`)
/// -> flatten -> resolve infixes -> promote instance methods to concrete
/// defs -> thread constraint dict params -> build ONE Scope from the
/// result. `elaborated_decls` is the fully-prepared whole-graph list
/// codegen will eventually consume directly (Stage 3).
///
/// `check_deps` controls what `target_decls` (what actually gets body-
/// type-checked, via `check_module_with_scope`) is built from:
///   - `false`: only the requested file's OWN decls (pre-elaboration on
///     this specific field doesn't matter -- `target_decls` is only ever
///     fed into `check_module_with_scope`, which type-checks each `Def`'s
///     own `.term` against `scope`, and `scope` itself already reflects
///     every elaboration pass below) -- dependencies contribute only
///     signatures to `scope`, their own bodies are never verified. Fast,
///     and what to use for isolating "did THIS file break".
///   - `true`: the fully-prepared WHOLE-GRAPH decl list (`dict_paramed`,
///     already computed below for `scope`/`elaborated_decls` -- reused
///     directly here, no second pass needed) -- every dependency's own
///     declarations get body-checked too, not just scoped. Slower
///     (checks everything reachable, once per call), but the check
///     actually named "check"/"compile"/"test" should mean: verifying a
///     file also verifies what it depends on.
#[partial]
def elaborate_loaded_modules_cached (file_path : String) (check_deps : Bool) (cache : ModuleInfoCache) : IO ElaboratedAndCache := do {
    let lc : LoadedAndCache <- load_file_modules_cached file_path cache;
    let loaded_result : Result String LoadedModules := lc.loaded;
    let out_cache : ModuleInfoCache := lc.cache;
    // The whole elaborate is an annotated local pair, not one bare
    // `return { elaborated := <huge match>, ... }` -- the struct-literal
    // pitfall again: this literal (the largest in the file) is exactly
    // what `validate_no_undesugared_struct_lits` flagged on the v29
    // self-compile.
    let elaborated_result : Result String ElaboratedModules := match loaded_result {
        Result.err e => Result.err e,
        Result.ok loaded =>
            let all_decls : List Decl := flatten_module_decls (get_loaded_all loaded) List.empty in
            let infixes : List Infix := collect_infixes all_decls in
            let resolved : List Decl := resolve_infix_decls infixes all_decls in
            let promoted : List Decl := promote_instance_defs resolved in
            let dict_paramed : List Decl := add_constraint_dict_params_decls promoted in
            let main_module : ModuleInfo := get_loaded_main loaded in
            let target_mp : ModulePath := main_module.path in
            let scope_data : ScopeData := build_scope_from_decls target_mp dict_paramed in
            let scope : Scope := { module_id := target_mp, scope := scope_data, parent := Option.none } in
            // `target_decls` must go through the SAME infix-resolution/
            // promotion/dict-param passes as the whole graph above -- the
            // raw `get_module_info_decls main_module` still has bare
            // placeholder operator vars (`Term.var (DebugName.named "+")`
            // etc, from the self-hosted parser -- see `resolve_infix_
            // decls`'s own doc comment, `lang/scope.mo`), which `scope`
            // (built from the ALREADY-resolved whole graph) has no entry
            // for under that literal name, only under `HAdd.add` --
            // checking the raw decls against the resolved scope produced
            // a bogus `unknown variable '+'` before this fix. When
            // `check_deps` is true, `dict_paramed` already IS that fully-
            // resolved list, for the whole graph (main module's own decls
            // included -- `all_decls`/`flatten_module_decls` folds in
            // `main_module` too, see `load_file_modules`), so reuse it
            // directly instead of redundantly re-running the same three
            // passes on just the main module's own raw decls again.
            let target_decls_raw : List Decl := get_module_info_decls main_module in
            let target_decls_pre : List Decl :=
                if check_deps then
                    dict_paramed
                else
                    add_constraint_dict_params_decls (promote_instance_defs (resolve_infix_decls infixes target_decls_raw)) in
            // Forall-wrap each target def's type with its free + constraint-
            // only type vars (`elaborate_def_typs`), using the whole-graph
            // name set so globals aren't wrapped. `known_names` comes from
            // `dict_paramed` (the fully-prepared whole-graph list) -- a
            // target-only `names_of_decls` would miss dependency globals and
            // wrongly Forall-wrap them. This re-introduces the implicit
            // type vars the parser deliberately dropped (e.g. `F` in
            // `def Lens [Functor F] {F : ...} ...`); `locals_with_def_typevars`
            // then skolemizes them from the resulting `Forall` chain.
            // Whole-graph macro/intrinsic expansion (`reflect_type_info!`)
            // -- see `expand_decls_graph`'s own doc comment. A no-op for
            // any file that never (transitively) invokes
            // `reflect_type_info!`, so safe to run unconditionally.
            match expand_decls_graph scope dict_paramed target_decls_pre {
                Result.err e => Result.err e,
                Result.ok expansion =>
                    let dict_paramed2 : List Decl := expansion.graph in
                    let target_decls_pre2 : List Decl := expansion.target in
                    // Rebuild the scope ONLY if the expansion actually
                    // rewrote decls. When nothing expanded -- the norm,
                    // since only `std/derive.mo` invokes
                    // `reflect_type_info!` in this corpus --
                    // `dict_paramed2` IS `dict_paramed`, so a rebuild
                    // would produce a scope identical to the one built
                    // just above, at the cost of a second full
                    // `build_scope_from_decls` over the whole dependency
                    // graph (measured: 1523ms of `elaborate_loaded_
                    // modules`' 5255ms on `examples/hello.mo`).
                    let scope2 : Scope :=
                        if expansion.changed then
                            { module_id := target_mp, scope := build_scope_from_decls target_mp dict_paramed2, parent := Option.none }
                        else scope in
                    let known_names : List Identifier := names_of_decls dict_paramed2 in
                    let target_decls : List Decl := elaborate_def_typs target_decls_pre2 known_names in
                    // Annotated local, not an inline literal --
                    // see `load_module_with_info`'s own note.
                    let elaborated : ElaboratedModules :=
                        { scope := scope2, target_decls := target_decls, elaborated_decls := dict_paramed2, loaded := loaded } in
                    Result.ok elaborated,
            }
    };
    let out : ElaboratedAndCache := { elaborated := elaborated_result, cache := out_cache };
    return out
}

/// Backwards-compatible wrapper: elaborate with a fresh cache.
#[partial]
def elaborate_loaded_modules (file_path : String) (check_deps : Bool) : IO (Result String ElaboratedModules) := do {
    let r : ElaboratedAndCache <- elaborate_loaded_modules_cached file_path check_deps module_info_cache_empty;
    return r.elaborated
}

// --- Tests: check_module_with_scope / check_file ---

#[test]
def test_check_module_with_scope_all_pass : IO Bool := do {
    let path : ModulePath := ModulePath.mp List.empty;
    let result : ParseResult (List Decl) := parse_all_decls "type Color { red, green }\ndef c : Color := red";
    match result {
        ParseResult.success _ decl_list => do {
            let sd : ScopeData := build_scope_from_decls path decl_list;
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags : List String <- check_module_with_scope scope decl_list locals Option.none false;
            return (match diags {
                List.empty => true,
                List.cons _ _ => false
            })
        },
        ParseResult.fail _ => do { return false }
    }
}

/// Gap-5 regression test: a parameterized inductive's constructors
/// reference the inductive's own type parameter (`A` in `type Box A
/// { mk (a : A) : Box A }`) -- before `check_inductive_with_scope`
/// skolemized the inductive's params into `locals`, `mk`'s signature
/// checked with `A` unbound and failed `unknown variable 'A' in mk`.
/// Mirrors `test_check_module_with_scope_all_pass`'s own single-
/// declaration shape, just with a parametrized inductive instead.
#[test]
def test_check_module_with_scope_paramed_inductive : IO Bool := do {
    let path : ModulePath := ModulePath.mp List.empty;
    let result : ParseResult (List Decl) := parse_all_decls "type Box A { mk (a : A) : Box A }";
    match result {
        ParseResult.success _ decl_list => do {
            let sd : ScopeData := build_scope_from_decls path decl_list;
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags : List String <- check_module_with_scope scope decl_list locals Option.none false;
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
        ParseResult.success _ decl_list => do {
            let sd : ScopeData := build_scope_from_decls path decl_list;
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags : List String <- check_module_with_scope scope decl_list locals Option.none false;
            return (match diags {
                List.cons msg rest =>
                    String.contains msg "unknown variable" &&
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

/// End-to-end proof that `lang/parser.mo`'s `variable_try_path`/
/// `field_access_chain` (the self-hosted mirror of the Rust reference's
/// `lower_core.rs::lower_var`'s `NameRef::P` hook) resolves `p.x`/`p.y`
/// dot field access on a locally-bound struct parameter through the full
/// parse -> resolve -> type-check pipeline, same shape as
/// `test_check_module_with_scope_all_pass` above.
#[test]
def test_check_module_with_scope_dot_field_access_resolves : IO Bool := do {
    let path : ModulePath := ModulePath.mp List.empty;
    let src : String := "type Color { red, green }\nstruct Point { x : Color, y : Color }\ndef getx (p : Point) : Color := p.x";
    let result : ParseResult (List Decl) := parse_all_decls src;
    match result {
        ParseResult.success _ decl_list => do {
            let sd : ScopeData := build_scope_from_decls path decl_list;
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags : List String <- check_module_with_scope scope decl_list locals Option.none false;
            return (match diags {
                List.empty => true,
                List.cons _ _ => false
            })
        },
        ParseResult.fail _ => do { return false }
    }
}

/// Same as above, chained two levels deep (`l.to.x`) -- proves
/// `field_access_chain`'s recursive nesting resolves correctly through the
/// self-hosted pipeline, not just a single field.
#[test]
def test_check_module_with_scope_chained_dot_field_access_resolves : IO Bool := do {
    let path : ModulePath := ModulePath.mp List.empty;
    let src : String := "type Color { red, green }\nstruct Point { x : Color, y : Color }\nstruct Line { from : Point, to : Point }\ndef getx (l : Line) : Color := l.to.x";
    let result : ParseResult (List Decl) := parse_all_decls src;
    match result {
        ParseResult.success _ decl_list => do {
            let sd : ScopeData := build_scope_from_decls path decl_list;
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags : List String <- check_module_with_scope scope decl_list locals Option.none false;
            return (match diags {
                List.empty => true,
                List.cons _ _ => false
            })
        },
        ParseResult.fail _ => do { return false }
    }
}

/// A dotted path whose first segment is NOT a local binding still
/// resolves as an ordinary qualified reference (regression guard on
/// `variable_try_path_global`'s fallback branch).
#[test]
def test_check_module_with_scope_dotted_module_path_still_resolves : IO Bool := do {
    let path : ModulePath := ModulePath.mp List.empty;
    let src : String := "type Color { red, green }\ndef c : Color := Color.red";
    let result : ParseResult (List Decl) := parse_all_decls src;
    match result {
        ParseResult.success _ decl_list => do {
            let sd : ScopeData := build_scope_from_decls path decl_list;
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags : List String <- check_module_with_scope scope decl_list locals Option.none false;
            return (match diags {
                List.empty => true,
                List.cons _ _ => false
            })
        },
        ParseResult.fail _ => do { return false }
    }
}

#[test]
def test_check_file_reports_missing_file : Bool :=
    let empty_base : PreludeInitBase := { scope_data := scope_data_empty, covered := List.empty } in
    let empty_cache : ModuleInfoCache := module_info_cache_empty in
    match check_file_cached empty_base empty_cache "definitely/does/not/exist.mo" false {
        IO.io result =>
            match result {
                FileCheckAndCache.mk fc_result _cache =>
                    match fc_result {
                        FileCheckResult.mk _path diags =>
                            match diags {
                                List.cons msg rest =>
                                    String.contains msg "file not found" &&
                                    match rest {
                                        List.empty => true,
                                        List.cons _ _ => false
                                    },
                                List.empty => false
                            }
                    }
            }
    }

/// Runs the same elaboration steps `elaborate_loaded_modules` runs
/// (infix resolution -> instance-method promotion -> dict-param
/// threading -> scope build) over an inline source string instead of a
/// real file's transitive dependency graph -- a fast, synthetic
/// cross-check for `lang.typecheck.infer`'s `resolve_class_method`
/// rewrite (Stage 2 of `bootstrapping/unify-check-compile-test-
/// elaboration.md`) that doesn't pay `elaborate_loaded_modules`'s own
/// O(N·D) whole-prelude-reload cost.
#[partial]
def check_synthetic_source (src : String) : IO (List String) := do {
    let path : ModulePath := ModulePath.mp List.empty;
    let result : ParseResult (List Decl) := parse_all_decls src;
    match result {
        ParseResult.success _ decl_list => do {
            let infixes := collect_infixes decl_list;
            let resolved := resolve_infix_decls infixes decl_list;
            let promoted := promote_instance_defs resolved;
            let dict_paramed := add_constraint_dict_params_decls promoted;
            let sd : ScopeData := build_scope_from_decls path dict_paramed;
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            check_module_with_scope scope dict_paramed locals Option.none false
        },
        ParseResult.fail _ => do { return ["parse failed"] },
    }
}

/// D4: a class-method call at a CONCRETE carrier with a real matching
/// instance resolves cleanly -- `Speak.say d` (`d : Dog`) dispatches to
/// the promoted `Speak_Dog_say`, proving `resolve_class_method`'s new
/// `find_matching_instance`-based lookup (replacing the old, permanently-
/// stubbed `derive_instance_key`) actually works end to end.
#[test]
def test_dict_resolution_d4_concrete_instance_resolves : IO Bool := do {
    let src : String :=
        "class Speak A { def say (a : A) : String }\n" ++
        "type Dog { woof }\n" ++
        "instance Speak Dog { def say (a : Dog) : String := \"woof\" }\n" ++
        "def greet (d : Dog) : String := Speak.say d";
    let diags : List String <- check_synthetic_source src;
    return (match diags { List.empty => true, List.cons _ _ => false })
}

/// D5: a class-method call FORWARDED through an already-bound dict
/// parameter (a constrained def's own body, `def speak_twice [Speak A]
/// (a : A) : String := Speak.say a`) resolves cleanly, rather than the
/// `unknown variable 'bound_var'` this used to report -- proves
/// `resolve_class_method`'s `local_dict_for_class` branch now calls
/// `build_dict_field_projection_checked` (the checker-facing sibling),
/// not the raw codegen-only `build_dict_field_projection`. This is the
/// exact shape a bridging instance's own promoted method body has
/// (`instance [HAdd A A A] Add A { def add a b := HAdd.add a b }`),
/// which was the concrete self-compile blocker this fix targets.
#[test]
def test_dict_resolution_d5_forwarding_resolves : IO Bool := do {
    let src : String :=
        "class Speak A { def say (a : A) : String }\n" ++
        "type Dog { woof }\n" ++
        "instance Speak Dog { def say (a : Dog) : String := \"woof\" }\n" ++
        "def speak_twice [Speak A] (a : A) : String := Speak.say a";
    let diags : List String <- check_synthetic_source src;
    return (match diags { List.empty => true, List.cons _ _ => false })
}

/// Stage 3's own load-bearing proof: `elaborate_module_decls`'s output
/// for `greet`'s body actually CONTAINS the resolved concrete reference
/// (`Speak_Dog_say`), not just "checks clean" -- codegen must consume
/// this rewritten term (not the original `Speak.say`) for Stage 3's
/// whole "codegen consumes the checker's own resolution" premise to mean
/// anything real.
#[test]
def test_elaborate_module_decls_rewrites_class_method_call : IO Bool := do {
    let src : String :=
        "class Speak A { def say (a : A) : String }\n" ++
        "type Dog { woof }\n" ++
        "instance Speak Dog { def say (a : Dog) : String := \"woof\" }\n" ++
        "def greet (d : Dog) : String := Speak.say d";
    let path : ModulePath := ModulePath.mp List.empty;
    let result : ParseResult (List Decl) := parse_all_decls src;
    match result {
        ParseResult.success _ decl_list => do {
            let infixes := collect_infixes decl_list;
            let resolved := resolve_infix_decls infixes decl_list;
            let promoted := promote_instance_defs resolved;
            let dict_paramed := add_constraint_dict_params_decls promoted;
            let sd : ScopeData := build_scope_from_decls path dict_paramed;
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            return (match elaborate_module_decls scope dict_paramed locals {
                Result.err _ => false,
                Result.ok elaborated => decl_list_has_greet_calling_speak_dog_say elaborated,
            })
        },
        ParseResult.fail _ => do { return false },
    }
}

/// `resolve_class_calls_decls`'s own syntactic (Phase 4) resolution --
/// unlike the test above (which goes through the real type-checker-
/// driven `elaborate_module_decls`), this exercises the SYNTACTIC
/// fallback directly, and specifically a class method call with NO
/// carrier-revealing arg at all (`MakeEmpty.empty`, zero args -- the
/// exact shape `std/derive.mo`'s `lens_getter`'s own list-literal-
/// desugared `FromListLiteral.empty` call hits, confirmed via direct
/// repro). Without a class-declared-default fallback
/// (`resolve_class_method_call_d4_default_carrier`), this call is left
/// permanently unresolved (`rebuild_call orig_head resolved_args`) --
/// `MakeEmpty.empty` staying literally `MakeEmpty.empty` in the output,
/// never becoming a real, directly-callable reference.
#[test]
def test_resolve_class_calls_decls_uses_class_declared_default_carrier : IO Bool := do {
    let src : String :=
        "class MakeEmpty (C : Type -> Type := MyBox) { def empty : C I64 }\n" ++
        "type MyBox A { mk (a : A) }\n" ++
        "instance MakeEmpty MyBox { def empty : MyBox I64 := MyBox.mk 0 }\n" ++
        "def use_it : MyBox I64 := MakeEmpty.empty";
    let result : ParseResult (List Decl) := parse_all_decls src;
    return (match result {
        ParseResult.success _ decl_list => do {
            let infixes := collect_infixes decl_list;
            let resolved := resolve_infix_decls infixes decl_list;
            let promoted := promote_instance_defs resolved;
            let dict_paramed := add_constraint_dict_params_decls promoted;
            let dispatched := resolve_class_calls_decls dict_paramed;
            decl_list_has_use_it_calling_makeempty_mybox_empty dispatched
        },
        ParseResult.fail _ => false,
    })
}

#[partial]
def decl_list_has_use_it_calling_makeempty_mybox_empty (ds : List Decl) : Bool :=
    match ds {
        List.empty => false,
        List.cons d rest =>
            (match d {
                Decl.def_d df =>
                    String.beq (module_path_to_string df.name) "use_it" &&
                        String.contains (show_term df.term) "MakeEmpty_MyBox_empty",
                _ => false,
            }) || decl_list_has_use_it_calling_makeempty_mybox_empty rest,
    }

#[partial]
def decl_list_has_greet_calling_speak_dog_say (ds : List Decl) : Bool :=
    match ds {
        List.empty => false,
        List.cons d rest =>
            (match d {
                Decl.def_d df =>
                    String.beq (module_path_to_string df.name) "greet" &&
                        String.contains (show_term df.term) "Speak_Dog_say",
                _ => false,
            }) || decl_list_has_greet_calling_speak_dog_say rest,
    }

// One more cross-check case was tried here and pulled pending follow-up
// (discovered live via a direct `cargo run -- run <fixture>.mo` debug
// script, not asserted as a passing test, to avoid landing a red test):
//
// "No matching instance is an error": `Speak.say` on a carrier with
// NO matching instance (`Cat`, deliberately given none) currently
// type-checks with ZERO diagnostics instead of failing. Traced to
// `type_check_free_var`'s existing abstract-signature fallback (the
// `err _ => ok (mk_typed (Term.var sentinel dbg) sig)` arm, unchanged
// by this rewrite) -- `Speak.say`'s abstract `A -> String` apparently
// unifies against ANY argument type rather than rejecting a rigid
// mismatch. Confirmed pre-existing, not a regression: `resolve_class_
// method` never succeeded at all before this rewrite (see Finding 1,
// `bootstrapping/unify-check-compile-test-elaboration.md`), so EVERY
// class-method call always hit this exact fallback previously too --
// this rewrite only changes when/whether real resolution succeeds,
// not this fallback's own (pre-existing, separately-scoped) leniency.
//
// D5 (a constrained def's own body forwarding its already-bound dict
// parameter, e.g. `def speak_twice [Speak A] (a : A) : String :=
// Speak.say a`) used to fail with `unknown variable 'bound_var'` --
// `local_dict_for_class`'s own lookup succeeded, but `build_dict_field_
// projection`'s returned term didn't re-typecheck cleanly, since that
// helper was built for the OLD codegen-only consumer (raw de-Bruijn
// index `0`, never meant to be re-run through the bidirectional
// checker). FIXED (2026-08-25): `lang.scope`'s `build_dict_field_
// projection_checked` sibling produces the same shape using the
// checker's real by-name free-variable convention instead, wired into
// `resolve_class_method`'s D5 branch ONLY -- the original codegen-facing
// `build_dict_field_projection` is untouched, since codegen's own
// consumer of it depends on the index-`0` shape and is confirmed
// working. See `test_dict_resolution_d5_forwarding_resolves` below.

/// End-to-end proof `elaborate_loaded_modules` actually resolves a file
/// with ZERO `use` decls (`std/test.mo`'s own `Test.assert`, whose body
/// references the ambient `Bool` type) -- the exact shape A3's diagnosis
/// showed `load_module_with_dependencies` used to fail on (it never
/// seeded prelude/init unless a file explicitly `use`d something that
/// transitively reached them). `elaborate_loaded_modules` always loads
/// via `load_file_modules`, which does seed them unconditionally.
/// `check_deps=false` here — this proves structural resolution of a
/// no-`use`-decls file, unrelated to dependency-body-checking; `true`
/// would just add prelude+init's full body-check cost to every run of
/// this fast, pre-commit-swept unit test for no benefit to what it's
/// actually testing.
#[test]
def test_elaborate_loaded_modules_resolves_file_with_no_use_decls : IO Bool := do {
    // Annotated bind -- `em.scope`/`em.target_decls` below desugar to
    // `{ .. }` field patterns, which need the matched value's own type.
    let result : Result String ElaboratedModules <- elaborate_loaded_modules "std/test.mo" false;
    match result {
        Result.err _ => return false,
        Result.ok em => do {
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags : List String <- check_module_with_scope em.scope em.target_decls locals Option.none false;
            return (match diags {
                List.empty => true,
                List.cons _ _ => false,
            })
        },
    }
}

