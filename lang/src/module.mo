/// Module loading infrastructure for the self-hosted compiler.
/// Parses source text and builds scope data from declarations.

use io {IO}
use std::io {file_exists, is_dir, list_dir, println, read_file}
use std::bench {now, report, report_since, since}
use lib::elaborate {free_vars, names_of_decls, elaborate_def}
use lib::types {
  module_path_to_string_colon,
  Class, ClassDef, Decl, DeclGroup, DebugName, Def, Identifier, Instance, InductConstructor, Inductive, Infix,
  LoadedModules, LocalScope, LocalVar, ModulePath, NamePath, NameRef, Param, Scope,
  ScopeData, ScopeInstance, Struct, StructField, Term, TypeError, def_d, hole, id, id_eq,
  inductive_d, list_reverse, mk, mp, name, nid, show_identifier, show_module_path, show_name_path,
  term_peel, to_name, union_ids,
  use_d,
}
use lib::parser {decls_parser, decls_parser_located, decls_parser_strict, module_path_to_string}
use lib::parser::core {ParseResult, fail, mk, success}
use lib::parser::diagnostic {render_parse_error}
use lib::mote {MoteManifest, Mote}
use lib::pretty {show_term}
use lib::typecheck::macro_apply {expand_decl_gen_call}
use lib::typecheck::macro_queue {DeclGenEntry, build_decl_gen_registry, derive_bridge_decls, expand_decls, lookup_decl_gen}
use lib::typecheck::meta_eval {meta_eval_invoke}
use lib::typecheck::meta_reflect {
  build_type_info_value, collect_inductives, find_inductive_by_bare_name,
  reify_decls_value_to_decls, term_free_var_name,
}
// Deliberately does NOT import `list_append`: this module declares its
// own (see the comment above it), and AGENTS.md item 19 records that the
// two are not interchangeable -- scope's takes an explicit `{A : Type}`
// binder, and both sit on `merge_scope_data`'s measured hot path.
// Importing it here as well made which one won a coin flip.
use lib::scope {
  OpenAlias,
  add_constraint_dict_params_decl_groups, add_constraint_dict_params_decls,
  build_scope_from_decls, build_scope_from_groups, decl_groups_flatten,
  collect_def_names, collect_infixes, collect_open_aliases, constraint_vars,
  filter_valid_open_aliases,
  modpath_eq, npath_map_empty, npath_map_insert, npath_map_lookup, npath_of,
  param_names, promote_instance_decl_groups, promote_instance_defs,
  alias_map_empty, build_alias_map,
  resolve_class_calls_decls, resolve_infix_decl_groups, resolve_infix_decls, resolve_open_alias_decls,
  scope_data_add_def_sig, scope_data_empty, scope_data_find_def_sig,
  scope_find_inductive, scope_push_local, scope_resolve_name,
}
use lib::termination {check_termination_all}
use lib::typecheck::diagnostic {render_type_error}
use lib::typecheck::infer {empty_local_types, empty_locals, mk, type_check}
// `--verbose` per-module/per-stage trace (see `std/src/log.mo`'s own header
// for why the helpers gate themselves and why `bench_step` below prints
// through `timing_line`).
use std::log {module_line, timing_line}
use std::list {Show, all, length}
use std::show {Show}
// `ScopeData.def_refs` is a `std.map` `HashMap ModulePath ScopeDef` (see
// `lang/scope.mo`'s own `use std.map {}` doc comment for why the import
// is empty).
use std::map {}

open IO {file_exists, is_dir, list_dir, println, read_file}
open ParseResult {fail, success}

/// Module path for the prelude
def prelude_module_path : ModulePath := ModulePath.mp [Identifier.id "prelude"]

def init_module_path : ModulePath := ModulePath.mp [Identifier.id "init"]

def std_module_path : ModulePath := ModulePath.mp [Identifier.id "std"]

/// `std.test` -- the module path `test_elaborate_loaded_modules_...` below
/// resolves to a file rather than naming one.
def std_test_module_path : ModulePath := ModulePath.mp [Identifier.id "std", Identifier.id "test"]

/// Parse all declarations from source text.
///
/// Uses `decls_parser_located`, so every term carries its source position
/// as a `Term.ctx` wrapper -- on EVERY path, not just `compile --debug`.
///
/// This is the one production parse site (`load_module_decls`/
/// `parse_module` reach it, and through them `check`, `test`, `compile`
/// and `pretty`), so locating here is what gives the whole compiler a
/// single term shape. It used to use the plain `decls_parser`, and
/// `compile --debug` then RE-READ and RE-PARSED the entire dependency
/// graph through `with_located_decls` to add the wrappers afterwards.
/// Two consequences, both bad:
///   - two parses on the default path, one of them thrown away;
///   - and, worse, a tree shape that only `compile --debug` ever saw.
///     `Term.ctx` is supposed to be semantically transparent (see its own
///     doc comment, `lang/types.mo`), but the ~180 sites that match on
///     term SHAPE only actually stay transparent if something exercises
///     them. Nothing did: CI compiles with `--release`, and `check`/
///     `test` never built a wrapper at all. `infer_carrier_type`
///     (`lang/scope.mo`) had no `Term.ctx` arm, so under `--debug` every
///     `++` on a String failed to resolve its `Append` instance and
///     `monad compile cli/src/main.mo` -- the DEFAULT invocation -- died at
///     `no instance found for `Append.append``.
/// With one shape, the 1467-test corpus exercises wrapper transparency
/// continuously, and `--release`/`--debug` goes back to meaning what it
/// should: whether DWARF is EMITTED, not what the compiler decides.
///
/// Runs the result through `expand_decls` (macro expansion,
/// `lang.typecheck.macro_queue`) before returning — this is the real
/// pipeline's own LENIENT parse site (feeds `build_scope_from_decls`
/// via `load_module_decls`/`parse_module`),
/// one of the two sites the macro-expansion plan calls out by name;
/// its strict twin is `try_parse_decls_strict` below. `ParseResult`'s
/// own `remaining` is untouched -- only the parsed payload changes.
/// (`try_parse_decls_strict` is still on the PLAIN parser: it only feeds
/// rendered parse-error diagnostics on a cold path, so it has no reason
/// to build wrappers. Locating it would be harmless, not useful.)
pub def parse_all_decls (input : String) : ParseResult (List Decl) :=
    match decls_parser_located input {
        ParseResult.success rem decl_list => ParseResult.success rem (expand_decls decl_list),
        ParseResult.fail e => ParseResult.fail e,
    }

/// Parse source text, returning the parsed declarations or none on parse error.
pub def try_parse_decls (input : String) : Option (List Decl) :=
    let result : ParseResult (List Decl) := parse_all_decls input in
    match result {
        ParseResult.success _ decl_list => Option.some decl_list,
        ParseResult.fail _ => Option.none,
    }

/// (The `try_parse_decls_with_locs` twin this section used to hold --
/// pre-expansion `(Decl, Location)` pairs feeding the v1 per-def
/// location table -- is gone: since stage 6 a def's own location is the
/// `Term.ctx` wrapper on its body, which `try_parse_decls_located`
/// above already captures.)

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
pub def try_parse_decls_strict (input : String) (path : Option String) : Result String (List Decl) :=
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
/// e.g., "init/src/process.mo" -> "init/src"
///
/// Delegates to `std.path`'s `raw_parent_dir` rather than keeping its own
/// backwards scan: `llvm/src/link.mo` needs the same operation to create a
/// compile target's directory, and llvm cannot depend on lang.
pub def extract_directory (file_path : String) : String :=
    raw_parent_dir file_path

/// Derive a module name from a file path — e.g. "examples/foo.mo" -> "foo".
/// Factored out of `load_file_modules` (below) so `check_file` can reuse
/// the exact same convention without a caller-supplied `mod_name`.
pub def module_name_from_path (file_path : String) : String :=
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

/// Collapse `.`/`..` segments and repeated separators: `a/../b` -> `b`,
/// `./x` -> `x`, `a//b` -> `a/b`. Pure string work with no filesystem
/// access, so it can never change WHICH file resolves -- only how the
/// winner is spelled.
///
/// It exists so that ONE FILE HAS ONE SPELLING, because a resolved path is
/// what `ModuleInfo.file_path` records and `qualify_modules`'s
/// `dedup_modules_by_file` (`lang/codegen/qualify.mo`) collapses the same
/// file registered under two module paths BY COMPARING THAT STRING.
/// `init/src/number.mo` reaches the loader twice -- as the bare `number`
/// that `init/src/lib.mo`'s `pub use number {*}` names relative to its own
/// directory, and as the `init::number` a mote prefix reads off
/// `mote_relative_file`. From the checkout root both spellings are the same
/// literal, so the dedup catches them. From inside a mote only the manifest
/// can answer one of them and `..` survives in the join, giving
/// `../init/src/number.mo` and `../lang/../init/src/number.mo` for the SAME
/// file: two strings, no dedup, so its declarations were owned by two
/// modules at once and every reference to them read as `declared in
/// number, init.number`. That flood is a qualify failure -- and from inside
/// `cli/` it did not terminate at all: measured, 177 s of 100% CPU with not
/// one syscall after the last resolution.
#[partial]
def normalize_path (p : String) : String :=
    let joined : String := join_path_segments (normalize_segments_go (path_segments_go p 0 0 List.empty) List.empty) "" in
    if String.starts_with "/" p
    then String.concat "/" joined
    else (if String.is_empty joined then "." else joined)

/// `s` split on `/`, with empty segments dropped so a leading `/` and any
/// `//` contribute nothing. `normalize_path` restores the leading slash
/// from the original string, which is the only thing it can carry.
#[partial]
def path_segments_go (s : String) (i : I64) (start : I64) (acc : List String) : List String :=
    if I64.lt i (String.length s)
    then (if String.beq (String.slice s i 1) "/"
          then path_segments_go s (I64.add i 1) (I64.add i 1)
                   (path_push_segment (String.slice s start (I64.sub i start)) acc)
          else path_segments_go s (I64.add i 1) start acc)
    else List.reverse (path_push_segment (String.slice s start (I64.sub (String.length s) start)) acc)

/// Accumulate one segment, skipping an empty one.
def path_push_segment (seg : String) (acc : List String) : List String :=
    if String.is_empty seg then acc else List.cons seg acc

/// `path_segments_go`'s output with `.` dropped and each `..` cancelling
/// the segment before it. A `..` with nothing to cancel is KEPT, and two
/// leading `..`s keep both -- otherwise `../init/src` would normalize to
/// `init/src` and stop naming the file it found.
#[partial]
def normalize_segments_go (segs : List String) (acc : List String) : List String :=
    match segs {
        List.empty => List.reverse acc,
        List.cons s rest =>
            if String.beq s "." then normalize_segments_go rest acc
            else (if String.beq s ".."
                  then (match acc {
                          List.empty => normalize_segments_go rest (List.cons s acc),
                          List.cons hd tl =>
                              if String.beq hd ".."
                              then normalize_segments_go rest (List.cons s acc)
                              else normalize_segments_go rest tl
                        })
                  else normalize_segments_go rest (List.cons s acc))
    }

/// Re-join segments with a single `/` between them and none at either end.
def join_path_segments (segs : List String) (acc : String) : String :=
    match segs {
        List.empty => acc,
        List.cons s rest =>
            if String.is_empty acc
            then join_path_segments rest s
            else join_path_segments rest (String.concat acc (String.concat "/" s))
    }

/// Return the first path in `candidates` that exists on disk (checked in
/// order via `file_exists`), or `Option.none` if none do. Factored out of
/// `resolve_module_file` below, which used to check its 7 candidate paths
/// via a cascade of nested `if/else` `do` blocks, one level per candidate
/// -- functionally a linear "first match wins" scan the whole time, just
/// expressed as 7 levels of nesting instead of a flat walk over a list.
///
/// The winner comes back NORMALIZED, and this is the one place that
/// happens: every resolved path in the compiler comes from here, so doing
/// it at this choke point is what makes a file's spelling independent of
/// whichever candidate happened to find it. See `normalize_path`.
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
            then do { return Option.some (normalize_path path) }
            else first_existing rest
        }
    }
}

/// Read a module path as a MOTE-relative one: the first segment names a mote,
/// whose sources live under its `src/`, and the rest is the module path within
/// it. `llvm.ir` -> `llvm/src/ir.mo`; a lone `std` -> that
/// mote's library root, `std/src/lib.mo`.
///
/// This is what makes `use llvm.ir` find the file at all now that every
/// mote keeps its modules under `src/` (`plans/packaging/package-system.md`
/// §5a) -- `module_path_to_file` joins segments literally and knows nothing
/// about motes. The mote NAMES are still a fixed list here; the manifest-driven
/// table (and the "not a declared dependency" error that comes with it) is §5c.
def mote_relative_file (mp : ModulePath) : String :=
    match mp {
        ModulePath.mp ids =>
            match ids {
                List.empty => "",
                List.cons hd rest =>
                    let mote_src : String := String.concat (identifier_to_string hd) "/src/" in
                    match rest {
                        List.empty => String.concat mote_src "lib.mo",
                        List.cons _ _ =>
                            String.concat mote_src
                                (String.concat (module_path_to_file (ModulePath.mp rest)) ".mo")
                    }
            }
    }

/// The ambient trio's (`prelude`/`init`/`std`) own resolution: its
/// CWD-relative candidate first, then the manifest.
///
/// The fall-through is the whole point of the helper, and it is what makes
/// resolution key off the MOTES rather than the working directory. `candidate`
/// is spelled relative to the checkout root, so it is only the answer when the
/// CWD *is* that root -- which is why `monad check src/main.mo` from inside
/// `cli/` used to report a wall of "unknown variable '++'" rather than loading
/// its own prelude: `first_existing` missed, the trio returned `none`, and no
/// manifest was ever consulted. From the root nothing changes, because the
/// first candidate always hits.
///
/// The manifest half reaches the same three files through each mote's OWN
/// declared path (`lang/mote.toml` declares `init = { path = "../init" }`,
/// say), so `lang/../init/src/prelude.mo` resolves wherever the CWD is.
#[partial]
def resolve_ambient_file (base_dir : String) (mp : ModulePath) (candidate : String) : IO (Option String) := do {
    let r : Option String <- first_existing [candidate];
    match r {
        Option.some p => return (Option.some p),
        Option.none => resolve_via_manifest base_dir mp
    }
}

/// Resolve a module path to a file path, trying different directories
/// First tries relative to base_dir, then the mote layout, then falls back to
/// the stdlib/lang roots for bare (un-mote-qualified) names.
///
/// There is no `examples/` fallback: an example is a mote like any other
/// now (`#![mote { ... }]`), so nothing resolves it by directory name.
#[partial]
def resolve_module_file (base_dir : String) (mp : ModulePath) : IO (Option String) {
    let mp_str := module_path_to_file mp;
    let with_extension := String.concat mp_str ".mo";
    let prelude_path := "init/src/prelude.mo";
    let relative_path := path_join base_dir with_extension;
    let direct_path := with_extension;
    let mote_path := mote_relative_file mp;
    let init_path := String.concat "init/src/" with_extension;
    let std_path := String.concat "std/src/" with_extension;
    let lang_path := String.concat "lang/src/" with_extension;

    if String.beq mp_str "prelude"
    then resolve_ambient_file base_dir mp prelude_path
    // Bare `init`/`std` are ambient re-export hubs (`init/src/lib.mo`/
    // `std/src/lib.mo`) -- their own module NAME no longer matches their
    // FILE name (unlike every other bare top-level module), so they
    // need the same kind of explicit special case `prelude` already
    // has, ahead of the general search below. (`mote_relative_file` would
    // reach the same two files, but only because a one-segment path means
    // "that mote's lib root" -- spelling it out keeps the ambient trio
    // together and independent of that rule.)
    else if String.beq mp_str "init"
    then resolve_ambient_file base_dir mp "init/src/lib.mo"
    else if String.beq mp_str "std"
    then resolve_ambient_file base_dir mp "std/src/lib.mo"
    else do {
        // `examples/` used to be a candidate here (`examples/<stem>.mo`).
        // It is gone: every example now carries a `#![mote { ... }]`
        // annotation naming it and its `deps`, so examples are reached the
        // way motes are -- by their own path, or as a declared dependency --
        // rather than by a name-convention probe into their directory. The
        // probe served nothing once that landed: an example referring to a
        // SIBLING resolves through `relative_path` above, which is tried
        // first and always hit for a file in the same directory.
        let found : Option String <- first_existing [
            relative_path, direct_path, mote_path, init_path, std_path, lang_path,
        ];
        match found {
            Option.some p => return (Option.some p),
            // Still only when every convention missed: the `motes/*/src`
            // search path, then the manifest.
            //
            // `mote_path` assumes a mote's directory is its name, sitting
            // at the working directory -- true for every mote in this
            // workspace, and false for one anywhere else (`motes/demo`
            // declaring `name = "demo"`, say). Discovering the importing
            // file's own mote costs a manifest read, so it happens here,
            // on the miss, and never on the path everything else takes.
            Option.none => do {
                let in_motes_cands <- motes_src_paths mp;
                // The scan above is the BARE-name convention: the stem is
                // probed under every `motes/*/src/`, which is how `use greet`
                // finds `motes/example/src/greet.mo` without naming its mote.
                // A QUALIFIED path (`use example::greet`) needs the other
                // half: the head names the mote, so the rest is read within
                // it. `mote_relative_file` is exactly that reading, and
                // prefixing it with `motes/` is the Rust host's own route to
                // the same file -- it pushes `cwd/motes` onto its search path
                // and then tries `to_mote_file_path` under each root
                // (`resolve_file_path`, core/src/term.rs), giving
                // `motes/example/src/greet.mo`.
                //
                // Tried AFTER the scan, deliberately: for a one-segment path
                // this candidate reads as `<name>/src/lib.mo` (`motes/greet/
                // src/lib.mo`), a file that is never the answer, so letting it
                // go first would only add a failing stat to every bare-name
                // lookup.
                let in_motes_qualified := String.concat "motes/" (mote_relative_file mp);
                let in_motes : Option String <- first_existing (List.append in_motes_cands (List.cons in_motes_qualified List.empty));
                match in_motes {
                    Option.some p => return (Option.some p),
                    Option.none => resolve_via_manifest base_dir mp
                }
            }
        }
    }
}

/// The `motes/<member>/src/<path>.mo` candidates for `mp`, in
/// `IO.list_dir`'s own sorted order.
///
/// Mirrors the Rust host's `build_default_search_paths` (`core/src/lib.rs`),
/// which pushes `cwd/motes` AND every `cwd/motes/*/src` onto its search
/// path -- that is the whole reason a bare `use greet` finds
/// `motes/example/src/greet.mo` without naming its mote, and why the
/// fixture in `examples/test_mote.mo` reads the way it does. Directory
/// probing rather than manifest-driven member resolution, deliberately:
/// the Rust host probes directories, so parity means probing them too.
///
/// `List.empty` outside a checkout with a `motes/` directory -- which is
/// every deployment, so the walk costs one `is_dir` there.
#[partial]
def motes_src_paths (mp : ModulePath) : IO (List String) := do {
    let is_there <- IO.is_dir (Path.path "motes");
    if Bool.not is_there then do { return List.empty }
    else do {
        let entries <- IO.list_dir (Path.path "motes");
        motes_src_paths_go entries (module_path_to_file mp)
    }
}

#[partial]
def motes_src_paths_go (entries : List String) (file_stem : String) : IO (List String) :=
    match entries {
        List.empty => do { return List.empty },
        List.cons name rest => do {
            let tail <- motes_src_paths_go rest file_stem;
            let src := String.concat "motes/" (String.concat name "/src");
            let is_there <- IO.is_dir (Path.path src);
            if Bool.not is_there
            then return tail
            else do {
                let candidate := String.concat src (String.concat "/" (String.concat file_stem ".mo"));
                let exists <- IO.file_exists (Path.path candidate);
                return (if exists then List.cons candidate tail else tail)
            }
        }
    }

/// Resolve `mp` against the importing file's OWN mote manifest: the first
/// segment names either the mote itself, or one of its DECLARED
/// dependencies, whose `[dependencies.<name>] path` says where that mote
/// lives.
///
/// The self case (`use demo.x` from inside mote `demo`) is also what a
/// `lib` alias becomes once rewritten, and `mote_path_within` answers it
/// exactly, off the mote's identity.
///
/// The dependency case is what package-system.md 5c calls the mote table,
/// and it is the half that makes resolution key off the MOTE ROOT rather
/// than the working directory: `../std` from inside `lang` is
/// `lang/../std/src/...` wherever the CWD is, whereas the name-convention
/// candidates in the cascade above (`std/src/list.mo`, `mote_relative_file`)
/// only hold when the CWD is the checkout root. Reached only on a cascade
/// MISS, so the manifest read costs nothing on the path everything takes.
#[partial]
def resolve_via_manifest (base_dir : String) (mp : ModulePath) : IO (Option String) := do {
    let mote : Option MoteManifest <- Mote.discover base_dir;
    match mote {
        Option.none => return Option.none,
        Option.some m => first_existing (manifest_candidates m mp)
    }
}

/// `mp`'s manifest-derived candidate files, self first: a mote may always
/// refer to itself, so when the first segment IS this mote's name that is
/// the answer, and the dependency list is tried only when it is not.
def manifest_candidates (m : MoteManifest) (mp : ModulePath) : List String :=
    match mote_path_within m mp {
        Option.none => mote_dep_files m mp,
        Option.some c => List.cons c (mote_dep_files m mp)
    }

/// The `src/` file a declared dependency's `mp` names -- `mote_path_within`'s
/// mirror for a DEPENDENCY, using the manifest's `path` rather than the
/// mote's name. `List.empty` when `mp`'s first segment is not a dependency
/// the manifest located (undeclared, or declared without a `path`), which
/// leaves the cascade's own answer to stand.
def mote_dep_files (m : MoteManifest) (mp : ModulePath) : List String :=
    match mp {
        ModulePath.mp ids =>
            match ids {
                List.empty => List.empty,
                List.cons hd rest =>
                    // `prelude` is the one module whose NAME is not its FILE
                    // name, and it belongs to `init` -- the same re-spelling
                    // `resolve_module_file`'s own `prelude` special case
                    // applies to the CWD-relative candidate. It is
                    // one-segment by construction, so it never reaches the
                    // `rest` cases below.
                    if String.beq (identifier_to_string hd) "prelude"
                    then mote_dep_file_of m "init" "prelude"
                    // A one-segment path means "that mote's own library
                    // root", the same rule `mote_path_within` applies.
                    else if List.is_empty rest
                    then mote_dep_file_of m (identifier_to_string hd) "lib"
                    else mote_dep_file_of m (identifier_to_string hd)
                             (module_path_to_file (ModulePath.mp rest))
            }
    }

/// The one candidate file a declared dependency `dep` contributes for a
/// module whose file stem is `stem`: `<dep dir>/src/<stem>.mo`.
///
/// `List.empty` when `dep` is undeclared or declared without a `path` --
/// resolution then has nothing better to try, and the cascade's own answer
/// stands.
def mote_dep_file_of (m : MoteManifest) (dep : String) (stem : String) : List String :=
    match MoteManifest.dep_dir_of m dep {
        Option.none => List.empty,
        Option.some dep_dir =>
            List.cons (String.concat (mote_dep_src_root dep_dir) (String.concat stem ".mo")) List.empty
    }

/// `<dep dir>/src/`, kept trailing-slashed so `mote_dep_file_of` can append
/// a stem. `raw_path_join` for the same reason `MoteManifest.src_root` uses
/// it: a `dir` of `""` must not turn into a leading `/`.
def mote_dep_src_root (dep_dir : String) : String :=
    String.concat (raw_path_join dep_dir "src") "/"

/// `<mote>.a.b` -> `<mote dir>/src/a/b.mo`, and a bare `<mote>` -> its
/// `src/lib.mo`. `Option.none` when the path does not name this mote.
def mote_path_within (m : MoteManifest) (mp : ModulePath) : Option String :=
    match mp {
        ModulePath.mp ids =>
            match ids {
                List.empty => Option.none,
                List.cons hd rest =>
                    if String.beq (identifier_to_string hd) m.name
                    then
                        let root := String.concat (MoteManifest.src_root m) "/" in
                        match rest {
                            List.empty => Option.some (String.concat root "lib.mo"),
                            List.cons _ _ =>
                                Option.some (String.concat root
                                    (String.concat (module_path_to_file (ModulePath.mp rest)) ".mo"))
                        }
                    else Option.none
            }
    }

/// Load a module by its ModulePath, returning parsed declarations or none
/// base_dir is the directory to resolve relative imports from
///
/// Resolves ONCE and hands the resolved path to `load_module_decls_at`,
/// which does the reading. That split is the whole point: see that
/// function's own note for the `prelude`-inside-a-mote defect that
/// resolving twice caused.
#[partial]
def load_module_decls (base_dir : String) (mp : ModulePath) : IO (Option (List Decl)) {
    let resolved : Option String <- resolve_module_file base_dir mp;
    match resolved {
        Option.some file_path => load_module_decls_at file_path mp,
        Option.none => do { return Option.none }
    }
}

/// Read and parse an ALREADY-RESOLVED module file.
///
/// This is the half of module loading that touches the disk, and it is
/// PATH-driven on purpose: one resolution, one read. `load_module_with_info`
/// resolves a module, records the resolved path as `ModuleInfo.file_path`,
/// and used to hand the LOADER only that path's DIRECTORY -- so the module
/// was resolved a SECOND time, from the resolved file's own directory, and
/// the second answer is not always the first. Measured (strace): a
/// `prelude` from inside `cli/` resolved correctly to
/// `../init/src/prelude.mo` through `cli`'s manifest, and re-resolved from
/// `../init/src` to nothing at all, because by then the only candidates
/// left are `init`'s own manifest -- where `init` is not a dependency of
/// itself (`MoteManifest.dep_dir_of`'s self arm is what closes that, but
/// the second resolution should not exist in the first place). `prelude`
/// therefore never loaded inside a mote, and a check there reported its
/// names as `unknown variable` -- 23 of them for `cli/src/main.mo`, with
/// the module trace showing the identical 74 modules as a clean root run,
/// because the line is printed BEFORE the load that then failed. The same
/// shape could also silently load a DIFFERENT file than the one
/// `file_path` named.
///
/// `decls_parser`/`parse_all_decls` are LENIENT by design (`decls_try`'s
/// own doc comment, `lang/parser.mo`): any real parse failure partway
/// through a file just stops there and reports SUCCESS with whatever was
/// accumulated so far, discarding everything from that point to EOF with
/// no diagnostic at all. This is the ONE real load path every dependency
/// (not just the target file) goes through, so it's exactly where that
/// leniency turns into silent, hard-to-find data loss -- confirmed live:
/// a `///` doc comment the self-hosted parser choked on partway through
/// `llvm/src/ir.mo` (91 real declarations) silently truncated it to
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
def load_module_decls_at (file_path : String) (mp : ModulePath) : IO (Option (List Decl)) {
    let present : Bool <- file_exists (Path.path file_path);
    if Bool.not present
    then do { return Option.none }
    else do {
        let content : String <- IO.read_file (Path.path file_path);
        let result : ParseResult (List Decl) := parse_all_decls content;
        match result {
            ParseResult.success rem decl_list =>
                if String.is_empty rem
                then do { return Option.some decl_list }
                else do {
                    println (String.concat "parse error: " (String.concat (module_path_to_string mp) " did not fully parse (stopped before end of file) -- remaining text starts:"));
                    println (String.slice rem 0 (if I64.gt (String.length rem) 300 then 300 else String.length rem));
                    return Option.none
                },
            ParseResult.fail _ => do { return Option.none }
        }
    }
}


// --- No longer referenced: the ScopeData-per-module loading path ----
//
// `load_module_scope`/`load_module_scope_default`/`extract_all_
// dependencies_go` below have no callers left. They were the
// `ScopeData`-shaped dependency-loading path, reached only through
// `build_prelude_init_base` and the `ModuleScopeCache` chain, both
// removed once `check_file_cached` was shown never to read the
// `PreludeInitBase` it was handed. The live path is
// `collect_dep_module_infos` (below), which loads `ModuleInfo` (raw
// per-module decls) instead and memoizes through `ModuleInfoCache`.
//
// Kept rather than deleted because `extract_all_dependencies_go`
// carries a measured fix -- seeding its own `visiting` set rather than
// `visited`, AGENTS.md's performance item 9 Fix A, part of the
// 545s -> 97s result -- and deleting the code would delete the only
// place that fix is written down. See AGENTS.md item 19 for the
// standing rule about sweeps that destroy measured optimizations.

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
pub struct LoadedAndCache {
    loaded : Result String LoadedModules,
    cache : ModuleInfoCache,
}

pub struct InfosAndCache {
    infos : List ModuleInfo,
    cache : ModuleInfoCache,
}

/// One queued dependency, paired with the directory it must be resolved
/// FROM -- its importer's own directory.
///
/// The walk used to thread a single `base_dir` through a flat worklist and
/// replace it with each module's directory as it went, so a queued module
/// was resolved from wherever the PREVIOUSLY loaded module happened to
/// live. That is only ever right when the worklist is a straight chain.
/// It went unnoticed because every mote-qualified path in this workspace
/// resolves from the working directory regardless of `base_dir`; a mote
/// found through its own manifest (`motes/demo`) does not, and the
/// dependency silently failed to load -- surfacing much later as an
/// "unknown variable" in the importing file.
pub struct PendingModule {
    path : ModulePath,
    base_dir : String,
}

/// Queue every one of `paths` against the same importer directory.
def pending_from (base_dir : String) (paths : List ModulePath) : List PendingModule :=
    match paths {
        List.empty => List.empty,
        List.cons p rest =>
            let entry : PendingModule := { path := p, base_dir := base_dir } in
            List.cons entry (pending_from base_dir rest)
    }

#[partial]
def collect_dep_module_infos (to_visit : List PendingModule) (visiting : List ModulePath) (visited : List ModuleInfo) (cache : ModuleInfoCache) (verbose : Bool) : IO InfosAndCache :=
    match to_visit {
        List.empty => do {
            // Annotated local, never a bare literal in `return` position
            // -- see AGENTS.md's own "known pitfall" and
            // `validate_no_undesugared_struct_lits`: a bare `return
            // { ... }` never reaches `type_check_struct_lit` with an
            // expected type, so it survives to codegen as a
            // `Literal.struct_lit` and compiles to a void placeholder.
            let out : InfosAndCache := { infos := visited, cache := cache };
            return out
        },
        List.cons pending tail =>
            let head : ModulePath := pending.path in
            if list_contains visiting head then
                // Circular dependency - skip to avoid infinite loop
                collect_dep_module_infos tail visiting visited cache verbose
            else if list_contains_module_info visited head then
                // Already loaded - skip
                collect_dep_module_infos tail visiting visited cache verbose
            else do {
                let new_visiting : List ModulePath := List.cons head visiting;
                // Printed BEFORE the load, not after: the read + parse is
                // the work being watched, and a hang inside a load leaves
                // this line as the last thing on screen -- which names
                // the culprit module. (`ModuleInfoCache` hits from a
                // later importing file re-print; acceptable -- verbose
                // output is already per-decl noisy in `check`, and it
                // gives per-file progress there.)
                // `::`-joined: this line is read by a person, and `::`
                // is how they wrote the module path. `Show ModulePath`
                // renders the dot-joined INTERNAL spelling.
                module_line verbose (module_path_to_string_colon head);
                // Cached: within one `check`/`compile` run the same
                // dependency is reached once per importing file, and
                // re-reading + re-parsing it each time is the dominant
                // cross-file cost (see `ModuleInfoCache`'s own note).
                let loaded : InfoAndCache <- load_module_with_info_cached pending.base_dir head cache;
                match loaded.info {
                    Option.some info => do {
                        // This module's OWN directory is what its own
                        // dependencies resolve from -- the shadowing fix
                        // (`lang/src/parser/string.mo` vs
                        // `init/src/string.mo`) lives here, now carried
                        // per queued entry instead of in one rolling
                        // variable.
                        let dep_base_dir : String := extract_directory info.file_path;
                        let dep_decls : List Decl := info.decl_list;
                        let dep_deps : List ModulePath := extract_use_decls dep_decls;
                        let new_to_visit : List PendingModule :=
                            List.append (pending_from dep_base_dir dep_deps) tail;
                        collect_dep_module_infos new_to_visit new_visiting (List.cons info visited) loaded.cache verbose
                    },
                    Option.none => do {
                        // A dependency that does not resolve is not a
                        // warning: its declarations are now MISSING from
                        // the loaded set, so every name it defined
                        // resurfaces much later as an unrelated `unknown
                        // variable` in whatever file first used it. That
                        // is exactly how the second-resolution defect in
                        // `load_module_decls_at`'s own note hid for a
                        // whole session -- the module trace showed the
                        // same 74 modules as a clean run, because the
                        // line above prints BEFORE the load that then
                        // failed. Named here so the next one is one line
                        // instead of a bisection.
                        println (String.concat "unresolved module: " (String.concat (module_path_to_string_colon head) (String.concat " (from " (String.concat pending.base_dir ") -- its declarations are missing from this run"))));
                        collect_dep_module_infos tail new_visiting visited loaded.cache verbose
                    }
                }
            }
    }


// --- No longer referenced: the shared dependency-fold and the
//     ScopeData merge ------------------------------------------------
//
// Everything from here down to `list_append` has no callers left, for
// the same reason as the cluster above: their last live call sites were
// `build_prelude_init_base` and the `ModuleScopeCache` chain. Kept, not
// deleted, for the same reason -- `merge_scope_data` is the documented
// reference use of `HashMap.merge_buckets` (`std/map.mo`), AGENTS.md
// item 9 Fix B, and `merge_instances`'s `ys`-empty short-circuit is
// what `lang/scope.mo`'s own `list_append` comment points at to explain
// a live optimization there. `list_append`/`list_append_go` at the end
// of this run ARE still live and used throughout this file.

/// The one shared "already-deduplicated dependency list -> one thing per
/// entry" fold: call `loader` once per entry in an already-complete,
/// already-deduplicated transitive closure, cons the result onto `acc`,
/// continue -- no re-derivation, no per-node subtree re-walk.
/// Hard-fails (`Result.err`, via `not_found`) on the first entry `loader`
/// can't resolve at all -- matches `check`/`compile`'s own "a bad
/// dependency is a real error" behavior elsewhere.
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

/// `load_dependency_entries`'s loader for the `Scope` path:
/// `load_module_scope`'s own two-tier resolution (try `base_dir`-relative
/// first, then fall back to an unrestricted global search), extracted so
/// it can be partially applied (`load_scope_entry base_dir`) into
/// `load_dependency_entries`'s `loader` parameter.
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
/// with_deps_and_prelude_cached` (since removed), merging the full
/// shared prelude/init scope every time — as the prime suspect; the
/// `to_list`+refold pattern re-walks/reallocates the ENTIRE base map's
/// buckets on every file regardless of how small that file's own `use`
/// set is. See AGENTS.md's performance section for the measured
/// before/after.
///
/// No empty-`sd2` short-circuit needed (an earlier revision of this
/// function, built on the old `to_list`+refold algorithm, had one,
/// since that algorithm's cost scaled with `|dr1|` regardless):
/// `HashMap.merge_buckets` is a
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
/// sites (in the since-removed `ModuleScopeCache` chain)
/// both passed the LARGE shared-base side as `ins1`/`xs` and the small/
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
        // Look through: this decides whether a def is bodyless, and a
        // located hole is still a hole.
        Term.ctx _loc inner => is_term_hole inner,
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

// --- `check`: multi-error typecheck pass (cli/src/main.mo's `check` command) ---
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
/// `check_module_with_scope`'s own walk, under its own name: the pub
/// entry point below is this plus the termination check, so every existing
/// caller gets both without a second call site to keep in step.
#[partial]
def check_module_decls_with_scope (scope : Scope) (decl_list : List Decl) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match decl_list {
        List.empty => do { return List.empty },
        List.cons d rest => do {
            let here : List String <- check_decl_with_scope d scope locals path verbose;
            let there : List String <- check_module_decls_with_scope scope rest locals path verbose;
            return (list_append here there)
        }
    }

/// A module's type diagnostics, then its termination diagnostics --
/// `lang/src/termination.mo`'s port of the host's `check_termination_all`
/// (`core/src/eval/termination.rs`), which the host likewise runs once per
/// module over that module's own declarations. Before this, both attributes
/// parsed and were ignored self-hosted, so a definition that loops forever
/// checked clean here while the host rejected it.
///
/// The termination pass is a decl-list walk, not a per-decl one, because it
/// needs the whole module to build its call graph; appending its result here
/// keeps the two gates in the one place the host has them.
pub def check_module_with_scope (scope : Scope) (decl_list : List Decl) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) := do {
    // Annotated bind: an IO bind's result type isn't recoverable in pure
    // infer mode, as at `typecheck_module_with_scope` below.
    let diags : List String <- check_module_decls_with_scope scope decl_list locals path verbose;
    return (list_append diags (check_termination_all decl_list))
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
    // On the name AFTER its module qualifier: a dictionary minted by
    // `promote_instance_defs` is now `lang.types::__Dict_Similar_Identifier`,
    // which does not START with `__Dict_`. Missing that would put dict
    // values back through the type checker, and they carry a deliberate
    // `Term.var 0` sentinel convention that does not survive it.
    String.starts_with "__Dict_" (unqualify_instance_name (show_name_path df.name))

/// The part of a synthesized name after its `module::` qualifier, or the
/// whole name when it has none. Mirrors `lang.codegen.emit`'s own
/// `unqualify_def_name`; kept here rather than imported because
/// `lang.module` is a DEPENDENCY of `lang.codegen.emit`, not the other
/// way round.
#[partial]
def unqualify_instance_name (s : String) : String :=
    let idx := find_instance_qualifier_sep s 0 (String.length s) in
    if I64.beq idx (0 - 1) then s else String.slice s (idx + 2) (String.length s - idx - 2)

#[partial]
def find_instance_qualifier_sep (s : String) (i : I64) (n : I64) : I64 :=
    if I64.gt (i + 2) n then (0 - 1)
    else if String.beq (String.slice s i 2) "::" then i
    else find_instance_qualifier_sep s (i + 1) n

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
        Struct.mk name fields _attrs _vis => do {
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
        Def.mk {name, typ, term := body, constraints := _constraints, attrs := _attrs, vis := _vis, ..} => do {
            if verbose then println ("  checking def " ++ show_name_path name) else do { return unit };
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
                    Result.err e => [render_type_error (show_name_path name) path e]
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
def elaborate_def_with_scope ({ name, typ, term := body, constraints, attrs, vis, params } : Def) (scope : Scope) (locals : LocalScope) : Result String Def :=
    if is_term_hole body then
        Result.ok (Def.mk name typ body constraints attrs vis params)
    else
        let locals_ : LocalScope := locals_with_def_typevars typ body scope locals in
        match type_check body typ scope empty_local_types locals_ {
            Result.ok tt => Result.ok (Def.mk name typ (tt.term) constraints attrs vis params),
            Result.err e => Result.err (render_type_error (show_name_path name) Option.none e),
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
pub def elaborate_module_decls_best_effort (scope : Scope) (decl_list : List Decl) (locals : LocalScope) : List Decl :=
    best_effort_decls (elaborate_module_decls_reporting scope decl_list locals)

/// A decl's own name, for the `--verbose` report below. Only `Decl.def_d`
/// carries a body that can fail to elaborate in a way worth naming; every
/// other shape reports its kind, which is enough to say "not a def".
#[partial]
def decl_display_name (d : Decl) : String :=
    match d {
        Decl.def_d def_ => match def_ { Def.mk {name, ..} => show_name_path name },
        Decl.inductive_d i => match i { Inductive.mk name _ _ _ _ _ => show_name_path name },
        _ => "<non-def decl>",
    }

/// What `elaborate_module_decls_best_effort` produced, plus the names of the
/// decls it silently left unchanged.
///
/// The `failed` half exists because swallowing those errors is what made a
/// whole class of bug invisible. A def that fails to elaborate keeps its
/// un-elaborated body, and codegen's syntactic fallbacks then have to cover
/// for it -- when one of THOSE has a gap too, the symptom surfaces stages
/// later as `no instance found for `Append.append`` in a def whose real
/// problem was that it never elaborated. Nothing printed anything in
/// between. Now `--verbose` says how many decls this pass gave up on, and
/// names the first few, so the next one starts with a location instead of a
/// bisect.
pub struct BestEffortElab {
    decls : List Decl,
    failed : List String,
}

#[partial]
def best_effort_decls (r : BestEffortElab) : List Decl := r.decls

#[partial]
def best_effort_failed (r : BestEffortElab) : List String := r.failed

/// Declared return type, not a bare literal at the use site -- the
/// self-hosted checker cannot infer a struct literal's type in `return`/
/// argument position and the self-hosted backend miscompiles one there.
#[partial]
def mk_best_effort_elab (decls : List Decl) (failed : List String) : BestEffortElab :=
    { decls := decls, failed := failed }

#[partial]
def elaborate_module_decls_reporting (scope : Scope) (decl_list : List Decl) (locals : LocalScope) : BestEffortElab :=
    match decl_list {
        List.empty => mk_best_effort_elab List.empty List.empty,
        List.cons d rest =>
            let tail : BestEffortElab := elaborate_module_decls_reporting scope rest locals in
            match elaborate_decl_with_scope d scope locals {
                Result.ok d2 => mk_best_effort_elab (List.cons d2 tail.decls) tail.failed,
                Result.err _ =>
                    mk_best_effort_elab (List.cons d tail.decls)
                        (List.cons (decl_display_name d) tail.failed),
            },
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

// --- Strict positivity (the `check` pass) ---
//
// An inductive's constructors may mention the inductive itself, but only in
// a strictly positive position: a self-occurrence to the LEFT of an arrow
// -- a field whose type is a function *from* the type being declared -- is
// a type that can be built without ever being smaller, which is the same
// circularity the termination check exists to keep out of the logic. The
// Rust reference runs this as `check_strict_positivity`
// (`core/src/eval/type.rs`), once per `Decl::Type` on its live path
// (`core_check_module.rs`); the self-hosted checker did not, so
// `type Bad { mkBad (f : Bad -> I64) }` was rejected by the host and
// accepted here. Measured 2026-09-23 before the port: the host rejects it,
// and the same file checks clean self-hosted.
//
// Polarity starts `true` at each constructor parameter and flips on every
// arrow's DOMAIN (`Term.pi`'s `arg`, `Term.forall`'s `kind`), staying put
// across the codomain. So `Bad -> I64` is negative and rejected, while
// `I64 -> Bad` and `(Bad -> I64) -> I64` -- two flips -- are accepted. Both
// of those were measured against the host rather than reasoned about.
//
// Self-reference is matched on the SPELLING the elaborator left in the
// term, exactly as the reference matches it, and for a qualified occurrence
// the module half is compared too. That half is not decoration: the same
// source checked twice by `target/release/monad-rs` gets different verdicts
// depending on the module the file is checked AS -- `check probe_qual.mo`
// (module `probe_qual`) rejects `type Q { mkQ (f : probe_qual::Q -> I64) }`
// while the identical file named by absolute path (module
// `home.anderscs.src.monad-bootstrap.probe_qual`) accepts it. Comparing the
// name half alone would flag the second invocation too, and would likewise
// flag another module's same-named type; `check_strict_pos`'s own doc
// comment names that as the reason the module is compared.
//
// The message is the reference's `TypeError::Generic` text verbatim, and it
// is rendered through `render_type_error` like every other per-declaration
// diagnostic here. The reference renders it through its `Diagnostic` and so
// prints a context header and a `1:1` span; this compiler's AST carries no
// span to print, which is the pre-existing difference in how the two frame
// an error (see `lang/typecheck/diagnostic.mo`'s own header), not a
// difference in the message.
//
// Deliberately inductive-only: the reference calls this for `Decl::Type`
// and not for `Decl::Struct`, and `check_decl_with_scope` routes a struct to
// `check_struct_with_scope`, so hooking this at `check_inductive_with_scope`
// keeps that boundary without a second guard.

/// Index of the last `::` in `s` (scanning up to `n`), or `found` --
/// started at -1 -- when there is none. A left-to-right scan that remembers
/// its last hit, which is what `strip_module_qualifier`
/// (`lang/src/termination.mo`) does for the same reason: the name half of a
/// qualified reference may itself be dotted (`std::io::IO.println`), so the
/// split has to be at the LAST separator and not the first.
#[partial]
def strict_pos_last_sep (s : String) (i : I64) (n : I64) (found : I64) : I64 :=
    if I64.gt (I64.add i 2) n then found
    else if String.beq (String.slice s i 2) "::" then strict_pos_last_sep s (I64.add i 1) n i
    else strict_pos_last_sep s (I64.add i 1) n found

/// The polarity of the other side of an arrow. A local helper rather than
/// the ambient `not`: this module has never used that name, and it resolves
/// through the same always-on table as everything else -- one line here
/// costs less than a name-resolution question at three call sites.
def strict_pos_flip (b : Bool) : Bool :=
    if b then false else true

/// Is `spelling` an occurrence of the type called `type_str` that THIS
/// module -- `module_str` -- declares?
///
/// A qualified spelling (`mod::Name`) is that type only when both halves
/// agree; a bare one when the whole spelling equals the name, mirroring
/// `check_strict_pos`'s `to_qualified()` split. `type_str` is the type's
/// dotted `show_name_path` spelling, which is also what the elaborator
/// stores for a bare reference (`lower_name_global`,
/// `lang/parser/lower_parse.mo`), and a qualified one is stored as
/// `show_module_path qmod` ++ `"::"` ++ that same spelling
/// (`qualified_ref_symbol`) -- so both sides of each comparison are
/// compared in one convention.
#[partial]
def strict_pos_is_self (module_str : String) (type_str : String) (spelling : String) : Bool :=
    let n : I64 := String.length spelling in
    let idx : I64 := strict_pos_last_sep spelling 0 n (0 - 1) in
    if I64.lt idx 0
    then String.beq spelling type_str
    else String.beq (String.slice spelling (I64.add idx 2) (I64.sub n (I64.add idx 2))) type_str
        && String.beq (String.slice spelling 0 idx) module_str

/// Does `t` contain a non-strictly-positive occurrence of the type called
/// `type_str`? `polarity` is this position's own sign, `true` for a
/// positive one; a self-occurrence under `false` is the error, and that is
/// the only thing this returns `true` for.
///
/// `term_peel` at entry, not a `Term.ctx` arm: the parser stores every term
/// with its source position as a transparent wrapper
/// (`decls_parser_located`), so a located `Term.pi` would match none of the
/// arms below and the walk would silently stop descending -- the failure
/// mode `term_peel`'s own doc comment warns about.
#[partial]
def strict_pos_bad (module_str : String) (type_str : String) (t : Term) (polarity : Bool) : Bool :=
    match term_peel t {
        Term.var _ dbg =>
            if polarity
            then false
            else match dbg {
                DebugName.named id => strict_pos_is_self module_str type_str (show_identifier id),
                DebugName.unnamed => false,
            },
        Term.app fun arg =>
            strict_pos_bad module_str type_str fun polarity || strict_pos_bad module_str type_str arg polarity,
        Term.pi arg ret =>
            strict_pos_bad module_str type_str arg (strict_pos_flip polarity) || strict_pos_bad module_str type_str ret polarity,
        Term.forall _ kind body =>
            strict_pos_bad module_str type_str kind (strict_pos_flip polarity) || strict_pos_bad module_str type_str body polarity,
        // Every other shape is opaque to the rule, matching the reference's
        // `_ => Ok(())` -- in particular `Term.lam`, whose body the
        // reference does not descend into either.
        _ => false,
    }

#[partial]
def strict_pos_params_bad (module_str : String) (type_str : String) (ps : List Param) : Bool :=
    match ps {
        List.empty => false,
        List.cons p rest =>
            match p {
                Param.mk _name typ _mult _default _attrs =>
                    strict_pos_bad module_str type_str typ true || strict_pos_params_bad module_str type_str rest,
            },
    }

#[partial]
def strict_pos_ctors_bad (module_str : String) (type_str : String) (cs : List InductConstructor) : Bool :=
    match cs {
        List.empty => false,
        List.cons c rest =>
            strict_pos_ctor_bad module_str type_str c || strict_pos_ctors_bad module_str type_str rest,
    }

#[partial]
def strict_pos_ctor_bad (module_str : String) (type_str : String) (c : InductConstructor) : Bool :=
    match c {
        InductConstructor.mk _name params _typ => strict_pos_params_bad module_str type_str params,
    }

/// An inductive's strict-positivity diagnostic, or `List.empty` when it has
/// none -- the shape `check_inductive_with_scope` below appends into.
///
/// Runs over the constructors' declared PARAMETERS, not over the
/// constructors' own `typ`: that is where the reference reads them
/// (`cons.params()`), and measured here it is also the only place they are
/// -- an elaborated `InductConstructor`'s `typ` is a hole for the field-free
/// shapes and the params carry every real type.
#[partial]
def check_strict_positivity_with_scope (scope : Scope) (ind : Inductive) (path : Option String) : List String :=
    match scope {
        Scope.mk module_id _sd _parent =>
            match ind {
                Inductive.mk name _params _typ constructors _attrs _vis =>
                    let type_str : String := show_name_path name in
                    if strict_pos_ctors_bad (show_module_path module_id) type_str constructors
                    then [render_type_error type_str path (TypeError.custom ("non-strictly positive occurrence of " ++ type_str))]
                    else List.empty,
            },
    }

#[partial]
def check_inductive_with_scope (ind : Inductive) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match ind {
        Inductive.mk name _params _typ constructors _attrs _vis => do {
            if verbose then println ("  checking type " ++ show_name_path name) else do { return unit };
            let locals_ : LocalScope := locals_with_inductive_params ind scope locals;
            let cons_diags : List String <- check_constructors_with_scope constructors scope locals_ path verbose;
            return (list_append (check_strict_positivity_with_scope scope ind path) cons_diags)
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
            if verbose then println ("    checking constructor " ++ show_name_path name) else do { return unit };
            return (match type_check typ Term.hole scope empty_local_types locals {
                Result.ok _ => List.empty,
                Result.err e => [render_type_error (show_name_path name) path e]
            })
        }
    }

pub struct FileCheckResult {
    path : String,
    diagnostics : List String,
}

/// `check_file_cached`'s own result bundled with the (possibly updated)
/// `ModuleInfoCache`, so `run_check_loop` can thread it forward to the
/// next file in the same run.
pub struct FileCheckAndCache {
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
/// Passes `check_deps=false` to `elaborate_loaded_modules` — see that
/// function's own doc comment for the two-mode rationale. `check_deps=true`
/// (checking the whole dependency closure a file pulls in, not just its
/// own top-level decls) is NOT yet safe to default to here: turning it on
/// for `cli/src/main.mo` (whose closure reaches ≈2200 decls, including this
/// self-hosted compiler's own richly-recursive AST types) caused unbounded
/// memory growth (28GB+ RSS and still climbing after ~9 minutes, had to be
/// killed) — root cause under investigation, see
/// `bootstrapping/check-deps-memory-blowup.md`.
#[partial]
pub def check_file_cached (cache : ModuleInfoCache) (file_path : String) (verbose : Bool) : IO FileCheckAndCache {
    let exists : Bool <- file_exists (Path.path file_path);
    if exists then do {
        if verbose then println ("checking " ++ file_path) else do { return unit };
        let ec : ElaboratedAndCache <- elaborate_loaded_modules_cached file_path false cache verbose;
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

/// Join a directory to one of its own entry names with exactly one
/// separator, whatever the caller's own trailing slash looked like.
///
/// `dir` comes straight off the command line, and `monad test lang/`
/// is at least as natural to type as `monad test lang` -- shell tab
/// completion produces the trailing slash on its own. A plain
/// `dir ++ "/" ++ name` then builds `lang//src`, which recursion
/// compounds into `lang//src//codegen//emit.mo`: still a working path
/// (POSIX collapses repeated slashes) but wrong in every line of
/// output that echoes it back, which is the whole of `check`'s and
/// `test`'s per-file reporting.
///
/// One slash is stripped, not all: `//` is genuinely
/// implementation-defined at the START of a POSIX path, and nothing
/// else here normalizes `.`/`..` either -- arguments stay as typed.
pub def join_path_dir (dir : String) (name : String) : String :=
    if String.ends_with dir "/" then dir ++ name else dir ++ "/" ++ name

/// Walk `dir`'s own entries (as returned by `IO.list_dir`), recursing
/// into subdirectories and keeping `.mo`-suffixed files.
#[partial]
def collect_mo_files_entries (dir : String) (entries : List String) : IO (List String) :=
    match entries {
        List.empty => do { return List.empty },
        List.cons name rest => do {
            let path : String := join_path_dir dir name;
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
pub def expand_check_paths (paths : List String) : IO (List String) :=
    match paths {
        List.empty => do { return List.empty },
        List.cons p rest => do {
            let is_directory : Bool <- is_dir (Path.path p);
            let here : List String <- if is_directory then collect_mo_files p else do { return [p] };
            let there : List String <- expand_check_paths rest;
            return (list_append here there)
        }
    }

/// `join_path_dir` collapses the caller's trailing slash rather than
/// doubling it -- `monad test lang/` used to report every file it found
/// as `lang//src//...`.
#[test]
def test_join_path_dir_no_trailing_slash : Bool :=
    String.beq (join_path_dir "lang" "src") "lang/src"

#[test]
def test_join_path_dir_strips_trailing_slash : Bool :=
    String.beq (join_path_dir "lang/" "src") "lang/src"

/// The fix has to hold at every directory level, not just the first:
/// `collect_mo_files_entries` recurses on its own output, so a doubled
/// slash that survived one join would compound at each one below it.
#[test]
def test_join_path_dir_nested_stays_single : Bool :=
    String.beq (join_path_dir (join_path_dir "lang/" "src") "codegen") "lang/src/codegen"

#[test]
def test_parse_all_decls_empty : Bool :=
    let result : ParseResult (List Decl) := parse_all_decls "" in
    match result {
        ParseResult.success _ _ => true,
        ParseResult.fail _ => false
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
    let name_a : NamePath := NamePath.npath [Identifier.id "a_def"] in
    let name_b : NamePath := NamePath.npath [Identifier.id "b_def"] in
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
            let color_path : NamePath := NamePath.npath [Identifier.id "Color"] in
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

pub struct ModuleInfo {
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
// Keyed on `ModulePath`, which is safe for the current corpus (one
// module per path, no per-file variation in what a path resolves to).
// This caches `ModuleInfo` -- the raw per-module decls -- because that
// is what `elaborate_loaded_modules` needs: its infix/promotion/dict-
// param/expansion passes all run over decls, not over a prebuilt
// `ScopeData`. An earlier `ModuleScopeCache` cached `ScopeData` instead
// and has been removed.
pub struct ModuleInfoCache {
    entries : HashMap String ModuleInfo,
    hits : I64,
    misses : I64,
}

pub def module_info_cache_empty : ModuleInfoCache := {
    entries := npath_map_empty,
    hits := 0,
    misses := 0,
}

def module_info_cache_lookup (key : ModulePath) (cache : ModuleInfoCache) : Option ModuleInfo :=
    npath_map_lookup (npath_of key) cache.entries

def module_info_cache_hit (cache : ModuleInfoCache) : ModuleInfoCache :=
    { cache with hits := cache.hits + 1 }

def module_info_cache_insert (key : ModulePath) (info : ModuleInfo) (cache : ModuleInfoCache) : ModuleInfoCache :=
    { cache with entries := npath_map_insert (npath_of key) info cache.entries, misses := cache.misses + 1 }

/// A `load_module_with_info` that consults (and extends) the cache.
pub struct InfoAndCache {
    info : Option ModuleInfo,
    cache : ModuleInfoCache,
}

#[partial]
def load_module_with_info_cached (base_dir : String) (mp : ModulePath) (cache : ModuleInfoCache) : IO InfoAndCache := do {
    match module_info_cache_lookup mp cache {
        Option.some hit => do {
            let out : InfoAndCache := { info := Option.some hit, cache := module_info_cache_hit cache };
            return out
        },
        Option.none => do {
            let loaded : Option ModuleInfo <- load_module_with_info base_dir mp;
            match loaded {
                Option.some info => do {
                    let out : InfoAndCache := { info := Option.some info, cache := module_info_cache_insert mp info cache };
                    return out
                },
                Option.none => do {
                    let out : InfoAndCache := { info := Option.none, cache := cache };
                    return out
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
            "\n\tdecls: " ++ Show.show (List.map Decl.to_name decl_list : List NamePath)
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
pub struct LoadedModules {
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
/// a real regression via the full `cli/src/main.mo` self-compile: `Reach
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
            // Own aliases FIRST: `build_alias_map` keeps the first entry
            // for a bare name, so a module's own `use`/`open` shadows the
            // ambient prelude/init/std ones -- the same precedence the
            // linear scan this replaced gave for free.
            let alias_names := build_alias_map aliases alias_map_empty in
            ModuleInfo.mk path file_path (resolve_open_alias_decls alias_names decl_list)
    }

#[partial]
def all_module_decl_names (modules : List ModuleInfo) : List String :=
    match modules {
        List.empty => List.empty,
        List.cons m rest => list_append (collect_def_names (m.decl_list)) (all_module_decl_names rest),
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
                    Option.some mi => filter_valid_open_aliases known_names (collect_open_aliases (mi.decl_list)),
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

/// `lib` names the mote a file belongs to, the way Rust's `crate::` names
/// its crate: inside `lang`, `use lib.codegen.emit` IS `lang.codegen.emit`.
///
/// Rewritten to the canonical mote-qualified path here, at load time, and
/// not resolved as a file path directly -- because a module path is also a
/// module's IDENTITY. Left as `lib.codegen.emit` it would be a second
/// module distinct from the same file loaded under its real name, scope
/// would hold both, and codegen would emit `lib.codegen.emit::f` symbols.
///
/// Reads no manifest unless a `lib` use is actually present, so files
/// without one cost nothing.
#[partial]
def resolve_lib_alias_decls (base_dir : String) (decls : List Decl) : IO (List Decl) := do {
    if has_lib_use decls
    then do {
        // The inline `#![mote { ... }]` first, exactly as `mote_of_module`
        // orders it: a file that declares its own mote IS a mote, and `lib`
        // must name it the same way it names one shipping a `mote.toml`.
        // (`mote_attr_position` has not been validated yet at this point in
        // the load, so a MISPLACED annotation is read here too -- it is
        // then reported by `validate_mote_attr` on the same load, which is
        // why reading it early cannot hide the error.)
        match inline_mote_of_decls base_dir decls {
            Option.some m => return (rewrite_lib_uses m.name decls),
            Option.none => do {
                let mote : Option MoteManifest <- Mote.discover base_dir;
                match mote {
                    Option.some m => return (rewrite_lib_uses m.name decls),
                    // Outside any mote (script mode): `lib` names nothing,
                    // and the use is left alone to fail as an ordinary
                    // missing module.
                    Option.none => return decls
                }
            }
        }
    }
    else return decls
}

def has_lib_use (decls : List Decl) : Bool :=
    match decls {
        List.empty => false,
        List.cons d rest =>
            match d {
                Decl.use_d path _ _ =>
                    if is_lib_alias path then true else has_lib_use rest,
                _ => has_lib_use rest
            }
    }

def is_lib_alias (mp : ModulePath) : Bool :=
    match mp {
        ModulePath.mp ids =>
            match ids {
                List.empty => false,
                List.cons hd _ => String.beq (identifier_to_string hd) "lib"
            }
    }

def rewrite_lib_uses (mote : String) (decls : List Decl) : List Decl :=
    match decls {
        List.empty => List.empty,
        List.cons d rest =>
            List.cons (rewrite_lib_use_decl mote d) (rewrite_lib_uses mote rest)
    }

def rewrite_lib_use_decl (mote : String) (d : Decl) : Decl :=
    match d {
        Decl.use_d path filter public =>
            Decl.use_d (lib_alias_path mote path) filter public,
        _ => d
    }

/// `lib.a.b` -> `<mote>.a.b`; a bare `lib` -> `<mote>`, which resolves to
/// that mote's `src/lib.mo` like any other one-segment mote reference.
def lib_alias_path (mote : String) (mp : ModulePath) : ModulePath :=
    match mp {
        ModulePath.mp ids =>
            match ids {
                List.empty => mp,
                List.cons hd rest =>
                    if String.beq (identifier_to_string hd) "lib"
                    then ModulePath.mp (List.cons (Identifier.id mote) rest)
                    else mp
            }
    }

#[partial]
def resolve_lib_alias_decls_opt (base_dir : String) (decls : Option (List Decl)) : IO (Option (List Decl)) := do {
    match decls {
        Option.none => return Option.none,
        Option.some dl => do {
            let rewritten : List Decl <- resolve_lib_alias_decls base_dir dl;
            return (Option.some rewritten)
        }
    }
}

#[partial]
pub def load_module_with_info (base_dir : String) (mp : ModulePath) : IO (Option ModuleInfo) {
    let resolved_path_opt : Option String <- resolve_module_file base_dir mp;
    match resolved_path_opt {
        Option.none => do { return Option.none },
        Option.some file_path => do {
            // The resolved path is what gets READ and what gets recorded --
            // `load_module_decls_at`, not `load_module_decls`, the latter
            // resolving a second time from this file's own directory and
            // free to disagree with the first answer. See that function's
            // own note for the `prelude`-inside-a-mote defect this caused.
            let actual_base_dir : String := extract_directory file_path;
            let raw_decls : Option (List Decl) <- load_module_decls_at file_path mp;
            let decl_list : Option (List Decl) <- resolve_lib_alias_decls_opt actual_base_dir raw_decls;
            match decl_list {
                Option.some decl_list => do {
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
                    let info : ModuleInfo := { path := mp, file_path := file_path, decl_list := decl_list };
                    return (Option.some info)
                },
                Option.none => do { return Option.none }
            }
        }
    }
}

// --- Declared-dependency enforcement (package-system.md 5d) ---------
//
// A mote may only use motes it declared. Checked as ONE pass over the
// already-loaded set rather than inside `resolve_module_file`, for two
// reasons: a manifest is then read once per MODULE instead of once per
// `use` line, and a pass returns real errors where the resolver can only
// return `Option.none` and let the failure resurface later as an unknown
// variable.
//
// Scope of the check: a `use` whose first segment names a mote sitting at
// the working directory -- which is every mote in this workspace. A mote
// found some other way (`motes/demo`, reached through its own manifest)
// is not flagged; enforcing those needs the full mote table with each
// dependency's declared PATH, not just its name.

/// The ambient trio, which every file may use without declaring anything:
/// `prelude` is the language's own, and `init`/`std` are re-export hubs
/// seeded into every file's closure by the loader itself.
def is_ambient_mote (name : String) : Bool :=
    if String.beq name "prelude" then true
    else if String.beq name "init" then true
    else String.beq name "std"

/// Does a mote actually go by `name`? Both places one can live are probed,
/// because both are real resolution paths: beside the working directory
/// under its own name (`mote_relative_file`'s convention, which is how
/// every top-level mote here resolves), and one level down under `motes/`
/// (`motes_src_paths`' convention, which is how `use example::greet`
/// reaches `motes/example/src/greet.mo`).
///
/// Missing the second is not cosmetic: it is exactly the case where a `use`
/// on a `motes/*` mote would go UNREPORTED when its `deps := [...]` entry
/// is deleted, because the head would look like a plain module name.
#[partial]
def is_mote_named (name : String) : IO Bool := do {
    let direct <- file_exists (Path.path (String.concat name "/mote.toml"));
    if direct then return true
    else file_exists (Path.path (String.concat "motes/" (String.concat name "/mote.toml")))
}

#[partial]
def validate_declared_deps (infos : List ModuleInfo) : IO (List String) :=
    match infos {
        List.empty => do { return List.empty },
        List.cons info rest => do {
            let here : List String <- validate_module_deps info;
            let later : List String <- validate_declared_deps rest;
            return (List.append here later)
        }
    }

// ─── The inline `#![mote { ... }]` annotation ────────────────────────
//
// A file outside any mote can declare its own inline instead of shipping a
// `mote.toml`: `#![mote { name := "structs", deps := [init, std] }]`. That
// is what takes `examples/` out of script mode -- before it, `Mote.discover`
// returned `none` for a directory with no `mote.toml`, so an example file
// validated nothing at all.

/// Does this declaration carry the file-level mote attribute?
def is_mote_attr_decl (d : Decl) : Bool :=
    match d { Decl.mote_d _ => true, _ => false }

/// The inline mote a module declares, if its FIRST declaration is a
/// `#![mote { ... }]`. `none` otherwise -- including when the attribute is
/// present but misplaced, which `validate_mote_attr_position` reports
/// separately rather than letting a misplaced attribute half-work (deps
/// enforced, position not).
def inline_mote_of_decls (dir : String) (decl_list : List Decl) : Option MoteManifest :=
    match decl_list {
        List.empty => Option.none,
        List.cons first _rest =>
            match first {
                Decl.mote_d attr => Mote.manifest_of_attr dir attr,
                _ => Option.none
            }
    }

/// The mote a module belongs to: an inline `#![mote { ... }]` attribute
/// wins when present, otherwise the enclosing `mote.toml`.
def mote_of_module (info : ModuleInfo) : IO (Option MoteManifest) := do {
    match inline_mote_of_decls (extract_directory info.file_path) info.decl_list {
        Option.some m => return (Option.some m),
        Option.none => Mote.discover (extract_directory info.file_path)
    }
}

/// The file-level `#![mote { ... }]` is valid ONLY as the first declaration
/// of a file.
///
/// The PARSER deliberately accepts it anywhere (`lang/src/parser.mo`'s
/// `mote_attr_parser`): `decls_try` silently truncates on a parse failure --
/// every declaration from the failure to EOF is discarded with no diagnostic
/// at all (`decls_try`'s own KNOWN GAP comment) -- so rejecting a misplaced
/// attribute there would report far less than it broke. The diagnostic
/// therefore belongs here, on the lowered decl list, where every surrounding
/// declaration is still present.
///
/// At most one error, matching `gate_declared_deps`'s one-message
/// convention: the first misplaced attribute is the one to fix.
def validate_mote_attr_position (info : ModuleInfo) : List String :=
    match info.decl_list {
        List.empty => List.empty,
        List.cons first rest =>
            if is_mote_attr_decl first
            then List.empty
            else misplaced_mote_attr info.file_path rest
    }

def misplaced_mote_attr (file : String) (decl_list : List Decl) : List String :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            if is_mote_attr_decl d
            then [misplaced_mote_attr_error file]
            else misplaced_mote_attr file rest
    }

def misplaced_mote_attr_error (file : String) : String :=
    String.concat "error: `#![mote { ... }]` must be the first declaration in " (String.concat file
    (String.concat "\n  it is a FILE-level annotation, so any declaration above it puts it in the wrong place"
    "\n  hint: move it to the very top of the file, above every declaration"))

/// Keys of an `#![mote { ... }]` that no reader consumes. Only the FIRST
/// declaration is inspected, matching `validate_mote_attr_position`: a
/// misplaced attribute gets the position error, not a pile of key errors
/// about an annotation that does not work at all.
def validate_mote_attr_keys (info : ModuleInfo) : List String :=
    match info.decl_list {
        List.empty => List.empty,
        List.cons first _rest =>
            match first {
                Decl.mote_d attr => Mote.mote_attr_unknown_keys attr,
                _ => List.empty
            }
    }

/// Both halves of the inline attribute's own validation, empty when the file
/// has no inline attribute.
def validate_mote_attr (info : ModuleInfo) : List String :=
    List.append (validate_mote_attr_position info) (validate_mote_attr_keys info)

#[partial]
def validate_module_deps (info : ModuleInfo) : IO (List String) := do {
    match validate_mote_attr info {
        List.cons e _ => return [e],
        List.empty => do {
            let mote : Option MoteManifest <- mote_of_module info;
            match mote {
                // Script mode -- a file outside any mote and with no inline
                // annotation (a one-off). Nothing declared anything, so
                // nothing is undeclared.
                Option.none => return List.empty,
                Option.some m => check_uses_declared m info (extract_use_decls info.decl_list)
            }
        }
    }
}

#[partial]
def check_uses_declared (m : MoteManifest) (info : ModuleInfo) (uses : List ModulePath) : IO (List String) :=
    match uses {
        List.empty => do { return List.empty },
        List.cons u rest => do {
            let here : List String <- check_one_use_declared m info u;
            let later : List String <- check_uses_declared m info rest;
            return (List.append here later)
        }
    }

#[partial]
def check_one_use_declared (m : MoteManifest) (info : ModuleInfo) (u : ModulePath) : IO (List String) := do {
    match use_head_mote u {
        // A one-segment path is a module name, not a mote reference.
        Option.none => return List.empty,
        Option.some head =>
            if is_ambient_mote head then return List.empty
            else if MoteManifest.declares m head then return List.empty
            else do {
                // Only complain about names that really are motes -- a
                // head segment naming nothing is an ordinary
                // module-not-found, reported where it happens.
                let is_mote <- is_mote_named head;
                if is_mote
                then return [undeclared_mote_error m info u head]
                else return List.empty
            }
    }
}

/// The first segment of a multi-segment use path -- the only position a
/// mote name can occupy.
def use_head_mote (u : ModulePath) : Option String :=
    match u {
        ModulePath.mp ids =>
            match ids {
                List.empty => Option.none,
                List.cons hd rest =>
                    match rest {
                        List.empty => Option.none,
                        List.cons _ _ => Option.some (identifier_to_string hd)
                    }
            }
    }

def undeclared_mote_error (m : MoteManifest) (info : ModuleInfo) (u : ModulePath) (head : String) : String :=
    String.concat "error: mote `" (String.concat head
    (String.concat "` is not a declared dependency of `" (String.concat m.name
    (String.concat "`\n  `use " (String.concat (module_path_to_string u)
    (String.concat "` in " (String.concat info.file_path
    (String.concat " requires mote `" (String.concat head
    (String.concat "`\n  hint: add [dependencies." (String.concat head
    (String.concat "] path = \"../" (String.concat head
    (String.concat "\" to " (String.concat m.dir "/mote.toml")))))))))))))))

/// Turn the first undeclared-mote error, if any, into the load's own
/// failure. One error, not all of them: the loader's `Result` carries a
/// single message, and the first one names a real manifest fix.
#[partial]
def gate_declared_deps (r : Result String LoadedModules) : IO (Result String LoadedModules) := do {
    match r {
        Result.err e => return (Result.err e),
        Result.ok loaded => do {
            let errs : List String <- validate_declared_deps (get_loaded_all loaded);
            match errs {
                List.empty => return (Result.ok loaded),
                List.cons e _ => return (Result.err e)
            }
        }
    }
}

// --- Native link libraries (package-system.md 2a, `[link] libs`) -----

/// The C libraries a whole program links against: the union of every
/// loaded module's mote's `[link] libs`, deduplicated, first-declared
/// order preserved.
///
/// Collected over the DEPENDENCY CLOSURE, not just the root mote: if a
/// mote you depend on calls into libm, your binary needs `-lm`, and you
/// should not have to restate that mote's build details in your own
/// manifest. The loaded set already IS the closure, so walking it is all
/// that is needed.
///
/// This is why `#[extern "c"]` carries no `lib := "..."`. Which C symbol
/// a def binds to is a property of the declaration (`link_name`); what
/// the linker is handed is a property of the package, and belongs in the
/// manifest the same way Cargo keeps `-l` flags out of `extern "C"`.
#[partial]
pub def collect_link_libs (infos : List ModuleInfo) : IO (List String) := do {
    let all : List String <- link_libs_of_modules infos;
    return (dedup_link_libs all List.empty)
}

#[partial]
def link_libs_of_modules (infos : List ModuleInfo) : IO (List String) :=
    match infos {
        List.empty => do { return List.empty },
        List.cons info rest => do {
            let here : List String <- link_libs_of_module info;
            let later : List String <- link_libs_of_modules rest;
            return (List.append here later)
        }
    }

#[partial]
def link_libs_of_module (info : ModuleInfo) : IO (List String) := do {
    // `mote_of_module`, not `Mote.discover`: an inline `#![mote { libs :=
    // [...] }]` declares the same `[link] libs` a manifest does, so a file
    // with no `mote.toml` must still reach the linker's flags through it.
    let mote : Option MoteManifest <- mote_of_module info;
    match mote {
        Option.none => return List.empty,
        Option.some m => return m.link_libs
    }
}

/// Order-preserving dedup. `seen` accumulates in reverse, but membership
/// is all it is used for, so the order that matters -- the output's -- is
/// the order of first declaration.
#[partial]
def dedup_link_libs (xs : List String) (seen : List String) : List String :=
    match xs {
        List.empty => List.empty,
        List.cons hd tl =>
            if link_lib_seen hd seen
            then dedup_link_libs tl seen
            else List.cons hd (dedup_link_libs tl (List.cons hd seen))
    }

#[partial]
def link_lib_seen (needle : String) (xs : List String) : Bool :=
    match xs {
        List.empty => false,
        List.cons hd tl => if String.beq hd needle then true else link_lib_seen needle tl
    }

/// `cache` carries `ModuleInfo`s already loaded earlier in this same
/// run; the returned `LoadedAndCache` hands back the extended one so a
/// multi-file caller (`run_check_loop`) can reuse it for the next file.
/// Pass `module_info_cache_empty` for a standalone load.
///
/// `verbose` gates the per-module trace (`std/src/log.mo`): the target
/// module line here, and every dependency's line down in
/// `collect_dep_module_infos`. This used to print the target
/// unconditionally and nothing else -- the whole "only the main module
/// is printed" problem the trace exists to fix.
#[partial]
def load_file_modules_cached (file_path : String) (cache : ModuleInfoCache) (verbose : Bool) : IO LoadedAndCache {
    let base_dir : String := extract_directory file_path;
    let module_name : String := module_name_from_path file_path;
    let mp : ModulePath := ModulePath.mp [Identifier.id module_name];
    module_line verbose module_name;
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
                    // isn't in `cli/src/main.mo`'s own dependency closure
                    // (`lang.module` itself never `use`s `std.list`).
                    // Compiling `cli/src/main.mo` through itself then hits
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
                    let walked : InfosAndCache <- collect_dep_module_infos (pending_from main_base_dir direct_deps_with_prelude) no_visiting no_visited cache verbose;
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
            let out : LoadedAndCache := { loaded := Result.err ("Failed to load" ++ Show.show mp), cache := cache };
            return out
        }
    }
}

/// Backwards-compatible wrapper: a standalone load with a fresh cache.
/// Every caller that isn't threading a whole-run cache uses this.
/// `verbose` forwards to the per-module trace (`std/src/log.mo`).
#[partial]
pub def load_file_modules (file_path : String) (verbose : Bool) : IO (Result String LoadedModules) := do {
    let r : LoadedAndCache <- load_file_modules_cached file_path module_info_cache_empty verbose;
    return r.loaded
}

/// Report one elaboration sub-step's elapsed time and hand back a fresh
/// timestamp for the next one, so a chain of `let`s can be timed by
/// threading the return value through it. Silent (and still returns a
/// timestamp) when `verbose` is false.
///
/// `forced` is not read: it exists so the caller can pass something that
/// consumes the step's own result (a `List.length`, a count), which
/// guarantees the work happens INSIDE the span rather than at some later
/// use. The evaluator is strict call-by-value -- `core/src/core_eval.rs`'s
/// `App` arm reduces both sides before applying, and `let x := v in b`
/// desugars to `App(Lam b, v)` -- so a `let`-bound step is already forced
/// where it is bound and `forced` is belt-and-braces. AGENTS.md item 25
/// claims the opposite ("the language is lazy", so a `Bench.report`
/// around a `let` measures nothing); whatever caused that measurement to
/// print nothing, laziness is not it. The check that matters either way
/// is arithmetic: these sub-times must add up to the enclosing
/// `elaborate_loaded_modules` total that `cli/src/main.mo` already prints.
/// If they do not, the spans are wrong -- do not reason about which.
#[partial]
pub def bench_step (verbose : Bool) (label : String) (t0 : I64) (forced : I64) : IO I64 :=
    if verbose then do {
        // `timing_line` (std/src/log.mo): the same "<label> <ms>ms" content
        // `Bench.report_since` printed, dim-colored so the sub-times
        // group visually under their `stage` line.
        timing_line label t0;
        Bench.now
    } else Bench.now

// --- elaborate_loaded_modules: THE unified check/compile/test front end ---
//
// `check` (via `check_file_cached`), `compile`/`test` (via `cli/src/main.mo`'s
// `compile_file`/test-loop, `lang/codegen/emit.mo`/`test_driver.mo`), and
// `slow_tests` used to each hand-roll their own version of this pipeline,
// independently, and had quietly drifted apart -- `check` seeded prelude/
// init and resolved infixes, `slow_tests`' own `load_module_with_dependencies`
// didn't; `compile`/`test` ran `promote_instance_defs`/
// `add_constraint_dict_params_decls` (dictionary-passing setup) but never
// type-checked anything; `check`/`slow_tests` type-checked but never ran
// dictionary-passing setup at all. `elaborate_loaded_modules` is the one
// canonical version, used identically by all of them from here on.
pub struct ElaboratedModules {
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

pub struct ElaboratedAndCache {
    elaborated : Result String ElaboratedModules,
    cache : ModuleInfoCache,
}

/// A trivial local flatten of every loaded module's own decls into one
/// list -- mirrors `lang.codegen.emit`'s own `collect_all_decls_from_modules`
/// exactly, but can't be imported from there: `lang.codegen.emit` already
/// `use`s `lang.module` (for `get_loaded_all`/`get_loaded_main`/
/// `.decl_list`/`try_parse_decls`), so importing back would be
/// a module cycle. Same dodge as `lang.typecheck.infer`'s own documented
/// small-helper duplications elsewhere in this codebase.
#[partial]
def flatten_module_decls (modules : List ModuleInfo) (acc : List Decl) : List Decl :=
    match modules {
        List.empty => acc,
        List.cons mod_ rest =>
            flatten_module_decls rest (list_append (mod_.decl_list) acc),
    }

/// `flatten_module_decls`' grouped twin -- the same modules in the same
/// order, but each module's decls kept as their own `DeclGroup`, so the
/// scope builder can still say which module owns a def.
///
/// Order is preserved exactly, which is load-bearing: the flat version
/// folds each module's decls onto the FRONT of the accumulator, so its
/// result is the modules in REVERSE load order with each module's own
/// decls in order. Prepending one group per module reproduces that, and
/// `decl_groups_flatten` (`lang/scope.mo`) of the result is the very list
/// `flatten_module_decls` returns.
#[partial]
def flatten_module_decl_groups (modules : List ModuleInfo) (acc : List DeclGroup) : List DeclGroup :=
    match modules {
        List.empty => acc,
        List.cons mod_ rest =>
            flatten_module_decl_groups rest (List.cons (DeclGroup.mk mod_.path mod_.decl_list) acc),
    }

/// `flatten_module_decls`, minus every `priv` declaration belonging to a
/// module other than `target`.
///
/// This is where `priv` is actually enforced for a real `check`/`compile`.
/// The scope builder has its own filter (`scope_def_visible_to`,
/// lang/src/scope.mo) but only on the `build_scope_from_modules` path,
/// which the pipeline does not take. It could do the job here now that
/// the grouped flatten carries each decl's owning module through
/// (`flatten_visible_module_decl_groups`), and `scope_def_visible_to`
/// reads exactly that -- but moving it would change the `check_deps` case,
/// where one shared scope deliberately shows a dependency its own
/// internals, so the filter stays at the flatten.
///
/// Two consequences worth knowing before changing this:
///
///   - It is skipped when `check_deps` is on (see the call site). One
///     shared scope cannot hide a module's internals from others AND show
///     them to itself, and checking a dependency's bodies needs the latter.
///   - CODEGEN does not go through it: `compile_loaded_modules_to_ir_with_debug`
///     re-flattens from `loaded`. That is deliberate -- `priv` is a scoping
///     rule, not a linking one, so a `pub` def calling its own `priv` helper
///     must still compile. Do not "fix" codegen to match.
#[partial]
def flatten_visible_module_decls (target : ModulePath) (modules : List ModuleInfo) (acc : List Decl) : List Decl :=
    match modules {
        List.empty => acc,
        List.cons mod_ rest =>
            let visible : List Decl :=
                if String.beq (show_module_path mod_.path) (show_module_path target)
                then mod_.decl_list
                else drop_priv_decls mod_.decl_list in
            flatten_visible_module_decls target rest (list_append visible acc),
    }

/// `flatten_visible_module_decls`' grouped twin -- the same `priv` rule
/// applied to the same modules in the same order, with each module's
/// visible decls kept as their own `DeclGroup`. See
/// `flatten_module_decl_groups` for why the order is preserved by
/// prepending one group per module.
#[partial]
def flatten_visible_module_decl_groups (target : ModulePath) (modules : List ModuleInfo) (acc : List DeclGroup) : List DeclGroup :=
    match modules {
        List.empty => acc,
        List.cons mod_ rest =>
            let visible : List Decl :=
                if String.beq (show_module_path mod_.path) (show_module_path target)
                then mod_.decl_list
                else drop_priv_decls mod_.decl_list in
            flatten_visible_module_decl_groups target rest (List.cons (DeclGroup.mk mod_.path visible) acc),
    }

#[partial]
def drop_priv_decls (decls : List Decl) : List Decl :=
    match decls {
        List.empty => List.empty,
        List.cons d rest =>
            if decl_is_priv d
            then drop_priv_decls rest
            else List.cons d (drop_priv_decls rest)
    }

/// Visibility lives on the declaration itself for defs, types, structs,
/// classes and instances; constructors and methods inherit the visibility
/// of the block that declares them, so dropping the block drops them too.
def decl_is_priv (d : Decl) : Bool :=
    match d {
        Decl.def_d df => visibility_beq df.vis Visibility.priv_,
        Decl.inductive_d ind => visibility_beq ind.vis Visibility.priv_,
        Decl.struct_d s => visibility_beq s.vis Visibility.priv_,
        Decl.class_d c => visibility_beq c.vis Visibility.priv_,
        Decl.instance_d i => visibility_beq i.vis Visibility.priv_,
        _ => false
    }

// --- Tests: priv filtering at the flatten ---

def priv_module_info : ModuleInfo :=
    let owner : ModulePath := ModulePath.mp [Identifier.id "Owner"] in
    let hidden : Def := Def.mk (NamePath.npath [Identifier.id "hidden"]) Term.hole Term.hole
        ([] : List TypeConstraint) ([] : List Attribute) Visibility.priv_ List.empty in
    let shown : Def := Def.mk (NamePath.npath [Identifier.id "shown"]) Term.hole Term.hole
        ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private List.empty in
    { path := owner,
      file_path := "Owner.mo",
      decl_list := [Decl.def_d hidden, Decl.def_d shown] }

def priv_flatten_names (target : ModulePath) : List String :=
    List.map (fn (d : Decl) => show_name_path (Decl.to_name d))
        (flatten_visible_module_decls target [priv_module_info] List.empty)

#[test]
def test_flatten_drops_priv_from_other_modules : Bool :=
    let names : List String := priv_flatten_names (ModulePath.mp [Identifier.id "Other"]) in
    if List.any (fn (n : String) => String.beq n "shown") names
    then not (List.any (fn (n : String) => String.beq n "hidden") names)
    else false

#[test]
def test_flatten_keeps_priv_in_its_own_module : Bool :=
    let names : List String := priv_flatten_names (ModulePath.mp [Identifier.id "Owner"]) in
    List.any (fn (n : String) => String.beq n "hidden") names

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

/// One decl -> the decl plus everything it generates: `decl_gen_subst_one`
/// (the decl itself, or a written macro call's own expansion), then
/// `derive_bridge_decls` (`#[derive ...]`/`#[derive_cli]` on a type
/// declaration, expanded into the `derive_*! <T>` call the user could
/// have written — see `macro_queue.mo`'s own section note for the whole
/// mechanism). Order is the reference's own: the type declaration first,
/// its generated instances/lenses after it.
///
/// The bridge belongs HERE and not in `macro_queue.mo`'s per-file
/// `expand_decls`, which `parse_all_decls` runs at parse time: this
/// function is the whole-graph pass, run once per elaboration, and the
/// bridge is deliberately not idempotent (a type keeps its attributes —
/// see the reference's own reason for never re-queueing the type). A
/// second pass would generate every instance twice.
#[partial]
def decl_gen_subst_decls (registry : List DeclGenEntry) (decls : List Decl) : List Decl :=
    match decls {
        List.empty => List.empty,
        List.cons d rest =>
            list_append (decl_gen_subst_one registry d)
                (list_append (derive_bridge_decls registry d) (decl_gen_subst_decls registry rest)),
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
                                                            match meta_eval_invoke dispatched (NamePath.npath (List.cons (Identifier.id meta_name) List.empty)) type_info_v {
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
///
/// Three decl lists, because there are three consumers and they need the
/// expansion in two DIFFERENT shapes.
///
/// `graph` (whole dependency graph) and `target` (the target's own
/// decls) are the PREPARED lists -- the same infix/promote/dict-param
/// form `dict_paramed` is in -- so the caller can rebuild its `Scope`
/// from them and type-check against it. `raw_target` is the same
/// expansion applied to the target's own RAW decl list (the
/// `main_module.decl_list` the parser produced), and it exists because
/// the CODEGEN paths do not consume a prepared list at all: both
/// `lang.codegen.emit`'s `compile_loaded_modules_to_ir` and
/// `lang.codegen.test_driver`'s `compile_loaded_modules_to_test_ir` take
/// `LoadedModules` and run the elaboration passes THEMSELVES, over each
/// module's own raw `decl_list` (`qualify_modules` first, so a generated
/// decl's bare names -- `String.concat`, `Lens`, the `Point.x` lens's
/// own `lens` -- get the same module qualification every parsed decl
/// gets). Handing them an already-prepared list is NOT an option:
/// `promote_instance_defs` APPENDS the promoted defs to the list it is
/// given, so running the passes over their own output duplicates every
/// instance method and dictionary value. A generated decl is not a
/// prepared decl, so it has to enter the pipeline at the same place a
/// parsed one does -- which is what `raw_target` is for.
///
/// `raw_target` covers the MAIN module only. A derive in a DEPENDENCY
/// module still reaches `graph`/`target` (and so the checker) but not the
/// codegen paths, which read each module's own `decl_list`; no corpus
/// file derives into a dependency, and the fix for that case is the same
/// "codegen consumes the prepared whole graph" step `elaborate_loaded_
/// modules`'s own doc comment calls Stage 3, not a fourth list here.
pub struct GraphExpansion {
    graph : List Decl,
    target : List Decl,
    /// The SAME expansion as `target`, applied to the target's own RAW
    /// (pre-elaboration) decl list instead of its prepared one -- see
    /// `expand_decls_graph`'s own doc comment for why the codegen
    /// pipeline needs this third form.
    raw_target : List Decl,
    changed : Bool,
    /// Whether `raw_target` actually differs from the raw list handed in.
    /// The caller patches the MAIN module's own `decl_list` only when it
    /// does, so a file that expands nothing keeps the exact list it
    /// loaded (and `loaded` is a pure value the caller may keep sharing).
    raw_changed : Bool,
}

def expand_decls_graph (scope : Scope) (whole_graph_decls : List Decl) (target : List Decl) (raw_target : List Decl) : Result String GraphExpansion :=
    let registry : List DeclGenEntry := build_decl_gen_registry whole_graph_decls in
    let graph_subst : List Decl := decl_gen_subst_decls registry whole_graph_decls in
    let target_subst : List Decl := decl_gen_subst_decls registry target in
    let raw_subst : List Decl := decl_gen_subst_decls registry raw_target in
    let substituted : Bool :=
        has_decl_gen_expansion registry whole_graph_decls || has_decl_gen_expansion registry target in
    // `raw_changed`: a registered decl-gen call anywhere in the RAW target
    // (its body may or may not contain a `reflect_type_info!`), or a
    // `reflect_type_info!` call left in the substituted raw target. Both
    // mean the raw list gains decls, so the main module's own `decl_list`
    // must be replaced with `raw_target`.
    let raw_changed : Bool :=
        has_decl_gen_expansion registry raw_target || has_reflect_type_info_call raw_subst in
    if has_reflect_type_info_call graph_subst || has_reflect_type_info_call target_subst || has_reflect_type_info_call raw_subst then
        let inds : List Inductive := collect_inductives whole_graph_decls in
        let empty_locs : LocalScope := { vars := List.empty, parent := Option.none } in
        // `dispatched` is the expansion ENVIRONMENT, not the graph that
        // gets checked or compiled: it is what `resolve_one_reflect_call`
        // evaluates the named meta-def against (`meta_eval_invoke`), so it
        // has to be resolvable for real execution.
        //
        // A whole-graph `validate_no_unresolved_class_calls` used to run
        // here, on this same list, as a fail-fast. It cannot survive
        // derives: a file that derives (`p1 == p2` over a `#[derive BEq]`
        // type) legitimately has an unresolvable `BEq.beq` call in it at
        // this point -- the instance the derive is about to generate does
        // not exist yet, and once it does it is a RAW decl awaiting the
        // codegen pipeline's own promotion pass, so no resolution of a
        // prepared list can see it either. The check now lives where the
        // resolution actually happens, over the decls the run will really
        // use: `lang.codegen.emit`'s and `lang.codegen.test_driver`'s own
        // `validate_no_unresolved_class_calls` on the reachable closure of
        // the fully-prepared graph. Nothing narrows for a non-derive file:
        // this validation only ever ran when a `reflect_type_info!` call
        // was present in the graph, and the downstream gate runs the same
        // check unconditionally.
        let dispatched := resolve_class_calls_decls (elaborate_module_decls_best_effort scope whole_graph_decls empty_locs) in
        match resolve_reflect_calls inds dispatched graph_subst {
            Result.err e => Result.err e,
            Result.ok graph_final =>
                match resolve_reflect_calls inds dispatched target_subst {
                    Result.err e => Result.err e,
                    // This branch always rewrites at least the
                    // `reflect_type_info!` call it just resolved.
                    Result.ok target_final =>
                        match resolve_reflect_calls inds dispatched raw_subst {
                            Result.err e => Result.err e,
                            Result.ok raw_final =>
                                let expanded : GraphExpansion :=
                                    { graph := graph_final, target := target_final, raw_target := raw_final, changed := true, raw_changed := raw_changed } in
                                Result.ok expanded,
                        },
                },
        }
    else
        let unexpanded : GraphExpansion :=
            { graph := graph_subst, target := target_subst, raw_target := raw_subst, changed := substituted, raw_changed := raw_changed } in
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
///   - `true`: the fully-prepared WHOLE-GRAPH decl list (`dict_paramed_flat`,
///     already computed below for `scope`/`elaborated_decls` -- reused
///     directly here, no second pass needed) -- every dependency's own
///     declarations get body-checked too, not just scoped. Slower
///     (checks everything reachable, once per call), but the check
///     actually named "check"/"compile"/"test" should mean: verifying a
///     file also verifies what it depends on.
/// The post-expansion scope, as its own def so the struct literal has a
/// declared return type to desugar against -- see the call site for why
/// neither an inline literal nor an annotated `let` inside the branch
/// works there.
#[partial]
def rebuild_target_scope (target_mp : ModulePath) (decls : List Decl) : Scope :=
    { module_id := target_mp, scope := build_scope_from_decls target_mp decls, parent := Option.none }

/// `loaded` with the MAIN module's own `decl_list` replaced by `decls` --
/// in both the `main_module` field and the matching entry of
/// `all_modules`. The two are separate lists and both have to agree:
/// test discovery and the `main`-rename step read `get_loaded_main`,
/// while everything that compiles reads `get_loaded_all`.
///
/// This is how decl-gen macro output (`#[derive ...]`'s generated
/// instances and lenses, `derive_beq! Point`'s) reaches the codegen
/// pipeline -- spliced into the module that wrote the macro call, in the
/// RAW form that pipeline expects. See `GraphExpansion`'s own doc
/// comment for why the prepared form is not an alternative.
#[partial]
def replace_module_decls (target_mp : ModulePath) (decls : List Decl) (mods : List ModuleInfo) : List ModuleInfo :=
    match mods {
        List.empty => List.empty,
        List.cons m rest =>
            // The choice is made in the DECL LIST, not by returning one
            // struct literal or the other from an `if` -- a bare struct
            // literal in `if`-branch position has no expected type to
            // desugar against (see `AGENTS.md`), and `ModuleInfo.mk`'s
            // first field is a `ModulePath`, so the wrong arm would not
            // even type-check.
            let chosen : List Decl := if modpath_eq m.path target_mp then decls else m.decl_list in
            let m2 : ModuleInfo := ModuleInfo.mk m.path m.file_path chosen in
            List.cons m2 (replace_module_decls target_mp decls rest)
    }

#[partial]
def replace_main_decls (loaded : LoadedModules) (target_mp : ModulePath) (decls : List Decl) : LoadedModules :=
    match loaded {
        LoadedModules.mk main all =>
            let new_main : ModuleInfo := ModuleInfo.mk main.path main.file_path decls in
            let new_all : List ModuleInfo := replace_module_decls target_mp decls all in
            LoadedModules.mk new_main new_all
    }

#[partial]
pub def elaborate_loaded_modules_cached (file_path : String) (check_deps : Bool) (cache : ModuleInfoCache) (verbose : Bool) : IO ElaboratedAndCache := do {
    let t_load : I64 <- Bench.now;
    let lc : LoadedAndCache <- load_file_modules_cached file_path cache verbose;
    // Declared-dependency enforcement (package-system.md 5d) before any
    // elaboration work: a mote reaching into one it never declared is a
    // manifest error, and saying so beats letting it surface as whatever
    // name happens to go missing first.
    let loaded_result : Result String LoadedModules <- gate_declared_deps lc.loaded;
    let out_cache : ModuleInfoCache := lc.cache;
    let _t_load_done : I64 <- bench_step verbose "  elab: load_file_modules (read+parse)" t_load 0;
    // Annotated local, never a bare literal in `return` position -- see
    // the identical note in `collect_dep_module_infos` above.
    let elaborated_result : Result String ElaboratedModules <- match loaded_result {
        Result.err e => return (Result.err e),
        Result.ok loaded => do {
            let t0 : I64 <- Bench.now;
            // `priv` declarations from OTHER modules are dropped here --
            // see `flatten_visible_module_decls` for why the filter lives
            // at the flatten rather than in the scope builder.
            //
            // Only when `check_deps` is off, which is every real
            // `check`/`compile`. This list is ONE scope, shared by the
            // target and by every dependency whose bodies are being
            // checked -- so with `check_deps` on, dropping a dependency's
            // `priv` helper would hide it from that dependency's own `pub`
            // defs, enforcing the rule against the module allowed to break
            // it. Per-consumer resolution is what would do both;
            // visibility-declarations.md tracks it.
            let target_module : ModuleInfo := get_loaded_main loaded;
            let target_path : ModulePath := target_module.path;
            // GROUPS, not a flat list: each group carries its own module's
            // path, so the scope built below registers every dependency def
            // under the module that OWNS it. That is what makes a
            // cross-module qualified reference resolvable -- see
            // `build_scope_from_groups` (`lang/scope.mo`) for why one path
            // for the whole list cannot work.
            let decl_groups : List DeclGroup :=
                if check_deps
                then flatten_module_decl_groups (get_loaded_all loaded) List.empty
                else flatten_visible_module_decl_groups target_path (get_loaded_all loaded) List.empty;
            let all_decls : List Decl := decl_groups_flatten decl_groups;
            let t_flat : I64 <- bench_step verbose "  elab: flatten_module_decls" t0 (List.length all_decls);
            let infixes : List Infix := collect_infixes all_decls;
            let t_collect : I64 <- bench_step verbose "  elab: collect_infixes" t_flat (List.length infixes);
            let resolved : List DeclGroup := resolve_infix_decl_groups infixes decl_groups;
            let t_infix : I64 <- bench_step verbose "  elab: resolve_infix_decls" t_collect (List.length (decl_groups_flatten resolved));
            let promoted : List DeclGroup := promote_instance_decl_groups resolved;
            let t_promote : I64 <- bench_step verbose "  elab: promote_instance_defs" t_infix (List.length (decl_groups_flatten promoted));
            let dict_paramed : List DeclGroup := add_constraint_dict_params_decl_groups promoted;
            let t_dict : I64 <- bench_step verbose "  elab: add_constraint_dict_params_decls" t_promote (List.length (decl_groups_flatten dict_paramed));
            // Everything after the scope is built from the FLAT view, not
            // the groups: `expand_decls_graph` and `target_decls_pre` both
            // take a `List Decl`, and codegen consumes the flat list too.
            // The grouping exists only to give the scope builder each
            // decl's owner.
            let dict_paramed_flat : List Decl := decl_groups_flatten dict_paramed;
            let main_module : ModuleInfo := get_loaded_main loaded;
            let target_mp : ModulePath := main_module.path;
            let scope_data : ScopeData := build_scope_from_groups dict_paramed;
            let t_scope : I64 <- bench_step verbose "  elab: build_scope_from_decls" t_dict (List.length scope_data.classes);
            let scope : Scope := { module_id := target_mp, scope := scope_data, parent := Option.none };
            // `target_decls` must go through the SAME infix-resolution/
            // promotion/dict-param passes as the whole graph above -- the
            // raw `main_module.decl_list` still has bare
            // placeholder operator vars (`Term.var (DebugName.named "+")`
            // etc, from the self-hosted parser -- see `resolve_infix_
            // decls`'s own doc comment, `lang/scope.mo`), which `scope`
            // (built from the ALREADY-resolved whole graph) has no entry
            // for under that literal name, only under `HAdd.add` --
            // checking the raw decls against the resolved scope produced
            // a bogus `unknown variable '+'` before this fix. When
            // `check_deps` is true, `dict_paramed_flat` already IS that
            // fully-resolved list, for the whole graph (main module's own
            // decls included -- `all_decls`/`flatten_module_decls` folds;
            // `main_module` too, see `load_file_modules`), so reuse it
            // directly instead of redundantly re-running the same three
            // passes on just the main module's own raw decls again.
            let target_decls_raw : List Decl := main_module.decl_list;
            let target_decls_pre : List Decl :=
                if check_deps then
                    dict_paramed_flat
                else
                    add_constraint_dict_params_decls (promote_instance_defs (resolve_infix_decls infixes target_decls_raw));
            let t_target : I64 <- bench_step verbose "  elab: target-only re-run of the same 3 passes" t_scope (List.length target_decls_pre);
            // Forall-wrap each target def's type with its free + constraint-
            // only type vars (`elaborate_def_typs`), using the whole-graph
            // name set so globals aren't wrapped. `known_names` comes from
            // `dict_paramed_flat` (the fully-prepared whole-graph list) -- a
            // target-only `names_of_decls` would miss dependency globals and
            // wrongly Forall-wrap them. This re-introduces the implicit
            // type vars the parser deliberately dropped (e.g. `F`;
            // `def Lens [Functor F] {F : ...} ...`); `locals_with_def_typevars`
            // then skolemizes them from the resulting `Forall` chain.
            // Whole-graph macro/intrinsic expansion (`reflect_type_info!`)
            // -- see `expand_decls_graph`'s own doc comment. A no-op for
            // any file that never (transitively) invokes
            // `reflect_type_info!`, so safe to run unconditionally.
            let expansion_result : Result String GraphExpansion := expand_decls_graph scope dict_paramed_flat target_decls_pre target_decls_raw;
            let t_expand : I64 <- bench_step verbose "  elab: expand_decls_graph" t_target 0;
            match expansion_result {
                Result.err e => return (Result.err e),
                Result.ok expansion => do {
                    let dict_paramed2 : List Decl := expansion.graph;
                    let target_decls_pre2 : List Decl := expansion.target;
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
                    // The literal needs its OWN annotated binding: a
                    // `let x : T := if c then { ... } else y` annotation
                    // does not reach into the branch, so the bare literal
                    // there gets no expected type, never desugars, and
                    // survives to codegen as a `Literal.struct_lit` (see
                    // `validate_no_undesugared_struct_lits`). It also made
                    // this whole def fail to elaborate ("expected Bool,
                    // found Type"), which -- because codegen elaboration
                    // is best-effort -- silently left the ENTIRE body
                    // unelaborated.
                    // The rebuild is INSIDE the branch, not bound by a `let`
                    // above it. This evaluator is strict (AGENTS.md item 25),
                    // so `let rebuilt_scope := build_scope_from_decls ...`
                    // ran the rebuild unconditionally and the `if` only chose
                    // which already-computed scope to keep. `if` is the one
                    // form that does not evaluate the branch it does not take,
                    // so this is what makes the guard real.
                    //
                    // It was not a small waste: `build_scope_from_decls` is
                    // the single most expensive phase, and a self-hosted
                    // `check cli/src/main.mo` spent 83.9s of 232s here -- 36% of
                    // the run -- duplicating the 81.9s the first build had
                    // already done, for a graph that had not changed.
                    // The annotated local moves INSIDE the branch rather
                    // than being dropped. It was load-bearing twice over:
                    // outside the branch it forced the rebuild eagerly (the
                    // bug above), but the literal also needs an expected type
                    // to desugar against, and a bare `{ ... }` in the branch
                    // has none -- it survives to codegen as a
                    // `Literal.struct_lit` and compiles to a void
                    // placeholder, which `validate_no_undesugared_struct_lits`
                    // rejects. An annotated `let ... in` INSIDE the branch
                    // does not help either: the annotation does not reach the
                    // literal from there.
                    //
                    // `rebuild_target_scope`'s declared return type is what
                    // gives it one, and calling it inside the branch keeps the
                    // laziness. Same shape the rest of the codebase uses when
                    // a literal needs a type it cannot get from its position.
                    // `did_change` keeps its own annotated binding: the
                    // condition is a field access, and inlining it into the
                    // `if` is the other half of what made this def fail to
                    // elaborate as "expected Bool, found Type".
                    let did_change : Bool := expansion.changed;
                    let scope2 : Scope :=
                        if did_change
                        then rebuild_target_scope target_mp dict_paramed2
                        else scope;
                    // Timed separately from `names_of_decls` below: when
                    // `expansion.changed` this is a SECOND whole-graph
                    // `build_scope_from_decls` (~1500ms, per the note
                    // above), and folding it into the next span would
                    // silently attribute that to `names_of_decls`. The
                    // arithmetic self-check (AGENTS.md item 25) cannot
                    // catch a mislabelled boundary -- the sub-times still
                    // sum to the total either way.
                    let t_scope2 : I64 <- bench_step verbose "  elab: post-expansion scope rebuild" t_expand (List.length scope2.scope.classes);
                    let known_names : List Identifier := names_of_decls dict_paramed2;
                    let t_names : I64 <- bench_step verbose "  elab: names_of_decls" t_scope2 (List.length known_names);
                    let target_decls : List Decl := elaborate_def_typs target_decls_pre2 known_names;
                    let _t_typs : I64 <- bench_step verbose "  elab: elaborate_def_typs" t_names (List.length target_decls);
                    // Hand the CODEGEN pipeline the expansion too: the
                    // generated decls go into the main module's own RAW
                    // `decl_list`, so both codegen paths (which run the
                    // elaboration passes themselves, over exactly that
                    // list) pick them up the same way they pick up a
                    // parsed decl -- see `GraphExpansion`'s own doc
                    // comment for why the prepared list is the wrong shape
                    // to hand them.
                    let raw_changed : Bool := expansion.raw_changed;
                    let loaded2 : LoadedModules :=
                        if raw_changed
                        then replace_main_decls loaded target_mp expansion.raw_target
                        else loaded;
                    // Annotated local, not an inline literal --
                    // see `load_module_with_info`'s own note.
                    let elaborated : ElaboratedModules :=
                        { scope := scope2, target_decls := target_decls, elaborated_decls := dict_paramed2, loaded := loaded2 };
                    return (Result.ok elaborated)
                },
            }
        },
    };
    let out : ElaboratedAndCache := { elaborated := elaborated_result, cache := out_cache };
    return out
}

/// Backwards-compatible wrapper: elaborate with a fresh cache.
#[partial]
pub def elaborate_loaded_modules (file_path : String) (check_deps : Bool) (verbose : Bool) : IO (Result String ElaboratedModules) := do {
    let r : ElaboratedAndCache <- elaborate_loaded_modules_cached file_path check_deps module_info_cache_empty verbose;
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

// --- Tests: strict positivity ---
//
// Synthetic, because the corpus has none: `non-strictly` appears in no
// `.mo` file, and a scan of all 162 inductive declarations across the repo
// found 0 the rule flags. This closes a soundness gap, so the test is the
// only thing holding the rule in place -- the sweep cannot.

/// The diagnostics `check_module_with_scope` reports for `src`, checked as
/// a module called `module_name` with no locals in scope. Every test below
/// is a one-line source plus the verdict, so they share this.
def strict_pos_diags_of_source (src : String) (module_name : String) : IO (List String) := do {
    let path : ModulePath := ModulePath.mp (List.cons (Identifier.id module_name) List.empty);
    match parse_all_decls src {
        ParseResult.success _ decl_list => do {
            let sd : ScopeData := build_scope_from_decls path decl_list;
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            check_module_with_scope scope decl_list locals Option.none false
        },
        ParseResult.fail _ => do { return List.cons "PARSE FAILED" List.empty }
    }
}

#[partial]
def strict_pos_has_diag (needle : String) (diags : List String) : Bool :=
    match diags {
        List.empty => false,
        List.cons d rest => if String.contains d needle then true else strict_pos_has_diag needle rest,
    }

def strict_pos_lacks_diag (needle : String) (diags : List String) : Bool :=
    if strict_pos_has_diag needle diags then false else true

/// The rule's own case: a constructor field whose type is a function FROM
/// the type being declared. Rejected by the reference
/// (`target/release/monad-rs check` on exactly this source, 2026-09-23).
/// Asserting the message, not just non-emptiness, is what makes this fail if
/// the diagnostic's wording drifts away from `TypeError::Generic`'s.
#[test]
def test_check_module_strict_pos_rejects_negative_self : IO Bool := do {
    let diags : List String <- strict_pos_diags_of_source "type Bad { mkBad (f : Bad -> I64) }" "probe";
    return (strict_pos_has_diag "non-strictly positive occurrence of Bad" diags && I64.beq (List.length diags) 1)
}

/// Recursion in the codomain, one constructor field per shape: a direct
/// field, an arrow whose RESULT is the type, and an arrow whose DOMAIN is
/// itself an arrow (two flips, so positive). All three are accepted by the
/// reference on the same source.
#[test]
def test_check_module_strict_pos_accepts_positive_self : IO Bool := do {
    let src : String := "type Tree { leaf (n : I64), node (l : Tree) (r : Tree) }\ntype Fwd { mkFwd (k : I64 -> Fwd) }\ntype Neg { mkNeg (h : (Neg -> I64) -> I64) }";
    let diags : List String <- strict_pos_diags_of_source src "probe";
    return (I64.beq (List.length diags) 0)
}

/// The module half of a qualified reference, both directions. `probe::Q` IS
/// this module's `Q` and is rejected; `other::Q` is not, and is accepted
/// even though its name half matches. The reference was measured producing
/// exactly this split for this pair of spellings, and it is the reason its
/// own comparison is not name-half-only: the same source checked as a
/// different module gets the other verdict.
#[test]
def test_check_module_strict_pos_qualified_self_is_this_module : IO Bool := do {
    let diags : List String <- strict_pos_diags_of_source "type Q { mkQ (f : probe::Q -> I64) }" "probe";
    return (strict_pos_has_diag "non-strictly positive occurrence of Q" diags)
}

#[test]
def test_check_module_strict_pos_qualified_other_module_is_not : IO Bool := do {
    let diags : List String <- strict_pos_diags_of_source "type Q { mkQ (f : other::Q -> I64) }" "probe";
    return (strict_pos_lacks_diag "non-strictly positive occurrence" diags)
}

/// A dotted type name is compared whole -- the elaborator stores a bare
/// reference as the name's dotted `show_name_path` spelling, so `D.E` has to
/// match `D.E` and not just its last segment.
#[test]
def test_check_module_strict_pos_dotted_name : IO Bool := do {
    let diags : List String <- strict_pos_diags_of_source "type D.E { mkE (g : D.E -> I64) }" "probe";
    return (strict_pos_has_diag "non-strictly positive occurrence of D.E" diags)
}

/// A struct with the same shape is NOT flagged: the reference runs this for
/// `Decl::Type` only, and `check_decl_with_scope` routes a struct to
/// `check_struct_with_scope` instead. Without this the check would be one
/// `Decl.struct_d` arm away from over-rejecting, and nothing else says so.
#[test]
def test_check_module_strict_pos_skips_structs : IO Bool := do {
    let diags : List String <- strict_pos_diags_of_source "struct S { f : S -> I64 }" "probe";
    return (strict_pos_lacks_diag "non-strictly positive occurrence" diags)
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
    let empty_cache : ModuleInfoCache := module_info_cache_empty in
    match check_file_cached empty_cache "definitely/does/not/exist.mo" false {
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
                    String.beq (show_name_path df.name) "use_it" &&
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
                    String.beq (show_name_path df.name) "greet" &&
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
    // RESOLVED, not spelled out. `std/src/test.mo` is a CWD-relative
    // literal, so it named a file only from the checkout root and this test
    // failed when the file was tested from inside `lang/`. Going through the
    // resolver keeps the point -- a file with no `use` declarations of its
    // own still needs the modules its SIBLINGS provide -- and holds wherever
    // the working directory is.
    let resolved <- resolve_module_file "" std_test_module_path;
    match resolved {
        Option.none => return false,
        Option.some test_file => do {
            // Annotated bind -- `em.scope`/`em.target_decls` below desugar to
            // `{ .. }` field patterns, which need the matched value's own type.
            let result : Result String ElaboratedModules <- elaborate_loaded_modules test_file false false;
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
    }
}

// ─── Mote-root resolution ───────────────────────────────────────────
//
// Two defects made `monad check`/`monad test` from INSIDE a mote report a
// wall of "unknown variable" while the same file checked clean from the
// checkout root. Both are pinned here by their pure halves; the whole-mote
// case itself needs the CWD to change, which `std/src/io.mo` has no
// `set_current_dir` for, so it is verified by hand (see the Phase 9 notes).

/// A `mote.toml` body in this repo's own shape and spelling
/// (sub-table headers, not inline tables -- `lang/src/toml.mo` reads the
/// former).
def lang_manifest_fixture : String :=
  "[mote]\nname = \"lang\"\nversion = \"0.1.0\"\n\n[dependencies.init]\npath = \"../init\"\n\n[dependencies.std]\npath = \"../std\"\n\n[dependencies.llvm]\npath = \"../llvm\"\n"

/// One candidate, checked as a single-element list -- every
/// `mote_dep_files` case below yields exactly one.
def sole_candidate_is (xs : List String) (expected : String) : Bool :=
    match xs {
        List.cons x rest =>
            match rest {
                List.empty => String.beq x expected,
                List.cons _ _ => false,
            },
        List.empty => false,
    }

/// The `dir = ""` case -- a mote whose `mote.toml` IS the working
/// directory, which is every mote `Mote.discover` finds by walking up from
/// a relative path. `String.concat m.dir "/src"` gives `/src` here: an
/// ABSOLUTE path, so `mote_path_within` answers `use lang::x` with
/// `/src/x.mo` and misses every time. `raw_path_join`'s empty-component
/// rule is the fix, and it is the same rule the dependency paths already
/// follow (`test_manifest_reads_dependency_paths`, `Mote`'s own tests).
#[test]
def test_src_root_of_a_mote_at_the_working_directory : Bool :=
    match Mote.parse_manifest "" lang_manifest_fixture {
        Option.none => false,
        Option.some m => String.beq (MoteManifest.src_root m) "src"
    }

/// The named-directory case, which must not regress while fixing the above.
#[test]
def test_src_root_of_a_named_mote_dir : Bool :=
    match Mote.parse_manifest "lang" lang_manifest_fixture {
        Option.none => false,
        Option.some m => String.beq (MoteManifest.src_root m) "lang/src"
    }

/// `prelude` is the one module whose NAME is not its FILE name, and it
/// belongs to `init` -- which no mote declares as a dependency called
/// `prelude`. Without the special case, `dep_dir_of m "prelude"` is `none`
/// and the prelude is unreachable through the manifest at all, so a mote
/// loaded from inside its own directory never gets its prelude.
#[test]
def test_mote_dep_files_reaches_prelude_through_init : Bool :=
    match Mote.parse_manifest "" lang_manifest_fixture {
        Option.none => false,
        Option.some m =>
            sole_candidate_is (mote_dep_files m prelude_module_path) "../init/src/prelude.mo"
    }

/// A one-segment path means "that mote's own library root", the same rule
/// `mote_path_within` applies to the mote's own name.
#[test]
def test_mote_dep_files_bare_name_is_that_motes_lib : Bool :=
    match Mote.parse_manifest "" lang_manifest_fixture {
        Option.none => false,
        Option.some m =>
            sole_candidate_is (mote_dep_files m init_module_path) "../init/src/lib.mo"
            && sole_candidate_is (mote_dep_files m std_module_path) "../std/src/lib.mo"
    }

/// A qualified path names a file inside the dependency's `src/`.
#[test]
def test_mote_dep_files_qualified_path_names_the_dep_file : Bool :=
    match Mote.parse_manifest "" lang_manifest_fixture {
        Option.none => false,
        Option.some m =>
            sole_candidate_is
                (mote_dep_files m (ModulePath.mp [Identifier.id "std", Identifier.id "list"]))
                "../std/src/list.mo"
            && sole_candidate_is
                (mote_dep_files m (ModulePath.mp [Identifier.id "llvm", Identifier.id "ir"]))
                "../llvm/src/ir.mo"
    }

/// An undeclared mote contributes NOTHING, so the cascade's own answer
/// stands and the failure is the ordinary "module not found" rather than a
/// bogus manifest path.
#[test]
def test_mote_dep_files_is_empty_for_an_undeclared_mote : Bool :=
    match Mote.parse_manifest "" lang_manifest_fixture {
        Option.none => false,
        Option.some m => List.is_empty (mote_dep_files m (ModulePath.mp [Identifier.id "jsonschema", Identifier.id "schema"]))
    }

/// The prelude/init/std half: a CWD-relative candidate that MISSES must
/// fall through to the manifest rather than returning `none`.
///
/// This used to be three early returns of `first_existing [<cwd-relative
/// literal>]`, which never consulted `resolve_via_manifest` at all -- which
/// is why `monad check src/main.mo` from inside `cli/` reported a wall of
/// "unknown variable '++'" instead of loading its own prelude.
///
/// The candidate is deliberately bogus so the miss is forced; the manifest
/// half then reads the real `lang/mote.toml` and answers with the real
/// `init` path.
///
/// The answer is asserted to NAME `init`'s prelude and to be a file that
/// exists -- deliberately not to be one fixed string, because which string
/// it is is genuinely CWD-relative. From the checkout root the manifest's
/// join is `lang/../init/src/prelude.mo`, and `normalize_path` cancels the
/// `lang` segment, leaving `init/src/prelude.mo`: the very spelling the
/// cascade's own candidate for the prelude uses, so the two agree and
/// `dedup_modules_by_file` sees one file rather than two. From inside a
/// mote the dependency path is relative to that mote, so its leading `..`
/// survives (`../init/src/prelude.mo`). Pinning either spelling makes this
/// test pass in one working directory and fail in the other -- and it did
/// both, in that order. The property that has to hold everywhere is one
/// NORMALIZED spelling per file, and that is pinned by `normalize_path`'s
/// own tests below rather than by pinning a CWD's spelling here.
#[test]
def test_resolve_ambient_file_falls_through_to_the_manifest : IO Bool := do {
    let r <- resolve_ambient_file "lang/src" prelude_module_path "init/src/__no_such_module__.mo";
    match r {
        Option.none => return false,
        Option.some p => do {
            let exists <- file_exists (Path.path p);
            if exists then return (String.ends_with p "init/src/prelude.mo") else return false
        }
    }
}

/// ...and the fall-through must not invent an answer where there is none:
/// a miss below a path that is no mote stops the walk-up
/// (`Mote.discover_go` at `/`), so resolution reports the miss it had.
///
/// The directory is ABSOLUTE, and that is load-bearing rather than
/// cosmetic. `parent_of` reads the empty parent of a name with no separator
/// as the WORKING DIRECTORY, so a relative `__no_such_mote_dir__` walks up
/// into whatever mote the test is being run from and finds one: run from
/// inside `lang/`, this test answered with a path and failed for that
/// reason alone. An absolute path outside every mote walks to `/` and
/// stops, from any working directory.
#[test]
def test_resolve_ambient_file_miss_outside_any_mote_stays_a_miss : IO Bool := do {
    let r <- resolve_ambient_file "/__no_such_mote_dir__" prelude_module_path "init/src/__no_such_module__.mo";
    match r {
        Option.none => return true,
        Option.some _ => return false
    }
}

/// `init`'s own manifest, in its real shape: `std` as a DEV-dependency
/// and, being the pure core, nothing else -- least of all itself.
def init_self_manifest_fixture : String :=
  "[mote]\nname = \"init\"\nversion = \"0.1.0\"\n\n[dev-dependencies.std]\npath = \"../std\"\n"

/// The self-reference arm of `dep_dir_of`, and why it is load-bearing
/// rather than a convenience: `prelude` belongs to `init`
/// (`mote_dep_files` routes it there, since `prelude` is the one module
/// whose NAME is not its FILE name) and `init` is exactly the mote that
/// cannot declare itself as a dependency. Without it the prelude of the
/// mote `init` is unreachable from inside `init/` -- `dep_dir_of` is
/// `none`, `mote_dep_files` is empty, `prelude` never loads, and every
/// check reports its names as `unknown variable`.
///
/// The candidate is `src/prelude.mo`, for the mote whose `mote.toml` sits
/// at the working directory (`dir` is `""`), which is the `raw_path_join`
/// empty rule the rest of this section is already pinned on.
#[test]
def test_mote_dep_files_prelude_within_init_itself : Bool :=
    match Mote.parse_manifest "" init_self_manifest_fixture {
        Option.none => false,
        Option.some m =>
            sole_candidate_is (mote_dep_files m prelude_module_path) "src/prelude.mo"
    }

/// The same arm reached by the mote's own NAME rather than through the
/// `prelude` re-spelling: a bare `<mote>` means that mote's `src/lib.mo`,
/// so from inside `init/` its own lib root resolves to `src/lib.mo`.
#[test]
def test_mote_dep_files_own_name_within_itself : Bool :=
    match Mote.parse_manifest "" init_self_manifest_fixture {
        Option.none => false,
        Option.some m =>
            sole_candidate_is (mote_dep_files m init_module_path) "src/lib.mo"
    }

/// The loader is PATH-driven: hand it a file its module path could never
/// resolve to, and it still reads THAT file. This is the invariant
/// `load_module_with_info` relies on to resolve exactly once -- it records
/// the resolved path and then reads exactly that, where the old shape
/// handed the loader the resolved path's DIRECTORY and let it resolve a
/// second time, free to disagree with the first answer (see
/// `load_module_decls_at`'s own note for the `prelude`-inside-a-mote
/// defect that cost).
#[test]
def test_load_module_decls_at_reads_the_path_it_is_given : IO Bool := do {
    // Resolved rather than spelled out, for the plain reason that
    // `init/src/prelude.mo` is the CWD-relative spelling and so names a
    // file only from the checkout root. Resolving it first keeps the point
    // -- the LOADER is path-driven -- and holds from inside a mote too.
    let resolved <- resolve_module_file "" prelude_module_path;
    match resolved {
        Option.none => return false,
        Option.some p => do {
            let decls <- load_module_decls_at p (ModulePath.mp [Identifier.id "definitely_not_prelude"]);
            match decls {
                Option.none => return false,
                Option.some ds => return (I64.gt (List.length ds) 0)
            }
        }
    }
}

/// ...and the resolver-driven entry point still reads the prelude through
/// the ordinary cascade from the worktree root, so the split above did not
/// change the path everything already takes.
#[test]
def test_load_module_decls_still_resolves_then_reads : IO Bool := do {
    let decls <- load_module_decls "" prelude_module_path;
    match decls {
        Option.none => return false,
        Option.some ds => return (I64.gt (List.length ds) 0)
    }
}

/// `normalize_path`'s whole job: the two spellings of one file that
/// `dedup_modules_by_file` has to recognize as the same file. The first is
/// what `resolve_via_manifest` builds from inside a mote (`../lang` +
/// `../init` + `src/number.mo`), the second what the cascade answers from
/// the checkout root -- and they must not differ, because the dedup
/// compares them as strings.
#[test]
def test_normalize_path_collapses_the_manifest_join_to_the_cascade_spelling : Bool :=
    String.beq (normalize_path "../lang/../init/src/number.mo") "../init/src/number.mo"

/// The equality the qualification pass actually depends on, stated the way
/// it uses it rather than against a literal.
#[test]
def test_normalize_path_makes_both_spellings_of_one_file_agree : Bool :=
    String.beq (normalize_path "../lang/../init/src/number.mo")
               (normalize_path "../init/src/number.mo")

#[test]
def test_normalize_path_drops_a_leading_dot_segment : Bool :=
    String.beq (normalize_path "./src/main.mo") "src/main.mo"

#[test]
def test_normalize_path_collapses_repeated_separators : Bool :=
    String.beq (normalize_path "src//tests///main.mo") "src/tests/main.mo"

/// A leading `..` has nothing to cancel and must survive -- normalizing
/// `../init/src` to `init/src` would stop naming the file that was found.
#[test]
def test_normalize_path_keeps_a_leading_parent : Bool :=
    String.beq (normalize_path "../init/src") "../init/src"

#[test]
def test_normalize_path_keeps_every_leading_parent : Bool :=
    String.beq (normalize_path "../../std/src/list.mo") "../../std/src/list.mo"

/// `..` past the root of a relative path still cancels what precedes it,
/// and leaves the surplus: `a/../../b` is `../b`, not `b`.
#[test]
def test_normalize_path_keeps_a_parent_that_overshoots : Bool :=
    String.beq (normalize_path "a/../../b.mo") "../b.mo"

#[test]
def test_normalize_path_keeps_an_absolute_root : Bool :=
    String.beq (normalize_path "/a/../b.mo") "/b.mo"

#[test]
def test_normalize_path_is_idempotent : Bool :=
    String.beq (normalize_path (normalize_path "../lang/../init/src/number.mo")) "../init/src/number.mo"

