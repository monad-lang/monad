/// Module loading infrastructure for the self-hosted compiler.
/// Parses source text and builds scope data from declarations.

use std::io {}
use std::bench {Bench.now}
use std::process {exec_cmd, process_id}
use lib::elaborate {free_vars, names_of_decls, elaborate_def}
use lang::types {
  Attribute, Class, ClassDef, DebugName, Decl, DeclGroup, Def, Identifier,
  InductConstructor, Inductive, Infix, Instance, LocalScope, LocalVar, Location,
  ModulePath, NamePath, NameRef, Param, Scope, ScopeData, ScopeInstance, SourceRange,
  Struct, StructField, Term, TypeConstraint, TypeError, UseFilter, UseItem,
  binder_anon, binder_is_explicit, binder_is_level, binder_name, concrete,
  has_incomplete_match_exemption, id_eq,
  list_reverse, many, module_path_to_string_colon, package_private, priv_,
  show_identifier, show_module_path, show_name_path, term_peel, union_ids,
  use_bare, use_glob, use_items, use_name, use_rename, use_sub, use_sub_rename,
  visibility_beq,
}
use lib::parser {
  LocatedDecls, decls_parser, decls_parser_located, decls_parser_located_with_ranges,
  decls_parser_strict, module_path_to_string,
}
use parsec::core {ParseError, ParseResult}
use lib::parser::diagnostic {parse_error_location, render_parse_error}
use lang::mote {
  BinTarget, Mote.discover, Mote.manifest_at, Mote.manifest_of_attr, Mote.mote_attr_unknown_keys,
  Mote.parse_manifest, Mote.toolchain_candidates, Mote.toolchain_missing_hint,
  Mote.toolchain_root, Mote.workspace_members, MoteManifest,
}
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
use lib::typecheck::infer {empty_local_types, empty_locals, type_check}
// `--affine` (Phase 5 of the enforcement plan): the M2 usage rule as
// real diagnostics. Built once per module by the affine walk below,
// exactly how `affine.mo`'s own doc on `check_def` prescribes.
use lib::typecheck::usage {borrow_of_name_set, ctor_name_set}
use lib::typecheck::affine {check_def}
// `--verbose` per-module/per-stage trace (see `std/src/log.mo`'s own header
// for why the helpers gate themselves and why `bench_step` below prints
// through `timing_line`).
use std::log {module_line, timing_line}
use std::list {List.any, List.contains_by, List.intercalate, List.length, Show}
use std::show {Show}
// `ScopeData.def_refs` is a `std.map` `HashMap ModulePath ScopeDef` (see
// `lang/scope.mo`'s own `use std.map {}` doc comment for why the import
// is empty).
use std::map {HashMap, HashMap.merge_buckets}
// `Runtime.c_path` is the last tier of `resolve_runtime_src` below -- the
// checkout-root-relative literal, kept in the mote that owns the C file
// rather than repeated here.
use runtime {Runtime.c_path}

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

// --- Declaration ranges (what navigation reads) ---
//
// An outline, a go-to-definition and a hover all need one thing `Decl`
// cannot give them: where in the file a declaration is. `Term.ctx`'s own
// doc comment (`lang/types.mo`) rejects a location FIELD, and `Attribute`'s
// says "Deliberately has no `source_location`" -- the corpus convention is
// wrap or side-table, never a field. The parser's `ParseDecl` does carry a
// span per declaration, so the side table is read out of the parse here, in
// terms a consumer outside `lang/parser*` can name.

/// One top-level declaration's extent, with enough identity to be useful
/// as an outline entry.
///
/// The range's own `path` is `Option.none`: the parser is handed text, not
/// a filename. A consumer that knows the file -- a language server has the
/// URI -- fills it in.
pub struct DeclRange {
    name : String,
    kind : String,
    range : SourceRange,
}

// Every field read below is routed through a one-line typed accessor rather
// than written inline. A `#[test]` def that touches two fields of different
// types is the recorded self-hosted codegen hazard -- the def picks up one
// FIELD's LLVM type as its own return type -- and `lang/src/tests/
// decl_range_tests.mo` reads exactly these. Same remedy the five LSP probes
// in `lang/src/tests/unify_tests.mo` use.

pub def decl_range_name (dr : DeclRange) : String := dr.name

pub def decl_range_kind (dr : DeclRange) : String := dr.kind

pub def decl_range_span (dr : DeclRange) : SourceRange := dr.range

pub def located_decl_list (l : LocatedDecls) : List Decl := l.decl_list

pub def located_decl_spans (l : LocatedDecls) : List SourceRange := l.spans

// `Inductive`/`Struct`/`Class`/`Instance` have no name accessor of their
// own (`Def.name` is the only one, `lang/types.mo`), and `decl_name_and_kind`
// below needs four. Each is its own def for the reason just stated: one
// field read, one explicit return type, per def.

def inductive_decl_name (i : Inductive) : NamePath := i.name

def struct_decl_name (s : Struct) : Identifier := s.name

def class_decl_name (c : Class) : Identifier := c.name

def instance_decl_name (i : Instance) : Identifier := i.name

/// A declaration's display name and its kind, for an outline.
///
/// `Decl.to_name` cannot serve here: it answers "what does this DECLARE",
/// and returns the EMPTY name (`npath []`) for every kind but `def_d`, by
/// design. An outline wants the opposite -- something printable for every
/// kind, even when that is only the module a `use` names.
///
/// The kind strings are the Rust reference's own vocabulary ("def",
/// "type", "struct", "class", "instance"), so the wire output reads like
/// the tool being replaced rather than like this compiler's internals.
/// `use`/`open`/`mote` have no declaration-level name in that sense and are
/// named after what they name; both macro spellings report "defmacro"
/// because they are one concept to a reader.
#[partial]
def decl_name_and_kind (d : Decl) : Pair String String := match d {
    Decl.def_d df => Pair.pair (show_name_path (Def.name df)) "def",
    Decl.inductive_d i => Pair.pair (show_name_path (inductive_decl_name i)) "type",
    Decl.struct_d s => Pair.pair (show_identifier (struct_decl_name s)) "struct",
    Decl.class_d c => Pair.pair (show_identifier (class_decl_name c)) "class",
    Decl.instance_d i => Pair.pair (show_identifier (instance_decl_name i)) "instance",
    Decl.infix_d _op path _vis => Pair.pair (show_name_path path) "infix",
    Decl.use_d path _filter _public => Pair.pair (show_module_path path) "use",
    Decl.open_d path _filter => Pair.pair (show_name_path path) "open",
    Decl.scoped_open_d path _filter _decl => Pair.pair (show_name_path path) "open",
    Decl.def_macro_d df => Pair.pair (show_name_path (Def.name df)) "defmacro",
    Decl.decl_gen_d name _params _decl_list _attrs => Pair.pair (show_name_path name) "defmacro",
    Decl.macro_call_d name _args => Pair.pair (show_identifier name) "macro",
    Decl.mote_d _attr => Pair.pair "" "mote",
}

/// Every top-level declaration in `src`, with its name, kind and range.
///
/// `List.empty` on a parse failure. A caller that wants the failure itself
/// -- `check_file_cached_from_source_ranged` does -- parses separately
/// rather than reading it out of an empty list, because a parse error is
/// not a declaration range and pretending otherwise would make "clean
/// file" and "unparseable file" the same answer.
///
/// PRE-EXPANSION, deliberately: this is what the user wrote, not what a
/// macro generated. `parse_all_decls` runs `expand_decls` after lowering
/// and this does not.
#[partial]
pub def decl_ranges_of_source (src : String) : List DeclRange :=
    match decls_parser_located_with_ranges src {
        ParseResult.success _rem located => decl_ranges_of_located located,
        ParseResult.fail _e => List.empty,
    }

#[partial]
def decl_ranges_of_located (located : LocatedDecls) : List DeclRange :=
    zip_decl_ranges (located_decl_list located) (located_decl_spans located) List.empty

/// Pair each declaration with its range, one for one.
///
/// A SHORT `spans` list stops the walk and returns what it has, rather than
/// running off the end or mis-pairing the tail: a declaration with no range
/// is a visible absence, while a declaration with the NEXT one's range is a
/// silently wrong answer. `lang/src/tests/decl_range_tests.mo` pins the
/// count equality that makes this branch unreachable.
#[partial]
def zip_decl_ranges (ds : List Decl) (spans : List SourceRange) (acc : List DeclRange) : List DeclRange :=
    match ds {
        List.empty => list_reverse acc,
        List.cons d rest => match spans {
            List.empty => list_reverse acc,
            List.cons s srest => zip_decl_ranges rest srest (List.cons (mk_decl_range d s) acc),
        },
    }

#[partial]
def mk_decl_range (d : Decl) (range : SourceRange) : DeclRange :=
    match decl_name_and_kind d {
        Pair.pair n k => DeclRange.mk n k range,
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

/// `extract_use_decls`'s filter-preserving sibling: the same walk, but it
/// keeps the `UseFilter` instead of discarding it (`Decl.use_d path _ _`).
///
/// The mote-dependency checks above only ever ask WHICH modules a file
/// imports, so dropping the filter there is right. The name-resolution
/// check below asks which NAMES it imports, and cannot see a brace entry
/// through that extractor at all -- this is why it exists rather than a
/// second projection of the same list.
#[partial]
def extract_use_filters (decl_list : List Decl) : List (Pair ModulePath UseFilter) :=
    extract_use_filters_go decl_list List.empty

#[partial]
def extract_use_filters_go (decl_list : List Decl) (acc : List (Pair ModulePath UseFilter)) : List (Pair ModulePath UseFilter) :=
    match decl_list {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Decl.use_d path filter _ =>
                    extract_use_filters_go rest (List.cons (Pair.pair path filter) acc),
                _ => extract_use_filters_go rest acc
            }
    }

/// The name a declaration binds, as SOURCE spells it, or `Option.none` for
/// a declaration that binds none.
///
/// Every kind is covered, not just `def`s, because a brace list routinely
/// names types and classes -- `use init::io {IO}`, `use std::show {Show}`,
/// `use http::types {Request}` -- and a def-only walk would report every
/// one of those as unresolvable. Constructors count too: they are ordinary
/// scope entries (`add_constructors_as_defs`, `lang/scope.mo`), so
/// `use mod {Nil}` really does bind.
///
/// The rendering is what the comparison is against, so a DOTTED def comes
/// back as its dotted spelling (`List.intercalate`). That is the whole
/// point: a brace item is compared against the declaration's own spelled
/// name, and `use_brace_item_name_dotted` (`lang/parser.mo`) now parses a
/// dotted item, so `use std::list {intercalate}` is rejected while
/// `use std::list {List.intercalate}` binds.
def decl_local_name (d : Decl) : Option String :=
    match d {
        Decl.def_d dd => match dd { Def.mk {name, ..} => Option.some (show_name_path name) },
        Decl.def_macro_d dd => match dd { Def.mk {name, ..} => Option.some (show_name_path name) },
        Decl.inductive_d ind => match ind {
            Inductive.mk name _ _ constructors _ _ =>
                Option.some (show_name_path name)
        },
        Decl.struct_d st => match st { Struct.mk nm _ _ _ => Option.some (show_identifier nm) },
        Decl.class_d cls => match cls { Class.mk nm _ _ _ _ => Option.some (show_identifier nm) },
        Decl.instance_d ins => match ins { Instance.mk nm _ _ _ _ _ _ => Option.some (show_identifier nm) },
        Decl.decl_gen_d nm _ _ _ => Option.some (show_name_path nm),
        _ => Option.none
    }

/// Every name a module declares, including its inductives' constructors.
/// Order is declaration order, but nothing depends on it: the only
/// consumer is a membership test.
#[partial]
def declared_names_of (decl_list : List Decl) (acc : List String) : List String :=
    match decl_list {
        List.empty => acc,
        List.cons d rest =>
            declared_names_of rest (List.append acc (decl_carried_names d))
    }

/// `decl_local_name` plus the constructor names an `inductive_d` carries.
/// Split out so `declared_names_of` stays one flat walk over the decl list.
def decl_carried_names (d : Decl) : List String :=
    match decl_local_name d {
        Option.none => List.empty,
        Option.some nm =>
            match d {
                Decl.inductive_d ind => match ind {
                    Inductive.mk _ _ _ constructors _ _ =>
                        List.cons nm (constructor_names constructors)
                },
                _ => List.cons nm List.empty
            }
    }

/// Constructor names, as DECLARED: bare (`cons`, `mk`).
///
/// This side's parser already stores them single-segment
/// (`NamePath.npath [name]`, `lang/parser.mo`) and `build_scope_inductive`
/// (`lang/scope.mo`) binds each one under that bare name, so
/// `use M {cons}` really does bind `cons` here. The Rust host stores the
/// same constructor as two segments (`List.cons`,
/// `term::induct_constructor`) and its `declared_names_of` therefore takes
/// the last segment to land on the same string -- if it did not,
/// `use M {cons}` would pass this check and fail the host's, and CI runs
/// both over the corpus. Keep the two in step.
///
/// Only an ordinary `type` reaches this function: `decl_carried_names`
/// calls it for `Decl.inductive_d` alone, so a `struct`'s synthesized
/// `mk` is deliberately NOT a declared name here -- and the host's
/// `declared_names_of` restricts itself to `InductiveVariant::Generic` to
/// match.
#[partial]
def constructor_names (cns : List InductConstructor) : List String :=
    match cns {
        List.empty => List.empty,
        List.cons cn rest =>
            match cn {
                InductConstructor.mk nm _ _ =>
                    List.cons (show_name_path nm) (constructor_names rest)
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
/// implementation of this empty-component/trailing-slash/absolute-second-
/// argument logic (was duplicated here before `Path` existed).
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
/// file registered under two module paths BY COMPARING THAT STRING. From
/// inside a mote the join legitimately carries `..`, so one file reached by
/// two routes could be spelled `../init/src/number.mo` and
/// `<root>/init/src/number.mo`: two strings, no dedup, declarations owned by
/// two modules at once, and every reference to them reading as `declared in
/// number, init.number`. That flood is a qualify failure -- and from inside
/// `cli/` it did not terminate at all: measured, 177 s of 100% CPU with not
/// one syscall after the last resolution.
///
/// The bare-`number` route that made the two-routes case routine
/// (`init/src/lib.mo`'s old `pub use number {*}`, beside the `init::number`
/// a mote prefix reads off `mote_relative_file`) is gone: a `use` must now
/// name a mote or `lib`. The `..` case it exposed is inherent to
/// mote-relative resolution, so this function stays.
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

/// Read a module path as MOTE-relative SEGMENTS: the first segment names a
/// mote, whose sources live under its `src/`, and the rest is the module
/// path within it. `llvm.ir` -> `["llvm", "src", "ir.mo"]`; a lone `std` ->
/// that mote's library root, `["std", "src", "lib.mo"]`.
///
/// Segments rather than the joined string, because this reading has two
/// consumers with different roots to anchor it at: `mote_relative_file`
/// below (joined, at the working directory) and the installed-toolchain
/// tier (`Mote.toolchain_candidates`, joined at a toolchain root). One
/// reading, so the two cannot drift -- and the same reason the ambient
/// trio's `resolve_ambient_file` takes segments rather than a literal.
def mote_segments (mp : ModulePath) : List String :=
    match mp {
        ModulePath.mp ids =>
            match ids {
                List.empty => List.empty,
                List.cons hd rest =>
                    let mote : String := identifier_to_string hd in
                    match rest {
                        List.empty => [mote, "src", "lib.mo"],
                        List.cons _ _ =>
                            [mote, "src",
                             String.concat (module_path_to_file (ModulePath.mp rest)) ".mo"]
                    }
            }
    }

/// `mote_segments` joined with single `/`s -- `llvm/src/ir.mo`.
///
/// This is what makes `use llvm.ir` find the file at all now that every
/// mote keeps its modules under `src/` (`plans/packaging/package-system.md`
/// §5a) -- `module_path_to_file` joins segments literally and knows nothing
/// about motes. The mote NAMES are still a fixed list here; the manifest-driven
/// table (and the "not a declared dependency" error that comes with it) is §5c.
def mote_relative_file (mp : ModulePath) : String :=
    join_path_segments (mote_segments mp) ""

/// The ambient trio's (`prelude`/`init`/`std`) own resolution: its
/// CWD-relative candidate first, then the manifest, then an installed
/// toolchain root.
///
/// The fall-through is the whole point of the helper, and it is what makes
/// resolution key off the MOTES rather than the working directory. The
/// joined candidate is spelled relative to the checkout root, so it is only
/// the answer when the CWD *is* that root -- which is why `monad check
/// src/main.mo` from inside `cli/` used to report a wall of "unknown
/// variable '++'" rather than loading its own prelude: `first_existing`
/// missed, the trio returned `none`, and no manifest was ever consulted.
/// From the root nothing changes, because the first candidate always hits.
///
/// Takes SEGMENTS rather than the joined string, so that the CWD-relative
/// spelling and the toolchain-relative one are built from ONE list:
/// `["init", "src", "prelude.mo"]` reads as `init/src/prelude.mo` under the
/// working directory and as `<root>/init/src/prelude.mo` under an installed
/// toolchain. It is also where the `prelude` alias lives -- `prelude`
/// belongs to `init`, and no module path can say so.
#[partial]
def resolve_ambient_file (base_dir : String) (mp : ModulePath) (segs : List String) : IO (Option String) := do {
    let r <- first_existing [join_path_segments segs ""];
    match r {
        Option.some p => return (Option.some p),
        Option.none => resolve_installed_or_manifest base_dir mp segs
    }
}

/// The last two tiers of EVERY resolution, in this order: the importing
/// mote's own manifest, then an installed toolchain root.
///
/// The manifest is first because it is EXPLICIT -- the mote declared this
/// dependency and said where it lives -- while a toolchain root is a
/// convention about the machine. A `std` vendored next to an external mote
/// therefore wins over the one in `~/.monad`, which is what pinning a
/// dependency means.
///
/// This pair is the whole answer for a mote in its own repository, which
/// has no checkout to resolve `init`/`std` out of: the manifest covers it
/// when it declared `path` dependencies, the toolchain root covers it when
/// it declared none and a nightly is installed.
def resolve_installed_or_manifest (base_dir : String) (mp : ModulePath) (segs : List String) : IO (Option String) := do {
    let via_manifest <- resolve_via_manifest base_dir mp;
    match via_manifest {
        Option.some p => return (Option.some p),
        Option.none => do {
            let root <- Mote.toolchain_root;
            toolchain_first_existing root segs
        }
    }
}

/// The installed-toolchain tier's own probe: `none` when this machine has
/// no toolchain root at all, else the first of the root's candidates for
/// `segs` that exists. Factored out so that "no root" is a miss rather than
/// a list of candidate paths built off a root that is not there.
def toolchain_first_existing (root : Option String) (segs : List String) : IO (Option String) := do {
    match root {
        Option.none => return Option.none,
        Option.some r => first_existing (Mote.toolchain_candidates r segs)
    }
}

/// Does this machine's toolchain root actually CARRY the ambient motes?
/// Probes `init/src/prelude.mo`, the one file every ambient resolution
/// needs and the same one `resolve_module_file` reads it from -- so this
/// answers the question resolution asks rather than an approximation of it.
///
/// The answer is what `Mote.toolchain_missing_hint` turns into a sentence,
/// and the distinction it draws is the useful one: a root that is THERE but
/// has no `init/src` (a `MONAD_ROOT` pointed at the wrong checkout, or at a
/// directory that is not one) needs different advice from a machine with no
/// root at all. `none` root is `false` here, since a root that does not
/// exist cannot carry anything.
def toolchain_has_ambient_sources (root : Option String) : IO Bool := do {
    let found <- toolchain_first_existing root ["init", "src", "prelude.mo"];
    match found {
        Option.some _ => return true,
        Option.none => return false
    }
}

/// The workspace ROOT above `dir`: the directory whose `mote.toml` carries
/// `[workspace] members`. `find_workspace_members` (`cli/src/main.mo`) is
/// the same walk, and it answers with that root's expanded MEMBERS; a caller
/// looking for a file that is not one of them (see `resolve_runtime_src`)
/// needs the root itself, which is the one thing the expansion throws away.
///
/// Lives here rather than beside `find_workspace_members` because
/// `resolve_runtime_src` is its only caller, and that has to sit at this
/// level: the codegen harnesses (`lang/src/codegen/test/e2e_harness.mo`,
/// `compile_tests.mo`, `test_link_e2e.mo`) compile the C runtime through the
/// same resolver, and they are modules of THIS mote -- so the resolver
/// cannot live in `cli/`, which is above them.
///
/// `Option.some ""` means the working directory is the root -- the same case
/// `find_workspace_members ""` already handles, where `dir` is `""` and
/// every path the caller builds from it stays CWD-relative.
#[partial]
def find_workspace_root (dir : String) (depth : I64) : IO (Option String) := do {
    if I64.lt depth 1 then do { return Option.none }
    else do {
        let here : List String <- Mote.workspace_members dir;
        if Bool.not (List.is_empty here) then do { return (Option.some dir) }
        else if String.beq dir "" then find_workspace_root ".." (depth - 1)
        else if String.beq dir "/" then do { return Option.none }
        else find_workspace_root (raw_path_join dir "..") (depth - 1)
    }
}

/// The first candidate that is present on disk, WITHOUT normalizing the
/// winner -- unlike `first_existing` above, and for the reason
/// `resolve_runtime_src`'s own doc comment gives: the winner may be a
/// walk-relative spelling whose `..` has to survive into the child process
/// that opens it.
#[partial]
def first_on_disk (candidates : List String) : IO (Option String) := do {
    match candidates {
        List.empty => return Option.none,
        List.cons path rest => do {
            let exists <- file_exists (Path.path path);
            if exists then return (Option.some path) else first_on_disk rest
        }
    }
}

/// The runtime C source, located from the first candidate that exists: the
/// target mote's own declared `[dependencies.runtime] path`, an installed
/// toolchain root, the workspace root above the working directory, and
/// finally `Runtime.c_path`.
///
/// The first two are ABSOLUTE by construction -- a manifest `path` may be
/// absolute, a toolchain root is -- and that matters because `clang`
/// resolves this argument against the COMPILER's own CWD. Only a relative
/// spelling is CWD-sensitive, so an absolute candidate sidesteps the
/// question the last two exist to answer. Those two stay relative: the
/// walk's answer is spelled from the working directory it walked from
/// (`../runtime/src/runtime.c` from inside `cli/`, where
/// `runtime/src/runtime.c` does not exist), and `Runtime.c_path` is the
/// checkout-root-relative literal, which is the right answer exactly when
/// the working directory IS that root.
///
/// The winner is deliberately NOT passed through `normalize_path`, even
/// though a walked spelling still carries its `..`: that spelling is valid
/// only relative to the CWD it was walked from, so collapsing it would name
/// a file that does not exist from inside `cli/`. `normalize_path` is safe
/// for module resolution because the resolved path is read in the same
/// process that resolved it; this one is handed to a CHILD process.
///
/// Falls back to `Runtime.c_path` when no candidate exists, rather than
/// reporting a miss here: the child is what knows how to say "no such file
/// or directory", and its message names the path it could not open.
///
/// `base_dir` is the directory of the file being compiled or tested, which
/// is what the manifest tier needs -- the mote whose `[dependencies.runtime]`
/// says where the C runtime lives. That is the tier an EXTERNAL mote relies
/// on (one in its own repository, with no checkout to walk up into), and it
/// is why this no longer takes the working directory as its only anchor.
///
/// `pub` because `cli` is a different mote from `lang` and its `compile`/`run`
/// paths are the callers: this moved here from `cli/src/main.mo` when the
/// codegen harnesses below needed the same resolver, and a def that crosses a
/// mote boundary has to say so.
pub def resolve_runtime_src (base_dir : String) : IO String := do {
    let manifest <- Mote.discover base_dir;
    let declared := match manifest {
        Option.none => List.empty,
        Option.some m => match MoteManifest.dep_dir_of m "runtime" {
            Option.none => List.empty,
            Option.some dep_dir => runtime_c_in dep_dir
        }
    };
    let root <- Mote.toolchain_root;
    let installed := match root {
        Option.none => List.empty,
        Option.some r => Mote.toolchain_candidates r ["runtime", "src", "runtime.c"]
    };
    let ws <- find_workspace_root "" 32;
    let walked := match ws {
        Option.none => List.empty,
        Option.some r => [raw_path_join r "runtime/src/runtime.c"]
    };
    let found <- first_on_disk (List.append declared (List.append installed walked));
    match found {
        Option.none => return Runtime.c_path,
        Option.some p => return p
    }
}

/// `<dep dir>/src/runtime.c` -- the one file a `[dependencies.runtime]`
/// `path` contributes. `raw_path_join` rather than `++`, so an absolute
/// `path` (which is what an external mote writes) stays absolute instead of
/// being appended to the mote's own directory as `./<abs>`.
def runtime_c_in (dep_dir : String) : List String :=
    [raw_path_join (raw_path_join dep_dir "src") "runtime.c"]

/// Resolve a module path to a file path, trying different directories
/// First tries relative to base_dir, then the mote layout, then falls back to
/// the stdlib/lang roots for bare (un-mote-qualified) names.
///
/// Every convention above is anchored at the WORKING DIRECTORY, so all of
/// them miss for a mote in its own repository. What answers there is the
/// cascade's last two tiers (`resolve_installed_or_manifest`): the mote's
/// own declared `path` dependencies, then an installed toolchain root --
/// which is what lets an external mote `use std::map` with no checkout
/// anywhere and nothing declared.
///
/// There is no `examples/` fallback: an example is a mote like any other
/// now (`#![mote { ... }]`), so nothing resolves it by directory name.
#[partial]
def resolve_module_file (base_dir : String) (mp : ModulePath) : IO (Option String) {
    let mp_str := module_path_to_file mp;
    let with_extension := String.concat mp_str ".mo";
    let prelude_segs := ["init", "src", "prelude.mo"];
    let relative_path := path_join base_dir with_extension;
    let direct_path := with_extension;
    let mote_path := mote_relative_file mp;
    let init_path := String.concat "init/src/" with_extension;
    let std_path := String.concat "std/src/" with_extension;
    let lang_path := String.concat "lang/src/" with_extension;

    if String.beq mp_str "prelude"
    then resolve_ambient_file base_dir mp prelude_segs
    // Bare `init`/`std` are ambient re-export hubs (`init/src/lib.mo`/
    // `std/src/lib.mo`) -- their own module NAME no longer matches their
    // FILE name (unlike every other bare top-level module), so they
    // need the same kind of explicit special case `prelude` already
    // has, ahead of the general search below. (`mote_relative_file` would
    // reach the same two files, but only because a one-segment path means
    // "that mote's lib root" -- spelling it out keeps the ambient trio
    // together and independent of that rule.)
    else if String.beq mp_str "init"
    then resolve_ambient_file base_dir mp ["init", "src", "lib.mo"]
    else if String.beq mp_str "std"
    then resolve_ambient_file base_dir mp ["std", "src", "lib.mo"]
    else do {
        // `examples/` used to be a candidate here (`examples/<stem>.mo`).
        // It is gone: every example now carries a `#![mote { ... }]`
        // annotation naming it and its `deps`, so examples are reached the
        // way motes are -- by their own path, or as a declared dependency --
        // rather than by a name-convention probe into their directory. The
        // probe served nothing once that landed: an example referring to a
        // SIBLING resolves through `relative_path` above, which is tried
        // first and always hit for a file in the same directory.
        let found <- first_existing [
            relative_path, direct_path, mote_path, init_path, std_path, lang_path,
        ];
        match found {
            Option.some p => return (Option.some p),
            // Still only when every convention missed: the `motes/*/src`
            // search path, then the manifest, then an installed toolchain
            // root.
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
                // probed under every `motes/*/src/`. A `use` can no longer
                // reach it -- the qualification rule rejects a one-segment
                // module path before resolution ever runs
                // (`check_use_spellings` below, the Rust host's
                // `validate_use_qualification`), so there is no spelling of
                // `use greet` left to find `motes/example/src/greet.mo`.
                // It stays because this cascade is shared: the dependency
                // walk and the prelude/toolchain probes call it too, and
                // dropping a tier would change how they resolve.
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
                let in_motes <- first_existing (List.append in_motes_cands (List.cons in_motes_qualified List.empty));
                match in_motes {
                    Option.some p => return (Option.some p),
                    Option.none => resolve_installed_or_manifest base_dir mp (mote_segments mp)
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
/// path. Directory probing rather than manifest-driven member resolution,
/// deliberately: the Rust host probes directories, so parity means probing
/// them too.
///
/// This is the tier a one-segment `use greet` would have needed, and that
/// spelling is gone: a `use` must now name a mote or `lib`, so the fixture
/// in `examples/test_mote.mo` reads `use example::greet {greet}` and is
/// answered by the qualified candidate just above rather than here. The
/// scan is kept because the cascade is shared, not because a `use` can
/// reach it.
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
    let mote <- Mote.discover base_dir;
    match mote {
        Option.none => return Option.none,
        Option.some m => do {
            let cands <- manifest_candidates m mp;
            first_existing cands
        }
    }
}

/// `mp`'s manifest-derived candidate files, self first: a mote may always
/// refer to itself, so when the first segment IS this mote's name that is
/// the answer, and the dependency list is tried only when it is not.
#[partial]
def manifest_candidates (m : MoteManifest) (mp : ModulePath) : IO (List String) := do {
    let deps <- mote_dep_files m mp;
    match mote_path_within m mp {
        Option.none => return deps,
        Option.some c => return (List.cons c deps)
    }
}

/// The file a declared dependency's `mp` names -- `mote_path_within`'s
/// mirror for a DEPENDENCY, using the manifest's `path` rather than the
/// mote's name. `List.empty` when `mp`'s first segment is not a dependency
/// the manifest located (undeclared, or declared without a `path`), which
/// leaves the cascade's own answer to stand.
///
/// IO for one arm: a BARE dependency name is that dependency's library root,
/// and only the dependency's own manifest knows where it declared that.
#[partial]
def mote_dep_files (m : MoteManifest) (mp : ModulePath) : IO (List String) := do {
    match mp {
        ModulePath.mp ids =>
            match ids {
                List.empty => return List.empty,
                List.cons hd rest =>
                    // `prelude` is the one module whose NAME is not its FILE
                    // name, and it belongs to `init` -- the same re-spelling
                    // `resolve_module_file`'s own `prelude` special case
                    // applies to the CWD-relative candidate. It is
                    // one-segment by construction, so it never reaches the
                    // `rest` cases below.
                    if String.beq (identifier_to_string hd) "prelude"
                    then return (mote_dep_file_of m "init" "prelude")
                    // A one-segment path means "that mote's own library
                    // root", the same rule `mote_path_within` applies.
                    else if List.is_empty rest
                    then do {
                        let xs <- mote_dep_lib_file_of m (identifier_to_string hd);
                        return xs
                    }
                    else return (mote_dep_file_of m (identifier_to_string hd)
                             (module_path_to_file (ModulePath.mp rest)))
            }
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

/// The one candidate a declared dependency's BARE name resolves to: that
/// dependency's own library root. `dep_man` is its manifest when the caller
/// found one at its directory (`Mote.manifest_at`); without one the
/// conventional `<dep dir>/src/lib.mo` stands -- which is what every
/// manifest in this tree restates, so the fallback is the usual answer and
/// not a legacy one.
///
/// Pure, so all three cases are testable without a filesystem; the IO half
/// that finds `dep_man` is `mote_dep_lib_file_of` below.
def mote_dep_lib_files (m : MoteManifest) (dep : String) (dep_man : Option MoteManifest) : List String :=
    match MoteManifest.dep_dir_of m dep {
        Option.none => List.empty,
        Option.some dep_dir =>
            match dep_man {
                Option.some d => List.cons (mote_lib_file_of d) List.empty,
                Option.none => List.cons (String.concat (mote_dep_src_root dep_dir) "lib.mo") List.empty
            }
    }

#[partial]
def mote_dep_lib_file_of (m : MoteManifest) (dep : String) : IO (List String) := do {
    match MoteManifest.dep_dir_of m dep {
        Option.none => return List.empty,
        Option.some dep_dir => do {
            let dep_man <- Mote.manifest_at dep_dir;
            return (mote_dep_lib_files m dep dep_man)
        }
    }
}

/// A mote's own library root: its declared `[lib] path`, which
/// `Mote.lib_target_path` already spells as `<mote dir>/<declared or
/// src/lib.mo>`. The fallback covers a `MoteManifest` built without one.
def mote_lib_file_of (m : MoteManifest) : String :=
    match m.lib_path {
        Option.some p => p,
        Option.none => String.concat (String.concat (MoteManifest.src_root m) "/") "lib.mo"
    }

/// `<mote>.a.b` -> `<mote dir>/src/a/b.mo`, and a bare `<mote>` -> the
/// mote's library root. `Option.none` when the path does not name this mote.
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
                            List.empty => Option.some (mote_lib_file_of m),
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
    let resolved <- resolve_module_file base_dir mp;
    match resolved {
        Option.some file_path => load_module_decls_at file_path mp,
        Option.none => do { return Option.none }
    }
}

/// The parse-and-leniency-gate half of `load_module_decls_at`, split out
/// so the same gate runs over text that did NOT come from disk -- see
/// `load_module_with_info_from_source`, which supplies an editor buffer.
/// `mp` names the module in the truncation message and is read for
/// nothing else.
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
def load_module_decls_of_text (mp : ModulePath) (content : String) : IO (Option (List Decl)) := do {
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

/// Read an ALREADY-RESOLVED module file from disk, then hand it to the
/// gate above. `Option.none` if there is no such file.
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
#[partial]
def load_module_decls_at (file_path : String) (mp : ModulePath) : IO (Option (List Decl)) {
    let present : Bool <- file_exists (Path.path file_path);
    if Bool.not present
    then do { return Option.none }
    else do {
        let content : String <- IO.read_file (Path.path file_path);
        load_module_decls_of_text mp content
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
    let opt_decls <- load_module_decls base_dir mp;
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
                let dep_decls_opt <- load_module_decls base_dir head;
                match dep_decls_opt {
                    Option.some dep_decls => do {
                        // First, find the actual file path for this module
                        let resolved_path_opt <- resolve_module_file base_dir head;
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
                let loaded <- load_module_with_info_cached pending.base_dir head cache;
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
            let entry_opt <- loader head;
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
    let sd_opt <- load_module_scope base_dir mp;
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
    let diags <- check_module_with_scope scope decl_list locals Option.none false;
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
                    let lv : LocalVar := { name := n, typ := Term.sort (SortLevel.concrete 0), multiplicity := Multiplicity.many } in
                    let extended : LocalScope := scope_push_local lv locals in
                    bind_unresolved_as_local_typevars rest scope extended
            }
    }

/// Walk a type's leading quantifier chain, collecting each binder's NAMED
/// debug-name identifier (unnamed binders are skipped).
/// This is how `locals_with_def_typevars` recovers the implicit type
/// parameters `elaborate.mo`'s `wrap_forall` introduced: a def like
/// `def Lens [Functor F] {F : Type -> Type} (...) : Type := ...` has its
/// `{F}` clause deliberately dropped by the parser
/// (`def_implicit_close`, lang/parser.mo) on the understanding that
/// `elaborate_def` re-introduces `F` as a leading quantifier binder
/// -- once that elaboration is wired into the pipeline, the binder name
/// only survives HERE (in `typ`'s quantifier chain), so this walk is what
/// skolemizes `F` into `locals` for the body check. Mirrors the Rust
/// reference's own quantifier-chain walk. Does NOT descend past the leading
/// quantifiers: nested inner ones (under an arrow) belong to a different
/// scope and are not this def's own implicit params.
#[partial]
def forall_chain_binder_names (typ : Term) : List Identifier :=
    match typ {
        // Three-way. An EXPLICIT binder is a real arrow and stops the
        // walk, which is what the old catch-all did -- descending past one
        // would pull type variables out of a function's domain, a scope
        // this def does not own.
        Term.pi b _dom body =>
            if binder_is_explicit b
            then List.empty
            else if binder_is_level b
            // A LEVEL binder's name is not a type variable: its only
            // consumer, `locals_with_def_typevars`, skolemizes these
            // names into `LocalScope` as TERM locals, and a level
            // variable must never land there (`scope_find_local` would
            // then find it, and `whnf_delta`'s local check would refuse
            // to unfold a same-named global). Levels live in the
            // signature as binders and are resolved by level
            // substitution, never by local lookup.
            then forall_chain_binder_names body
            else match binder_name b {
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
    let diags <- check_module_decls_with_scope scope decl_list locals path verbose;
    return (list_append diags (check_termination_all decl_list))
}

// --- Ranged diagnostics (the language server's view) ---
//
// Everything above returns rendered strings -- what a terminal wants, and
// all a terminal can use. A language server cannot work that way: the
// editor needs a RANGE beside each message, and the range is discarded the
// moment a message is rendered. So this is a parallel surface, not a change
// to the one `check` runs.

/// One diagnostic, with the declaration it was reported against.
///
/// `range` is `Option` because not every diagnostic HAS a declaration: the
/// termination pass reports per module and a load failure reports per file.
/// `Option.none` is that case, stated rather than filled in with an
/// invented range.
///
/// THERE IS DELIBERATELY NO SEVERITY FIELD YET, and the reason binds
/// whoever adds one. `cli/src/main.mo`'s `run_check_loop` counts EVERY
/// diagnostic as an error and prints `FAIL` for any non-empty list, and it
/// reads `FileCheckResult.diagnostics : List String`, which has no severity
/// to consult. So the first non-error diagnostic -- the self-hosted
/// checker's warning passes, explicitly not in this cut -- has to land
/// TOGETHER with a severity-aware `run_check_loop` and a `FileCheckResult`
/// that carries severity, or self-hosted `check` starts failing on warnings
/// and takes CI with it. Adding the field now, when nothing can produce a
/// warning, would be an untestable channel.
///
/// `message` IS THE RENDERED MULTI-LINE STRING, not a one-line summary, and
/// that is a binding note on the wire layer rather than a defect. The ranged
/// walk tags what `check_decl_with_scope` already returns, and that is
/// `render_type_error`'s / `render_parse_error`'s output: a header line, a
/// `--> path:line:col` arrow, and three lines of source with a caret. Right
/// for `check`'s terminal, wrong for an editor, which wants the header line
/// alone in its popup. The reduction belongs where the wire diagnostic is
/// built (`motes/toolkit`'s diagnostic module), and the plain forms to
/// reduce TO already exist: `type_error_message` and `error_message`
/// (`lang/src/typecheck/diagnostic.mo:40`, `lang/src/parser/diagnostic.mo:23`).
/// Do not add a second message field here -- `check` reads this one.
pub struct Diagnostic {
    message : String,
    range : Option SourceRange,
}

pub def diagnostic_message (dg : Diagnostic) : String := dg.message

pub def diagnostic_range (dg : Diagnostic) : Option SourceRange := dg.range

#[partial]
def attach_range_go (r : Option SourceRange) (msgs : List String) (acc : List Diagnostic) : List Diagnostic :=
    match msgs {
        List.empty => acc,
        List.cons m rest => attach_range_go r rest (List.cons (Diagnostic.mk m r) acc),
    }

/// Tag every message one declaration produced with that declaration's range.
#[partial]
def attach_range (r : Option SourceRange) (msgs : List String) : List Diagnostic :=
    list_reverse (attach_range_go r msgs List.empty)

/// The range recorded for a declaration, matched by NAME.
///
/// NOT by position, and this is the part that looks like it should be a zip
/// and must not be. `ElaboratedModules.target_decls` -- the list the checker
/// actually walks -- is the EXPANDED declaration list: `parse_all_decls`
/// runs `expand_decls`, which turns one `macro_call_d` into many
/// declarations, and the elaborate pipeline's `promote_instance_defs` and
/// `resolve_infix_decls` add more again. This table is pre-expansion, by
/// design. So the two lists differ in LENGTH and in ORDER, and zipping them
/// would silently attach the wrong range to every declaration from the first
/// macro call onwards -- wrong in the way that still looks plausible.
///
/// A name that expanded away, or that elaboration minted, simply has no
/// range: `Option.none`, which every consumer already handles.
///
/// Names are not unique in the abstract -- nothing stops a file from
/// declaring `foo` twice under different kinds -- so this takes the FIRST
/// match in declaration order. Two same-named declarations in one file is
/// the only way to observe the difference, and it costs a line or two of
/// range error, never a wrong file.
#[partial]
def range_for_decl (decl_ranges : List DeclRange) (d : Decl) : Option SourceRange :=
    match decl_name_and_kind d {
        Pair.pair n _kind => find_decl_range decl_ranges n,
    }

#[partial]
def find_decl_range (decl_ranges : List DeclRange) (n : String) : Option SourceRange :=
    match decl_ranges {
        List.empty => Option.none,
        List.cons dr rest =>
            if String.beq (decl_range_name dr) n then Option.some (decl_range_span dr)
            else find_decl_range rest n,
    }

/// `check_module_decls_with_scope`'s ranged sibling: the same per-decl walk,
/// the same `check_decl_with_scope` calls, each declaration's message list
/// tagged with that declaration's range.
///
/// A SIBLING rather than a rewrite, and the duplication is the point: the
/// string version stays byte-identical, and because the two walk
/// independently, neither `check`'s rendered output nor its cost can move.
/// Threading a range table through the string version would make every
/// `check` build and consult a table it never reads.
#[partial]
def check_module_decls_with_scope_ranged (scope : Scope) (decl_list : List Decl) (locals : LocalScope)
    (path : Option String) (decl_ranges : List DeclRange) (verbose : Bool) : IO (List Diagnostic) :=
    match decl_list {
        List.empty => do { return List.empty },
        List.cons d rest => do {
            let here : List String <- check_decl_with_scope d scope locals path verbose;
            let there <- check_module_decls_with_scope_ranged scope rest locals path decl_ranges verbose;
            return (list_append (attach_range (range_for_decl decl_ranges d) here) there)
        }
    }

/// `check_module_with_scope`'s ranged sibling: the same two gates in the
/// same order, the per-declaration walk and then the module-level
/// termination pass.
///
/// `check_termination_all` reports on the module as a whole -- it is a
/// decl-list walk building a call graph, not a per-decl check -- so its
/// messages carry `Option.none` rather than a range borrowed from whichever
/// declaration happens to sit nearby.
pub def check_module_with_scope_ranged (scope : Scope) (decl_list : List Decl) (locals : LocalScope)
    (path : Option String) (decl_ranges : List DeclRange) (verbose : Bool) : IO (List Diagnostic) := do {
    let diags <- check_module_decls_with_scope_ranged scope decl_list locals path decl_ranges verbose;
    let no_range : Option SourceRange := Option.none;
    return (list_append diags (attach_range no_range (check_termination_all decl_list)))
}
// --- Affine checking (`--affine`): the M2 rule as real diagnostics ---
//
// `affine.mo`'s `check_def` has existed since M2 but nothing in the
// real check driver ever called it — the only caller was
// `bench/src/affine_report.mo`, which tallies but never fails. This
// is the wiring that turns the advisory rule into checkable output:
// every ordinary diagnostic `check_module_with_scope` produces, PLUS
// the affine rule's, through the same `render_type_error` and the
// same empty-list-means-clean gate.
//
// Shape note (and why a sibling, not a parameter): the flag is a NEW
// `check_module_with_scope_affine` entry point that duplicates the
// decl-walk's four-line shape, rather than an `affine_mode : Bool`
// threaded through the existing chain. That threading would touch
// every `check_module_with_scope` call site in this file and
// `cli/src/main.mo` — a dozen-plus edit lines of pure conflict
// surface in exactly the files the upcoming build-system rebase
// restructures. The sibling touches none of them: existing
// signatures, existing call sites stay byte-identical, and a rebase
// either carries this whole block or drops it as a unit.

/// The `--affine` counterpart of `check_module_with_scope`: same
/// ordinary diagnostics plus the M2 affine rule's, with `ctors`/
/// `borrows` built ONCE per module rather than per def
/// (`affine.mo`'s own doc on `check_def`; per-node lookup would be a
/// full scope scan at every application).
pub def check_module_with_scope_affine (scope : Scope) (decl_list : List Decl) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) := do {
    let ctors : HashMap String Bool := ctor_name_set scope;
    let borrows : HashMap String Bool := borrow_of_name_set scope;
    let diags <- check_module_decls_with_scope_affine ctors borrows scope decl_list locals path verbose;
    return (list_append diags (check_termination_all decl_list))
}

#[partial]
def check_module_decls_with_scope_affine (ctors : HashMap String Bool) (borrows : HashMap String Bool) (scope : Scope) (decl_list : List Decl) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match decl_list {
        List.empty => do { return List.empty },
        List.cons d rest => do {
            let here : List String <- check_decl_with_scope_affine d ctors borrows scope locals path verbose;
            let there : List String <- check_module_decls_with_scope_affine ctors borrows scope rest locals path verbose;
            return (list_append here there)
        }
    }

/// The affine variant of `check_decl_with_scope`: for everything with a
/// term of its own, ordinary type diagnostics first (via the existing,
/// untouched walk), then the affine rule's appended. Non-def decls
/// have no affine content of their own and delegate wholesale.
#[partial]
def check_decl_with_scope_affine (d : Decl) (ctors : HashMap String Bool) (borrows : HashMap String Bool) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match d {
        Decl.def_d df =>
            // The gate mirrors `check_decl_with_scope`'s own arm exactly:
            // a dict value def skips the ORDINARY check too (its body is
            // a codegen artifact ordinary `type_check` can't validate --
            // see `is_dict_value_def`), not just the affine extras.
            if is_dict_value_def df then do { return List.empty }
            else do {
                let diags <- check_def_with_scope df scope locals path verbose;
                let extra : List String :=
                    render_affine_diags (check_def scope ctors borrows df) (show_name_path df.name) path;
                return (list_append diags extra)
            },
        // A `scoped_open_d`'s inner decl is its own decl to check, same
        // as the ordinary walk's deliberate recursion.
        Decl.scoped_open_d _ _ inner => check_decl_with_scope_affine inner ctors borrows scope locals path verbose,
        _ => check_decl_with_scope d scope locals path verbose,
    }

/// `affine.mo`'s `List TypeError` rendered through the same
/// `render_type_error` every other diagnostic here uses, with the
/// def's own name as the context.
#[partial]
def render_affine_diags (errs : List TypeError) (context_name : String) (path : Option String) : List String :=
    match errs {
        List.empty => List.empty,
        List.cons e rest => List.cons (render_type_error context_name path e) (render_affine_diags rest context_name path),
    }

/// `promote_instance_defs`'s own `__Dict_ClassName_Args` value def
/// (`lang/scope.mo`'s `promote_instance`, e.g. `__Dict_Speak_Dog`) is a
/// pure codegen artifact -- its `.typ` is a bare sort but its
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

/// `scope` with the def-body match-coverage check switched off, when `attrs`
/// carries `#[allow_incomplete_match "<reason>"]` (`types.mo`). Both def-body
/// entry points below go through here; see `validate_match_coverage`
/// (`lang/typecheck/infer.mo`) for why one attribute is enough and why it is
/// not `#[partial]`.
def scope_for_def_body (attrs : List Attribute) (scope : Scope) : Scope :=
    if has_incomplete_match_exemption attrs
    then { scope with incomplete_match_ok := true }
    else scope

/// `scope` for an ELABORATION body, where coverage is never checked.
///
/// Coverage belongs to `check`, which turns a rejection into a diagnostic a
/// reader sees. Elaboration's caller is best-effort by design
/// (`elaborate_module_decls_reporting` below keeps a failed decl UNCHANGED and
/// prints only under `--verbose`), so a coverage rejection here is silently
/// swallowed and codegen then compiles the un-elaborated body with its
/// syntactic fallbacks -- `void_val` struct literals and index-0 field reads.
/// That is a SIGSEGV in the self-compiled binary with no diagnostic anywhere,
/// the exact shape `lang/codegen/validate.mo` documents; it cost a ladder
/// rung on 2026-10-06. Checking the same rule twice buys nothing: every def
/// elaboration sees has already been through `check_def_with_scope`.
def scope_for_elab_body (attrs : List Attribute) (scope : Scope) : Scope :=
    let body_scope : Scope := scope_for_def_body attrs scope in
    { body_scope with incomplete_match_ok := true }

#[partial]
def check_def_with_scope (df : Def) (scope : Scope) (locals : LocalScope) (path : Option String) (verbose : Bool) : IO (List String) :=
    match df {
        Def.mk {name, typ, term := body, constraints := _constraints, attrs, vis := _vis, ..} => do {
            if verbose then println ("  checking def " ++ show_name_path name) else do { return unit };
            if is_term_hole body then do {
                return List.empty
            } else do {
                let locals_ : LocalScope := locals_with_def_typevars typ body scope locals;
                let body_scope : Scope := scope_for_def_body attrs scope;
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
                return (match type_check body typ body_scope empty_local_types locals_ {
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
        let body_scope : Scope := scope_for_elab_body attrs scope in
        match type_check body typ body_scope empty_local_types locals_ {
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
// arrow's DOMAIN -- `Term.pi`'s `arg`, which is also where a former
// `forall`'s `kind` now sits -- staying put
// across the codomain. So `Bad -> I64` is negative and rejected, while
// `I64 -> Bad` and `(Bad -> I64) -> I64` -- two flips -- are accepted. Both
// of those were measured against the host rather than reasoned about.
//
// Self-reference is matched on the SPELLING the elaborator left in the
// term, exactly as the reference matches it, and for a qualified occurrence
// the module half is compared too. That half is not decoration: the same
// source checked twice by `target-rust/release/monad-rs` gets different verdicts
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
        // Merged; inert on the folded flavour -- a quantifier's domain is a
        // sort, and `strict_pos_bad` answers `false` for one, so the old arm's
        // "flip over the kind, then walk the body" is what this does.
        Term.pi _b arg ret =>
            strict_pos_bad module_str type_str arg (strict_pos_flip polarity) || strict_pos_bad module_str type_str ret polarity,
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
        Scope.mk module_id _sd _parent _ok =>
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
def check_file_cached_mode (affine : Bool) (cache : ModuleInfoCache) (file_path : String) (verbose : Bool) : IO FileCheckAndCache {
    let exists : Bool <- file_exists (Path.path file_path);
    if exists then do {
        if verbose then println ("checking " ++ file_path) else do { return unit };
        let ec <- elaborate_loaded_modules_cached file_path false cache verbose;
        let out_cache : ModuleInfoCache := ec.cache;
        match ec.elaborated {
            Result.ok em => do {
                let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
                // The one line `affine` changes: the M2 rule's
                // diagnostics appended to the ordinary ones
                // (`check_module_with_scope_affine`'s own doc above).
                let diags <- if affine
                    then check_module_with_scope_affine em.scope em.target_decls empty_locs (Option.some file_path) verbose
                    else check_module_with_scope em.scope em.target_decls empty_locs (Option.some file_path) verbose;
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

/// `check_file_cached` for text that is not (yet) on disk -- the language
/// server's entry point. The same body minus the `file_exists` gate: a
/// buffer is checked from what the editor holds, so whether a file of
/// that name exists is no longer the question.
///
/// The checking is `check_module_with_scope`, byte-identical to the disk
/// path's, so a buffer and the file it stands for report the same
/// diagnostics once saved.
///
/// `verbose` must be false on any path whose stdout is a protocol stream.
#[partial]
pub def check_file_cached_from_source (cache : ModuleInfoCache) (file_path : String) (source : String) (verbose : Bool) : IO FileCheckAndCache := do {
    let ec <- elaborate_loaded_modules_cached_go file_path false (Option.some source) cache verbose;
    let out_cache : ModuleInfoCache := ec.cache;
    match ec.elaborated {
        Result.ok em => do {
            let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
            let diags <- check_module_with_scope em.scope em.target_decls empty_locs (Option.some file_path) verbose;
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
}

// --- The ranged file check (what `monad lsp` calls) ---

/// `FileCheckAndCache` for the ranged path: the same three pieces, with
/// `Diagnostic` in place of the rendered string -- plus the two things
/// navigation needs and nothing else in the compiler produces.
///
/// WHY THE SCOPE IS HERE. A language server answers hover and
/// go-to-definition by resolving an identifier against the scope of the
/// file it was typed in, and that scope exists for exactly as long as the
/// check that built it: `check_buffer_ranged` has it in `em.scope` and used
/// to drop it on the floor, so the only way for a server to resolve two
/// identifiers in the same file would have been to re-elaborate the whole
/// closure per keystroke. Carrying it out of the check is what makes a
/// warm recheck worth having -- and it is the reason this struct grew
/// rather than navigation growing its own entry point. `Option.none` on
/// every path that did not elaborate: a file that did not parse has no
/// scope, and neither has one whose elaboration failed.
///
/// WHY THE RANGES ARE HERE. `decl_ranges_of_located` was already computed
/// on the elaborated path (the ranged diagnostics key on it), and on the
/// two failure paths the located parse is in the caller's hand, so the
/// outline costs nothing extra -- and it is most wanted exactly when the
/// file does not compile. `List.empty` only when there was no located
/// parse at all.
pub struct RangedFileCheck {
    path : String,
    diagnostics : List Diagnostic,
    cache : ModuleInfoCache,
    ranges : List DeclRange,
    scope : Option Scope,
}

pub def ranged_file_path (f : RangedFileCheck) : String := f.path

pub def ranged_file_diagnostics (f : RangedFileCheck) : List Diagnostic := f.diagnostics

pub def ranged_file_cache (f : RangedFileCheck) : ModuleInfoCache := f.cache

pub def ranged_file_ranges (f : RangedFileCheck) : List DeclRange := f.ranges

pub def ranged_file_scope (f : RangedFileCheck) : Option Scope := f.scope

/// The one-diagnostic result for a buffer that did not parse, at the
/// position the parse gave up.
///
/// A `Location` is a point, so the range's two ends are the same value:
/// a zero-width range marks the spot rather than inventing an extent the
/// parser never measured.
///
/// `ranges` is whatever the caller's own parse produced, and is
/// `no_decl_ranges` from the strict-`fail` arm, which never got as far as a
/// declaration list. The truncation path below passes what the lenient walk
/// did manage to read, so the outline survives a syntax error -- which is
/// when a user most wants it.
#[partial]
def ranged_parse_failure (cache : ModuleInfoCache) (file_path : String) (source : String)
    (ranges : List DeclRange) (e : ParseError) : RangedFileCheck :=
    let msg : String := render_parse_error source (Option.some file_path) e in
    let loc : Location := parse_error_location source e in
    let span : SourceRange := SourceRange.mk loc loc (Option.some file_path) in
    let one_diag : Diagnostic := Diagnostic.mk msg (Option.some span) in
    let no_scope : Option Scope := Option.none in
    let one : RangedFileCheck := {
        path := file_path,
        diagnostics := [one_diag],
        cache := cache,
        ranges := ranges,
        scope := no_scope,
    } in
    one

/// No declaration ranges: a buffer the strict parse rejected outright, and
/// the empty accumulator of a range walk. Named rather than written
/// `List.empty` at each use, per this file's own convention -- an
/// unannotated empty list in argument position is the shape that resolved
/// to the wrong instance in the `Map.empty` bug.
def no_decl_ranges : List DeclRange := List.empty

/// A buffer the lenient top-level walk truncated.
///
/// THIS is the real parse-failure path, not the `fail` arm above, and
/// finding that out is most of why this function exists. `decls_try`
/// reports `success` on a malformed declaration -- it keeps everything it
/// accumulated and stops, discarding the rest of the file with no
/// diagnostic (its own comment records the reasoning and the reverted
/// resync attempt). So `decls_parser_located` almost never answers `fail`,
/// and the only signal that a file did not parse is a NON-EMPTY
/// remainder -- the very gate `load_module_decls_of_text` applies before it
/// will accept a module at all.
///
/// Running the strict twin here turns that signal back into a real
/// `ParseError`, so the message and the position come from
/// `render_parse_error`, the same renderer the rest of the tree uses,
/// instead of a second and worse spelling of the same fact.
///
/// `located` is the caller's lenient parse, and its ranges are carried
/// through to the result: the declarations the walk DID read are real
/// declarations at real positions, and dropping them here would make the
/// outline empty in precisely the file that needs one.
#[partial]
def ranged_truncation (cache : ModuleInfoCache) (file_path : String) (source : String)
    (located : LocatedDecls) : RangedFileCheck :=
    let ranges : List DeclRange := decl_ranges_of_located located in
    match decls_parser_strict source {
        ParseResult.fail e => ranged_parse_failure cache file_path source ranges e,
        // Unreachable in practice: `decls_skip_strict` consumes the whole
        // input or fails, so a lenient truncation implies a strict failure.
        // Kept as a stated `Option.none` rather than an invented position,
        // because a wrong range is worse than an absent one. The message
        // mirrors `load_module_decls_of_text`'s own truncation wording.
        ParseResult.success _ _ =>
            let msg : String := "error: " ++ file_path ++ " did not fully parse (stopped before end of file)" in
            let none_range : Option SourceRange := Option.none in
            let no_scope : Option Scope := Option.none in
            let one : RangedFileCheck := {
                path := file_path,
                diagnostics := [Diagnostic.mk msg none_range],
                cache := cache,
                ranges := ranges,
                scope := no_scope,
            } in
            one,
    }

/// The buffer parsed, so elaborate it and check it -- the ordinary path.
///
/// This is the ONE place a `Scope` for a buffer exists, so it is the one
/// place a language server's hover and go-to-definition can get one from;
/// both arms below therefore carry it out in the result rather than
/// letting it die with the local (see `RangedFileCheck`'s own doc).
#[partial]
def check_buffer_ranged (cache : ModuleInfoCache) (file_path : String) (source : String)
    (located : LocatedDecls) (verbose : Bool) : IO RangedFileCheck := do {
    let decl_ranges : List DeclRange := decl_ranges_of_located located;
    let ec <- elaborate_loaded_modules_cached_go file_path false (Option.some source) cache verbose;
    let out_cache : ModuleInfoCache := ec.cache;
    match ec.elaborated {
        Result.ok em => do {
            let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
            let diags <- check_module_with_scope_ranged em.scope em.target_decls empty_locs (Option.some file_path) decl_ranges verbose;
            let warm : Option Scope := Option.some em.scope;
            let ok : RangedFileCheck := {
                path := file_path,
                diagnostics := diags,
                cache := out_cache,
                ranges := decl_ranges,
                scope := warm,
            };
            return ok
        },
        Result.err e => do {
            // An elaborate-path failure is a rendered `String` by then --
            // the `Location` was discarded on the way down -- so this one
            // genuinely has no range to report. It has no scope either:
            // elaboration is what builds one, and it did not finish.
            let none_range : Option SourceRange := Option.none;
            let err_diag : Diagnostic := Diagnostic.mk e none_range;
            let no_scope : Option Scope := Option.none;
            let err : RangedFileCheck := {
                path := file_path,
                diagnostics := [err_diag],
                cache := out_cache,
                ranges := decl_ranges,
                scope := no_scope,
            };
            return err
        },
    }
}

/// `check_file_cached_from_source`'s ranged sibling: the language server's
/// entry point, and the whole reason the in-memory load path exists.
///
/// The buffer is parsed ONCE up front, for two reasons. The ranges have to
/// come from the text the editor is showing, which is the buffer and not
/// the file on disk. And a buffer that does not parse has to be reportable
/// WITH a range, which the elaborate path cannot do -- it reports load
/// failures as a rendered `String`, `load_module_decls_of_text` included.
///
/// When the parse does not complete, this returns that one diagnostic and
/// does NOT call elaborate. Both paths run the same grammar over the same
/// text and the same remainder gate, so continuing would report one problem
/// twice.
///
/// `verbose` must be false on any path whose stdout is a protocol stream.
/// Note the one hazard this does not remove: `load_module_decls_of_text`
/// prints its truncation message with an UNCONDITIONAL `println` (stdout,
/// not gated on `verbose`), so a DEPENDENCY that fails to parse -- a real
/// file on disk, reached by the walk -- still writes to stdout. That is
/// fine for `check` and must be dealt with before a server relies on it;
/// see the language-server plan's stdout rule.
#[partial]
pub def check_file_cached_from_source_ranged (cache : ModuleInfoCache) (file_path : String)
    (source : String) (verbose : Bool) : IO RangedFileCheck :=
    match decls_parser_located_with_ranges source {
        ParseResult.fail e =>
            do { return (ranged_parse_failure cache file_path source no_decl_ranges e) },
        ParseResult.success rem located =>
            if String.is_empty rem
            then check_buffer_ranged cache file_path source located verbose
            else do { return (ranged_truncation cache file_path source located) },
    }
/// The two pub faces of `check_file_cached_mode`: the signature every
/// existing caller uses stays byte-identical (`check_file_cached`), and
/// `--affine` gets a sibling rather than a threaded flag — the same
/// rebase-surgical choice as `check_module_with_scope_affine` above.
pub def check_file_cached (cache : ModuleInfoCache) (file_path : String) (verbose : Bool) : IO FileCheckAndCache :=
    check_file_cached_mode false cache file_path verbose

/// `check` with `--affine`: ordinary diagnostics plus the M2 affine
/// rule's, so a corpus file with an over-use fails `check` the same way
/// a type error already does.
pub def check_file_cached_affine (cache : ModuleInfoCache) (file_path : String) (verbose : Bool) : IO FileCheckAndCache :=
    check_file_cached_mode true cache file_path verbose

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
    let entries <- list_dir (Path.path dir);
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
    let sig_a : Term := Term.pi binder_anon Term.hole (Term.sort (SortLevel.concrete 1)) in
    let sig_b : Term := Term.sort (SortLevel.concrete 1) in
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
                incomplete_match_ok := false,
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
                incomplete_match_ok := false,
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
                incomplete_match_ok := false,
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
                incomplete_match_ok := false,
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
                incomplete_match_ok := false,
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
                incomplete_match_ok := false,
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
                incomplete_match_ok := false,
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
            let loaded <- load_module_with_info base_dir mp;
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
                let mote <- Mote.discover base_dir;
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
    let resolved_path_opt <- resolve_module_file base_dir mp;
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
            let decl_list <- resolve_lib_alias_decls_opt actual_base_dir raw_decls;
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

/// `load_module_with_info`, but the target module's DECLS come from
/// `source` rather than from disk -- the language server's path, so an
/// editor buffer is checked without being written out first.
///
/// The path is still resolved from `base_dir`/`mp`, so the returned
/// `ModuleInfo.file_path` is the real file, and a URI naming no workspace
/// module still fails here. Deliberate: it keeps the dependency WALK
/// (`collect_dep_module_infos`) reading real files, so only the single
/// module under the cursor comes from memory.
///
/// Both of `load_module_with_info`'s traps are preserved, and they are
/// load-bearing: `load_module_decls_of_text` carries the truncation gate,
/// and `resolve_lib_alias_decls_opt` is what makes a `use lib::x` inside
/// the buffer resolve. Dropping either surfaces much later as a wall of
/// `unknown variable`, never as the real cause.
#[partial]
def load_module_with_info_from_source (base_dir : String) (mp : ModulePath) (source : String) : IO (Option ModuleInfo) {
    let resolved_path_opt <- resolve_module_file base_dir mp;
    match resolved_path_opt {
        Option.none => do { return Option.none },
        Option.some file_path => do {
            let actual_base_dir : String := extract_directory file_path;
            let raw_decls : Option (List Decl) <- load_module_decls_of_text mp source;
            let decl_list <- resolve_lib_alias_decls_opt actual_base_dir raw_decls;
            match decl_list {
                Option.some decl_list => do {
                    let info : ModuleInfo := { path := mp, file_path := file_path, decl_list := decl_list };
                    return (Option.some info)
                },
                Option.none => do { return Option.none }
            }
        }
    }
}

/// Pick the target module's loader: the disk one normally, the buffer one
/// when the caller supplied source. The branch lives here, in one place,
/// so the dependency walk and both `_go` bodies below stay untouched.
#[partial]
def load_target_module (base_dir : String) (mp : ModulePath) (source : Option String) : IO (Option ModuleInfo) :=
    match source {
        Option.none => load_module_with_info base_dir mp,
        Option.some src => load_module_with_info_from_source base_dir mp src,
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

/// The directory a mote called `name` was FOUND in, working-directory-
/// relative, or `none` when no mote goes by that name. All three places one
/// can live are probed, because all three are real layouts a manifest can
/// point at:
///
///   * beside the working directory under its own name
///     (`mote_relative_file`'s convention, which is how every top-level mote
///     here resolves) -> `foo`;
///   * one level down under `motes/` (`motes_src_paths`' convention, which
///     is how `use example::greet` reaches `motes/example/src/greet.mo`)
///     -> `motes/foo`;
///   * one level UP, the sibling convention this repo's own manifests use
///     (`std/mote.toml`'s `path = "../init"`) -> `../foo`. Probed last
///     because it is the only one of the three whose answer is not already
///     under the working directory.
///
/// Each of the three exists because a layout exists that needs it, and the
/// third was found the way the first two were: by running `monad check` in a
/// nested mote at `nest/greet` whose dependency sits at `nest/foo` and
/// watching the hint not fire at all -- the message fell back to the
/// unnamed `unresolved module` and said nothing about a missing declaration.
/// `scripts/check-external-mote.sh`'s configuration 6 is that layout, kept.
///
/// Missing the `motes/` probe is not cosmetic either: it is exactly the case
/// where a `use` on a `motes/*` mote would go UNREPORTED when its
/// `deps := [...]` entry is deleted, because the head would look like a
/// plain module name.
///
/// Answers with the DIRECTORY rather than a `Bool`, and the caller is why:
/// the undeclared-dependency hint has to name a path the user can paste
/// into their manifest, and the only path that is certainly right is one
/// derived from where the mote actually is. A `Bool` here is what made that
/// hint hardcode `../<name>`, which is right for the sibling layout and
/// wrong for the flat one (where the manifest value is `foo`) -- both cases
/// are asserted end to end in that same configuration, and both are rows
/// over `undeclared_mote_error` below.
#[partial]
def mote_named_at (name : String) : IO (Option String) := do {
    let direct <- file_exists (Path.path (String.concat name "/mote.toml"));
    if direct then return (Option.some name)
    else do {
        let nested : String := String.concat "motes/" name;
        let nested_exists <- file_exists (Path.path (String.concat nested "/mote.toml"));
        if nested_exists then return (Option.some nested)
        else do {
            let sibling : String := String.concat "../" name;
            let sibling_exists <- file_exists (Path.path (String.concat sibling "/mote.toml"));
            if sibling_exists then return (Option.some sibling) else return Option.none
        }
    }
}

/// Does this machine's toolchain root PROVIDE a mote called `name`?
///
/// A fourth category beside the ambient trio, the declared dependencies and
/// the motes visible from the working directory -- and the one that matters
/// for a mote in its own repository, which has no checkout and may declare
/// nothing. Resolution does not need a declaration for these (the toolchain
/// tier of `resolve_installed_or_manifest` answers by NAME, which is what
/// `use std::map` in an external repo relies on), so the declared-dependency
/// gate must not demand one either: its hint says `path = "../<name>"`,
/// and a path pointing INTO the toolchain is precisely the dependency this
/// whole route exists to remove.
///
/// Not folded into `is_ambient_mote`: that predicate is about the
/// LANGUAGE's own trio, which is fixed and name-matched. This one is about
/// one machine's install and is answered by the filesystem.
///
/// Split as a pure decision over the root, then the env read, for the same
/// reason `Mote.toolchain_candidates` is: there is no `set_env` native, so
/// only the half that does not read the environment can be rowed in-process.
def installed_mote_at (root : Option String) (name : String) : IO Bool := do {
    let found <- toolchain_first_existing root [name, "mote.toml"];
    match found {
        Option.some _ => return true,
        Option.none => return false
    }
}

def is_installed_mote (name : String) : IO Bool := do {
    let root <- Mote.toolchain_root;
    installed_mote_at root name
}

#[partial]
def validate_declared_deps (infos : List ModuleInfo) : IO (List String) :=
    match infos {
        List.empty => do { return List.empty },
        List.cons info rest => do {
            let here : List String <- validate_module_deps info;
            // Names before the mote half's own reports, for the same reason
            // `validate_module_deps` puts spellings before declaredness: a
            // brace entry that cannot bind is the more fundamental fix, and
            // `gate_declared_deps` reports only the first error it is handed.
            let names : List String := validate_use_names infos info;
            let later : List String <- validate_declared_deps rest;
            return (List.append names (List.append here later))
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
            let uses : List ModulePath := extract_use_decls info.decl_list;
            let mote <- mote_of_module info;
            // Checked for EVERY file, script mode included: a one-off has no
            // manifest to declare a mote in, so a bare `use io` is both most
            // likely there and least visible. `gate_declared_deps` reports
            // only the first error, and a re-spelled `use` is the more
            // fundamental fix, so the spellings come first.
            let spellings <- check_use_spellings mote info uses;
            match mote {
                // Script mode -- a file outside any mote and with no inline
                // annotation (a one-off). Nothing declared anything, so
                // nothing is undeclared.
                Option.none => return spellings,
                Option.some m => do {
                    let declared <- check_uses_declared m info uses;
                    return (List.append spellings declared)
                }
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
                // ...nor about a mote the toolchain provides: the install
                // pins it, resolution finds it by name, and the hint below
                // would ask for a `path` into the install.
                let installed <- is_installed_mote head;
                if installed then return List.empty
                else do {
                    // Only complain about names that really are motes -- a
                    // head segment naming nothing is an ordinary
                    // module-not-found, reported where it happens. The
                    // WHERE is carried into the message: it is the one
                    // thing that turns the hint's path into the right
                    // path (see `dep_path_hint`).
                    let found <- mote_named_at head;
                    match found {
                        Option.none => return List.empty,
                        Option.some found_dir => return [undeclared_mote_error m info u head found_dir]
                    }
                }
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

// ─── A `use` brace list must name declarations that exist ────────────
//
// `use M {n}` binds `n` only when `M` declares a top-level name that IS
// `n`, matched against the declaration's own SPELLED name. A dotted def is
// declared as one identifier holding a dot (`pub def List.length`), so the
// brace item names the same spelling (`{List.length}`, via
// `use_brace_item_name_dotted`, `lang/parser.mo`) and the bare tail
// `{length}` names nothing. Nothing used to say so: the entry was a silent
// no-op whose failure surfaced later as `unknown variable` at the CALL
// site, if at all.
//
// Checked at load, where the whole `List ModuleInfo` is already in hand:
// the target module is parsed, so this needs no extra I/O and no second
// parse. `{*}` and `{}` are deliberately unchanged -- this is a
// resolution rule, not import-list minimalism.

#[partial]
def validate_use_names (infos : List ModuleInfo) (info : ModuleInfo) : List String :=
    check_use_filters infos info (extract_use_filters info.decl_list)

#[partial]
def check_use_filters (infos : List ModuleInfo) (info : ModuleInfo) (uses : List (Pair ModulePath UseFilter)) : List String :=
    match uses {
        List.empty => List.empty,
        List.cons u rest =>
            match u {
                Pair.pair path filter =>
                    list_append (check_one_use_filter infos info path filter) (check_use_filters infos info rest)
            }
    }

def check_one_use_filter (infos : List ModuleInfo) (info : ModuleInfo) (path : ModulePath) (filter : UseFilter) : List String :=
    match filter {
        // Bare `use M` (deprecated, and never named anything) and an
        // explicit empty list both import no names.
        UseFilter.use_bare => List.empty,
        UseFilter.use_items items =>
            match find_module_by_path infos path {
                // A path that resolves to no LOADED module is an ordinary
                // module-not-found (or a `lib::`-aliased path, which the
                // alias pass rewrites later); the loader reports that, and
                // guessing here would report it twice.
                Option.none => List.empty,
                Option.some target =>
                    check_use_items infos info path (declared_names_of target.decl_list List.empty) items
            }
    }

#[partial]
def check_use_items (infos : List ModuleInfo) (info : ModuleInfo) (path : ModulePath) (names : List String) (items : List UseItem) : List String :=
    match items {
        List.empty => List.empty,
        List.cons item rest =>
            list_append (check_one_use_item infos info path names item) (check_use_items infos info path names rest)
    }

def check_one_use_item (infos : List ModuleInfo) (info : ModuleInfo) (path : ModulePath) (names : List String) (item : UseItem) : List String :=
    match item {
        UseItem.use_name n => check_one_use_name info path names n,
        // The name half is what has to exist; the alias is the caller's
        // own choice of spelling and is never checked against `M`.
        UseItem.use_rename n _alias => check_one_use_name info path names n,
        UseItem.use_glob => List.empty,
        UseItem.use_sub n sub => check_use_sub infos info path n sub,
        UseItem.use_sub_rename n _alias sub => check_use_sub infos info path n sub
    }

/// `use foo { bar { baz } }`: the sub-list is checked against the module
/// at the EXTENDED path, not against `foo`.
#[partial]
def check_use_sub (infos : List ModuleInfo) (info : ModuleInfo) (path : ModulePath) (n : Identifier) (items : List UseItem) : List String :=
    let sub_path : ModulePath := use_sub_path path n in
    match find_module_by_path infos sub_path {
        Option.none => List.empty,
        Option.some target =>
            check_use_items infos info sub_path (declared_names_of target.decl_list List.empty) items
    }

/// `lang/scope.mo`'s `path_extend`, which is not exported -- a
/// `ModulePath` plus one segment, the path a `use_sub` item addresses.
def use_sub_path (path : ModulePath) (n : Identifier) : ModulePath :=
    match path {
        ModulePath.mp ids => ModulePath.mp (list_append ids (List.cons n List.empty))
    }

def check_one_use_name (info : ModuleInfo) (path : ModulePath) (names : List String) (n : Identifier) : List String :=
    let name : String := identifier_to_string n in
    if List.contains_by String.beq name names
    then List.empty
    else List.cons (unknown_use_name_error info path name (dotted_spelling_of names name)) List.empty

/// The declared name `n` is the TAIL of, if the module declares one --
/// `length` is the tail of `List.length`. This is what turns the error
/// every dotted import produces into one that names the spelling the user
/// actually wanted, rather than only saying that what they wrote is wrong.
#[partial]
def dotted_spelling_of (names : List String) (n : String) : Option String :=
    match names {
        List.empty => Option.none,
        List.cons x rest =>
            if String.beq (tail_after_last_dot x) n then Option.some x else dotted_spelling_of rest n
    }

/// Everything after the LAST `.`, or `""` when there is none.
/// `init::string` exports no `split`/`index_of`, so this scans with
/// `String.slice`; identifiers and def names are short, and this only runs
/// on the error path.
#[partial]
def tail_after_last_dot_go (s : String) (len : I64) (i : I64) (last : I64) : I64 :=
    if I64.lt len i
    then last
    else tail_after_last_dot_go s len (I64.add i 1)
        (if String.beq (String.slice s i 1) "." then i else last)

def tail_after_last_dot (s : String) : String :=
    let len : I64 := String.length s in
    let last : I64 := tail_after_last_dot_go s len 0 (-1) in
    if I64.lt last 0 then "" else String.drop (I64.add last 1) s

def unknown_use_name_error (info : ModuleInfo) (path : ModulePath) (n : String) (dotted : Option String) : String :=
    let p : String := module_path_to_string path in
    String.concat_all [
        "error: `", p, "` declares no `", n, "`\n",
        "  `use ", p, " {", n, "}` in ", info.file_path, "\n",
        use_name_hint p n dotted
    ]

/// The advice half of the message above. A brace item is matched against a
/// declaration's full spelled name, so the fix for a bare tail is to write
/// the dotted spelling (`List.length`), and the fix for a name the module
/// declares nowhere is to keep the module loaded with `{}` and reach the
/// name qualified. `use_name_hint`'s Rust twin in
/// `core/src/term/module.rs` says the same thing in the same words -- CI
/// runs both over the corpus.
def use_name_hint (p : String) (n : String) (dotted : Option String) : String :=
    match dotted {
        Option.some d => String.concat_all [
            "  hint: `", d, "` is declared there — a brace item is matched against a declaration's full spelled name, not its last segment\n",
            "  hint: write `use ", p, " {", d, "}`\n"
        ],
        Option.none => String.concat_all [
            "  hint: a brace item names a top-level declaration exactly; nothing in `", p, "` is declared as `", n, "`\n",
            "  hint: if the module is needed only for its qualified names, write `use ", p, " {}`\n"
        ]
    }

// ─── A `use` must name a mote, or `lib` ──────────────────────────────
//
// A `use` path's first segment names a MOTE -- `init`, `std`, `runtime`,
// any `motes/*` -- or the reserved alias `lib`, which is the importing
// mote's own. Nothing else. A bare `use io` is a path relative to the
// importing FILE, so which module it names depends on where that file
// sits: `init/src/io.mo` and `std/src/io.mo` are spelled the same bare
// way, and a file in `std/src/` resolves the second while the Rust host
// resolves the first. Outside this checkout the bare form resolves
// nothing at all, every candidate tier being a working-directory literal.

/// The segments of a `use` path, as plain strings.
def use_segment_names (u : ModulePath) : List String :=
    match u { ModulePath.mp ids => List.map identifier_to_string ids }

/// Whether a `use` path names the ambient prelude -- bare `prelude`, or
/// `init::prelude`, its one other spelling.
///
/// The prelude is seeded into EVERY file's closure by the loader, so an
/// import of it is redundant by construction. It is also the one module
/// whose NAME is not its FILE name, so an explicit path to it is a second
/// way to name `init/src/prelude.mo`.
def use_names_ambient_prelude (u : ModulePath) : Bool :=
    match use_segment_names u {
        List.empty => false,
        List.cons hd rest =>
            match rest {
                List.empty => String.beq hd "prelude",
                List.cons hd2 rest2 =>
                    match rest2 {
                        List.empty => String.beq hd "init" && String.beq hd2 "prelude",
                        List.cons _ _ => false
                    }
            }
    }

/// Whether a bare name is a MOTE -- the only thing a one-segment `use` may
/// name, besides `lib`.
///
/// Probed, not looked up: no side keeps a registry of mote names, and
/// neither needs one. `MoteManifest.declares` answers for the file's own
/// mote and its declared dependencies; `mote_named_at` and
/// `is_installed_mote` ask the filesystem the way resolution itself does.
/// The Rust host asks the manifest half of the same question
/// (`validate_use_qualification`, core/src/term/module.rs) so the two
/// compilers cannot drift on what a source means.
#[partial]
def head_names_mote (m : Option MoteManifest) (head : String) : IO Bool := do {
    if head_names_mote_declared m head then return true
    else do {
        let installed <- is_installed_mote head;
        if installed then return true
        else do {
            let found <- mote_named_at head;
            match found { Option.none => return false, Option.some _ => return true }
        }
    }
}

/// The manifest half of `head_names_mote`, split out because `#[test]` defs
/// are pure and cannot touch the filesystem -- the same split, for the same
/// reason, as `installed_mote_at` / `is_installed_mote`.
def head_names_mote_declared (m : Option MoteManifest) (head : String) : Bool :=
    if is_ambient_mote head then true
    else match m {
        Option.none => false,
        Option.some man => MoteManifest.declares man head
    }

#[partial]
def check_use_spellings (m : Option MoteManifest) (info : ModuleInfo) (uses : List ModulePath) : IO (List String) :=
    match uses {
        List.empty => do { return List.empty },
        List.cons u rest => do {
            let here <- check_one_use_spelling m info u;
            let later <- check_use_spellings m info rest;
            return (List.append here later)
        }
    }

#[partial]
def check_one_use_spelling (m : Option MoteManifest) (info : ModuleInfo) (u : ModulePath) : IO (List String) := do {
    if use_names_ambient_prelude u then return [prelude_import_error info u]
    else match use_segment_names u {
        List.empty => return List.empty,
        List.cons head rest =>
            match rest {
                // More than one segment: the head is a mote reference, which
                // `check_one_use_declared` already validates.
                List.cons _ _ => return List.empty,
                List.empty => do {
                    if String.beq head "lib" then return List.empty
                    else do {
                        let known <- head_names_mote m head;
                        if known then return List.empty
                        else do {
                            let owner <- bare_use_owner info.file_path head;
                            return [bare_use_error info u owner]
                        }
                    }
                }
            }
    }
}

/// The mote that owns the module a bare name resolves to, so the hint can
/// name the line to write rather than describe the rule.
///
/// Probed with resolution's own precedence: the importing file's directory
/// first (`resolve_module_file`'s `relative_path` tier), then the working
/// directory's `init`/`std`/`lang`. `none` when no candidate exists at all
/// -- the bare name resolves nowhere, and a generic hint is better than an
/// invented owner.
#[partial]
def bare_use_owner (importer : String) (head : String) : IO (Option String) := do {
    let beside : String := raw_path_join (extract_directory importer) (String.concat head ".mo");
    let here <- IO.file_exists (Path.path beside);
    if here then owning_mote_name beside
    else bare_use_owner_cwd head
}

#[partial]
def bare_use_owner_cwd (head : String) : IO (Option String) := do {
    let f : String := String.concat head ".mo";
    let i <- IO.file_exists (Path.path (raw_path_join "init/src" f));
    if i then return (Option.some "init")
    else do {
        let s <- IO.file_exists (Path.path (raw_path_join "std/src" f));
        if s then return (Option.some "std")
        else do {
            let l <- IO.file_exists (Path.path (raw_path_join "lang/src" f));
            if l then return (Option.some "lang")
            else return Option.none
        }
    }
}

#[partial]
def owning_mote_name (file : String) : IO (Option String) := do {
    let m <- Mote.discover (extract_directory file);
    match m {
        Option.none => return Option.none,
        Option.some man => return (Option.some man.name)
    }
}

/// The message for a one-segment `use` that names a module rather than a
/// mote.
def bare_use_error (info : ModuleInfo) (u : ModulePath) (owner : Option String) : String :=
    String.concat_all [
        "error: `use ", module_path_to_string u, "` does not name a mote\n",
        "  `use ", module_path_to_string u, "` in ", info.file_path,
        " is a module path relative to the importing file, so which module it names depends on where that file sits\n",
        "  hint: ", bare_use_hint (module_path_to_string u) owner,
    ]

def bare_use_hint (head : String) (owner : Option String) : String :=
    match owner {
        Option.some o =>
            String.concat_all [
                "write `use ", o, "::", head, "` for that module, or `use lib::", head,
                "` for this mote's own"
            ],
        Option.none =>
            String.concat_all [
                "name the mote that owns it (`use <mote>::", head,
                "`), or write `use lib::", head, "` for this mote's own"
            ]
    }

// ─── The rule's own tests ───────────────────────────────────────────
//
// The Rust host carries the same six cases (core/src/term/module/test.rs).
// Both runtimes enforce the rule, so a divergence here would mean a source
// means one thing under `cargo run` and another under the compiler this
// project ships. The legal half matters as much as the illegal one: a rule
// that rejected everything would pass a rejection test.

/// A `ModuleInfo` for a source string, in script mode -- no file is read
/// and no mote is discovered, so `validate_module_deps` reports the `use`
/// spellings and nothing else.
def probe_module_info (source : String) : ModuleInfo :=
    match try_parse_decls source {
        Option.some decls => ModuleInfo.mk (ModulePath.mp [Identifier.id "probe"]) "probe.mo" decls,
        Option.none => ModuleInfo.mk (ModulePath.mp [Identifier.id "probe"]) "probe.mo" List.empty
    }

#[test]
def test_use_head_mote_of_a_qualified_path_is_the_mote : Bool :=
    match use_head_mote (ModulePath.mp [Identifier.id "init", Identifier.id "io"]) {
        Option.some h => String.beq h "init",
        Option.none => false
    }

#[test]
def test_use_head_mote_of_a_bare_name_is_none : Bool :=
    match use_head_mote (ModulePath.mp [Identifier.id "io"]) {
        Option.none => true,
        Option.some _ => false
    }

#[test]
def test_use_names_the_ambient_prelude_in_both_spellings : Bool :=
    use_names_ambient_prelude (ModulePath.mp [Identifier.id "prelude"]) &&
    use_names_ambient_prelude (ModulePath.mp [Identifier.id "init", Identifier.id "prelude"]) &&
    Bool.not (use_names_ambient_prelude (ModulePath.mp [Identifier.id "init", Identifier.id "io"]))

#[test]
def test_bare_use_hint_names_the_owning_mote : Bool :=
    String.beq (bare_use_hint "io" (Option.some "init"))
        "write `use init::io` for that module, or `use lib::io` for this mote's own"

#[test]
def test_bare_use_of_a_module_is_rejected : IO Bool := do {
    let errs <- validate_module_deps (probe_module_info "use io {IO}");
    return (Bool.not (List.is_empty errs))
}

#[test]
def test_use_of_the_prelude_is_rejected_in_both_spellings : IO Bool := do {
    let bare <- validate_module_deps (probe_module_info "use prelude");
    let qualified <- validate_module_deps (probe_module_info "use init::prelude");
    return (Bool.not (List.is_empty bare) && Bool.not (List.is_empty qualified))
}

#[test]
def test_use_of_a_mote_and_lib_is_accepted : IO Bool := do {
    let cross <- validate_module_deps (probe_module_info "use init::io {IO}");
    let sibling <- validate_module_deps (probe_module_info "use std::io {IO}");
    let own <- validate_module_deps (probe_module_info "use lib {List}");
    return (List.is_empty cross && List.is_empty sibling && List.is_empty own)
}

// ─── The `use` brace-name check (validate_use_names) ─────────────────
//
// `use M {n}` binds `n` only when `M` declares a top-level name that IS
// `n`, checked on the DECLARATION. These drive `validate_use_names`
// through a two-module world parsed from text, which is what the loader
// hands it: `validate_declared_deps` gives it every loaded module and the
// one being validated.

/// Every declaration kind a brace list can name, at `probe::list`, plus
/// the pair that keeps the comparison honest: a bare `length` sits
/// ALONGSIDE the dotted `List.length`, so a check that compared tails
/// instead of full names would accept both.
def use_names_target : String := String.concat_all [
    "def List.length : I64 := 1\n",
    "def length : I64 := 2\n",
    "def f : I64 := 3\n",
    "type T {\n  mk (u : Unit)\n}\n",
    "struct S { x : I64 }\n",
    "class C A { def c (a : A) : A }\n",
    "instance MyInst : C String {\n  def c (a : String) : String := a\n}\n",
    "defmacro dm T := decls { }\n"
]

/// Parse each `(path, source)` target into a `ModuleInfo`, or `none` if
/// any of them fails -- so a typo in a probe's own source is reported by
/// the helper rather than silently contributing no names (which would let
/// every rejection test below pass on a parse failure instead of on the
/// rule).
#[partial]
def probe_targets (targets : List (Pair ModulePath String)) (acc : List ModuleInfo) : Option (List ModuleInfo) :=
    match targets {
        List.empty => Option.some acc,
        List.cons t rest =>
            match t {
                Pair.pair path src =>
                    match try_parse_decls src {
                        Option.some decls => probe_targets rest (List.cons (ModuleInfo.mk path "target.mo" decls) acc),
                        Option.none => Option.none
                    }
            }
    }

/// The error messages `validate_use_names` produces for a world holding
/// `targets` plus `importing_src` as the file that imports one of them.
/// Empty means the check passed.
def probe_use_names (targets : List (Pair ModulePath String)) (importing_src : String) : List String :=
    match probe_targets targets List.empty {
        Option.none => [ "the probe target did not parse" ],
        Option.some targets =>
            let importing : ModuleInfo := probe_module_info importing_src in
            validate_use_names (List.cons importing targets) importing
    }

/// The one-target shorthands. Spelled with `Pair.pair`/`List.cons` rather
/// than `[(p, s)]`: a literal in argument position is exactly the shape
/// AGENTS.md's bare-struct-literal trap covers, and there is nothing to
/// gain here by testing it.
def probe_list_names (target_src : String) (importing_src : String) : List String :=
    let path : ModulePath := ModulePath.mp [Identifier.id "probe", Identifier.id "list"] in
    let target : Pair ModulePath String := Pair.pair path target_src in
    probe_use_names (List.cons target List.empty) importing_src

/// The headline case, and the one the corpus was full of. `length` is not
/// a declaration of `probe::list` -- `List.length` is -- so the entry
/// binds nothing, and is now an error at the `use` line instead of a
/// silent no-op whose failure surfaced later as `unknown variable` at the
/// call site.
#[test]
def test_a_dotted_def_cannot_be_imported_by_name : Bool :=
    match probe_list_names "def List.length : I64 := 1" "use probe::list {length}" {
        List.cons msg rest =>
            Bool.and (List.is_empty rest)
                (String.starts_with "error: `probe::list` declares no `length`" msg),
        List.empty => false
    }

/// A typo has no dotted sibling to point at, so the hint has to fall back
/// to the module-load spelling rather than claim a dotted name exists.
#[test]
def test_a_use_name_declared_nowhere_is_rejected : Bool :=
    match probe_list_names "def length : I64 := 1" "use probe::list {lenght}" {
        List.cons msg rest =>
            Bool.and (List.is_empty rest)
                (String.starts_with "error: `probe::list` declares no `lenght`" msg),
        List.empty => false
    }

/// The half a rule that rejected everything would pass without: every
/// declaration kind a brace list names -- def, type, a constructor,
/// struct, class, instance, defmacro -- plus the bare `length` that sits
/// next to `List.length` and would be accepted by a tail comparison.
#[test]
def test_every_declaration_kind_can_be_imported_by_its_own_name : Bool :=
    List.is_empty (probe_list_names use_names_target "use probe::list {f, T, mk, S, C, MyInst, dm, length}")

/// ...and its mirror, which is the subtle half: `mk` here comes from a
/// `STRUCT`, whose synthesized constructor is not a declared name on
/// either compiler (`struct` is its own decl kind, and only a `type`
/// names constructors). A rule that walked every inductive's constructors
/// would accept this.
#[test]
def test_a_structs_synthesized_constructor_is_not_importable : Bool :=
    Bool.not (List.is_empty (probe_list_names "struct S { x : I64 }" "use probe::list {mk}"))

/// `{*}` and `{}` are deliberately unchanged: this is a resolution rule,
/// not import-list minimalism. A bare `use` names nothing either.
#[test]
def test_a_glob_an_empty_list_and_a_bare_use_are_accepted : Bool :=
    List.is_empty (probe_list_names use_names_target "use probe::list {*}") &&
    List.is_empty (probe_list_names use_names_target "use probe::list {}") &&
    List.is_empty (probe_list_names use_names_target "use probe::list")

/// A rename is checked against the name it renames FROM. The alias is the
/// importer's own choice of spelling and is never looked up in the target.
#[test]
def test_a_rename_checks_the_name_not_the_alias : Bool :=
    List.is_empty (probe_list_names use_names_target "use probe::list {f as g}") &&
    Bool.not (List.is_empty (probe_list_names use_names_target "use probe::list {g as f}"))

/// A sub-list is checked against the module at the EXTENDED path, not the
/// module that holds it. The two modules carry DIFFERENT names (`g` on
/// `probe::outer`, `f` on `probe::outer::inner`) so a check that used the
/// outer path would accept `inner {g}` and fail here.
#[test]
def test_a_sub_list_is_checked_against_the_extended_path : Bool :=
    let outer_path : ModulePath := ModulePath.mp [Identifier.id "probe", Identifier.id "outer"] in
    let inner_path : ModulePath := ModulePath.mp [Identifier.id "probe", Identifier.id "outer", Identifier.id "inner"] in
    let outer : Pair ModulePath String := Pair.pair outer_path "def g : I64 := 1" in
    let inner : Pair ModulePath String := Pair.pair inner_path "def f : I64 := 1" in
    let world : List (Pair ModulePath String) := [outer, inner] in
    List.is_empty (probe_use_names world "use probe::outer {inner {f}}") &&
    Bool.not (List.is_empty (probe_use_names world "use probe::outer {inner {g}}"))

/// A path that resolves to no LOADED module is left alone: that is an
/// ordinary module-not-found (or a `lib::`-aliased path, rewritten
/// later), which the loader reports where it happens. Reporting it here
/// would say it twice, and with the wrong reason.
#[test]
def test_a_use_of_an_unloaded_module_is_left_alone : Bool :=
    List.is_empty (probe_list_names use_names_target "use probe::absent {whatever}")

/// The message for an explicit import of the prelude, which is ambient.
///
/// The check sits on the DECLARATION and never on resolution: the loader
/// seeds `prelude` into every file's closure, and that alias is
/// load-bearing -- `MoteManifest.dep_dir_of`'s self arm (lang/src/mote.mo)
/// is what makes the prelude of the mote `init` reachable from inside
/// `init/` at all.
def prelude_import_error (info : ModuleInfo) (u : ModulePath) : String :=
    String.concat_all [
        "error: `use ", module_path_to_string u, "` names the prelude, which is ambient\n",
        "  every file already sees `prelude` -- the loader seeds it into each module's closure, ", info.file_path, " included\n",
        "  hint: delete the `use ", module_path_to_string u, "` line",
    ]

/// The `[dependencies.<head>] path` value to suggest, written relative to
/// the directory the MANIFEST lives in (`mote_dir`) -- which is what a
/// manifest's paths are relative to, and the only reason this is a
/// computation rather than the literal it used to be.
///
/// `mote_dir` is the manifest's directory as `Mote.discover` spells it
/// (working-directory-relative), and `found_dir` is where `mote_named_at`
/// found the mote -- so the answer is the mote's own spelling with one
/// `../` per real segment of `mote_dir` in front of it:
///
///   * `("", "foo")` -> `foo` -- the mote beside the working directory,
///     which is where the bare-and-flat layout puts it;
///   * `("greet", "foo")` -> `../foo` -- the sibling convention this repo
///     itself uses (`std/mote.toml`'s `path = "../init"`), and the one the
///     hardcoded answer happened to be right for;
///   * `("greet/src", "motes/foo")` -> `../../motes/foo`;
///   * `(".", "foo")` -> `foo` -- a `.` names no level, so it contributes no
///     `../` (a bare `monad check` reaches the manifest as `.` in some
///     paths, `""` in others).
///
/// `none` for the two shapes the two strings cannot be related across:
/// a `..` segment in `mote_dir`, and an absolute `mote_dir` (which is
/// reachable -- `monad check /abs/src/lib.mo` discovers an absolute manifest
/// while the mote probe beside it is working-directory-relative). Both are
/// a formality rather than a live path: `Mote.discover` walks UP from the
/// file's own directory by stripping components, so its answer is a chain
/// of real directory names, `""` or a `.` -- never `..`. The caller says
/// where the mote is in that case instead of inventing a path, because a
/// wrong `path` value is worse than none: it sends the user somewhere that
/// looks plausible and opens nothing.
def dep_path_hint (mote_dir : String) (found_dir : String) : Option String :=
    if String.starts_with "/" mote_dir then Option.none
    else dep_path_hint_go (path_segments_go mote_dir 0 0 List.empty) found_dir

def dep_path_hint_go (segs : List String) (found_dir : String) : Option String :=
    match segs {
        List.empty => Option.some found_dir,
        List.cons s rest =>
            if String.beq s "." then dep_path_hint_go rest found_dir
            else if String.beq s ".." then Option.none
            else match dep_path_hint_go rest found_dir {
                Option.none => Option.none,
                Option.some inner => Option.some (raw_path_join ".." inner)
            }
    }

/// The hint's `path` clause, with the no-path form spelled out as a
/// placeholder rather than dropped: a hint that stops after
/// `[dependencies.foo]` reads as if the entry needed no path at all.
def undeclared_mote_path_clause (mote_dir : String) (found_dir : String) : String :=
    match dep_path_hint mote_dir found_dir {
        Option.some p => String.concat "path = \"" (String.concat p "\""),
        Option.none => String.concat "path = \"<path to " (String.concat found_dir ">\"")
    }

/// The undeclared-dependency message, with BOTH paths computed from where
/// things actually are.
///
/// What it said before: a hardcoded `path = "../<head>"`, and the manifest
/// as `m.dir ++ "/mote.toml"`. The second is broken outright when the
/// manifest is the working directory's own (`m.dir` is `""`, so it rendered
/// `/mote.toml`); the first is broken whenever the mote is beside the
/// working directory rather than beside the manifest, which is the flat
/// layout `mote_named_at`'s own probe finds -- there the value a manifest
/// needs is `foo`, and `../foo` resolves one directory too high. The flat
/// layout and the sibling one are both driven end to end by
/// `scripts/check-external-mote.sh`'s configuration 6, and both are rows
/// over this def (`test_undeclared_mote_error_names_working_directory_paths`,
/// `..._names_a_nested_manifest`).
///
/// `found_dir` doubles as the second line's evidence -- "which is at `foo`"
/// is what tells a reader which of the two `foo` directories the path is
/// supposed to point at. It is spelled with its delimiters on BOTH sides
/// because the missing one is exactly how this line first shipped: a
/// backtick opened around the mote name in the first clause and never
/// closed, so the line read "which is there at foo" followed by a stray
/// backtick.
def undeclared_mote_error (m : MoteManifest) (info : ModuleInfo) (u : ModulePath)
    (head : String) (found_dir : String) : String :=
    String.concat_all [
        "error: mote `", head, "` is not a declared dependency of `", m.name, "`\n",
        "  `use ", module_path_to_string u, "` in ", info.file_path,
        " requires mote `", head, "`, which is at `", found_dir, "`\n",
        "  hint: add [dependencies.", head, "] ", undeclared_mote_path_clause m.dir found_dir,
        " to ", raw_path_join m.dir "mote.toml",
    ]

/// Turn the first undeclared-mote error, if any, into the load's own
/// failure. One error, not all of them: the loader's `Result` carries a
/// single message, and the first one names a real manifest fix.
#[partial]
def gate_declared_deps (r : Result String LoadedModules) : IO (Result String LoadedModules) := do {
    match r {
        Result.err e => return (Result.err e),
        Result.ok loaded => do {
            let errs <- validate_declared_deps (get_loaded_all loaded);
            match errs {
                List.empty => return (Result.ok loaded),
                List.cons e _ => return (Result.err e)
            }
        }
    }
}

// ─── Mote targets (package-system.md 2a, `[lib]`/`[[bin]]`) ──────────
//
// Every mote must have at least one target that is actually there. The model
// in `lang/mote.mo` records where a target WOULD be -- `lib_path` is
// `src/lib.mo` when the manifest declares no `[lib] path`, and a manifest
// with no bin table still gets one `src/main.mo` target -- because
// `Mote.manifest_of_table` is pure and cannot probe the filesystem. This is
// the half that probes, so a mote whose library root was never written is
// reported as the missing file it is rather than as whatever name happens to
// go missing during elaboration.

/// Does at least one of this mote's targets exist on disk?
#[partial]
def mote_has_a_target (m : MoteManifest) : IO Bool := do {
    match m.lib_path {
        Option.none => first_bin_on_disk m.bins,
        Option.some p => do {
            let there <- file_exists (Path.path p);
            if there then return true else first_bin_on_disk m.bins
        }
    }
}

/// The first of `bs` whose `path` is a file; `false` when there is none.
#[partial]
def first_bin_on_disk (bs : List BinTarget) : IO Bool := do {
    match bs {
        List.empty => return false,
        List.cons b rest => do {
            let there <- file_exists (Path.path (BinTarget.target_path b));
            if there then return true else first_bin_on_disk rest
        }
    }
}

def option_target_paths (p : Option String) : List String :=
    match p { Option.none => List.empty, Option.some s => List.cons s List.empty }

def bin_target_paths (bs : List BinTarget) : List String :=
    match bs {
        List.empty => List.empty,
        List.cons b rest => List.cons (BinTarget.target_path b) (bin_target_paths rest)
    }

/// Every path the gate tried for this mote, in the order it tried them.
def mote_target_paths (m : MoteManifest) : List String :=
    List.append (option_target_paths m.lib_path) (bin_target_paths m.bins)

/// The target-less message. Which paths were tried depends on the manifest,
/// so they are NAMED: "none of these is a file" is only actionable if the
/// reader can see which files were tried.
def targetless_mote_error (m : MoteManifest) : String :=
    let named : String :=
        List.intercalate " and "
            (List.map (fn (p : String) => String.concat "`" (String.concat p "`"))
                (mote_target_paths m)) in
    String.concat_all [
        "error: mote `", m.name, "` has no target that exists\n",
        "  ", raw_path_join m.dir "mote.toml", " names ", named,
        " as its targets, and none of those is a file\n",
        "  hint: create `", mote_lib_file_of m,
        "` for a library mote, or add a [[bin]] table naming the file a binary mote builds",
    ]

/// `acc` with `m` added, unless a mote rooted at the same directory is
/// already there. Directory rather than name: `dir` is what every target path
/// is spelled from, and two spellings of one directory (`""` and `"."`) name
/// the same tree.
def push_mote (m : MoteManifest) (acc : List MoteManifest) : List MoteManifest :=
    if List.any (fn (x : MoteManifest) => String.beq x.dir m.dir) acc
    then acc
    else List.cons m acc

def push_maybe (found : Option MoteManifest) (acc : List MoteManifest) : List MoteManifest :=
    match found { Option.none => acc, Option.some m => push_mote m acc }

/// Every mote named by `dirs`, consed onto `acc`.
#[partial]
def motes_of_dirs (dirs : List String) (acc : List MoteManifest) : IO (List MoteManifest) := do {
    match dirs {
        List.empty => return acc,
        List.cons d rest => do {
            let found <- Mote.discover d;
            let next : List MoteManifest := push_maybe found acc;
            motes_of_dirs rest next
        }
    }
}

/// Every mote owning one of the loaded modules, consed onto `acc`.
#[partial]
def motes_of_infos (infos : List ModuleInfo) (acc : List MoteManifest) : IO (List MoteManifest) := do {
    match infos {
        List.empty => return acc,
        List.cons info rest => do {
            let found <- Mote.discover (extract_directory info.file_path);
            let next : List MoteManifest := push_maybe found acc;
            motes_of_infos rest next
        }
    }
}

/// The motes `gate_mote_targets` checks: the workspace's declared members,
/// then the motes owning this load's modules.
///
/// BOTH halves are load-bearing, and each covers the other's hole. Members
/// alone miss a standalone mote: `Mote.workspace_members` answers
/// `List.empty` for a manifest with no `[workspace] members` -- a workspace
/// of one, which is exactly the external fixture
/// `scripts/check-external-mote.sh` builds -- so the gate would be silently
/// absent there. Loaded modules alone miss the motes the compiler never
/// imports: this closure reaches twelve of the twenty-one members -- `init`,
/// `std`, `lang`, `cli`, `llvm`, `runtime`, `build`, `lsp`, `toolkit`, `json`,
/// `parsec` and `toml` (`json` by way of `cli` -> `lsp::server` ->
/// `toolkit::jsonrpc`) -- and reaches neither `slow_tests`, `bench`, `proofs`,
/// `motes/demo`, `motes/example`, `motes/ffi_example`, `motes/http`,
/// `motes/moon` nor `motes/moose`. Nothing in the tree writes `use
/// slow_tests` at all.
///
/// Members come first and in manifest order, so the first error names the
/// first offender a reader would find in the root `mote.toml`. Both walks
/// cons, so the union is reversed once at the end.
///
/// Inline `#![mote { ... }]` motes are exempt by construction rather than by
/// an exemption list: an inline file's nearest `mote.toml` is the virtual
/// workspace root above it, which has no `[mote]`, so `Mote.discover` answers
/// `none` for its directory.
#[partial]
def mote_target_candidates (infos : List ModuleInfo) : IO (List MoteManifest) := do {
    let root <- find_workspace_root "" 32;
    let member_dirs : List String <- match root {
        Option.none => return List.empty,
        Option.some d => Mote.workspace_members d
    };
    let members <- motes_of_dirs member_dirs List.empty;
    let all <- motes_of_infos infos members;
    return (List.reverse all)
}

/// The first of `motes` that has no target on disk, if any.
#[partial]
def first_targetless_mote (motes : List MoteManifest) : IO (Option MoteManifest) := do {
    match motes {
        List.empty => return Option.none,
        List.cons m rest => do {
            let ok <- mote_has_a_target m;
            if ok then first_targetless_mote rest else return (Option.some m)
        }
    }
}

/// Turn the first target-less mote, if any, into the load's own failure. One
/// error, not all of them, matching `gate_declared_deps`.
#[partial]
def gate_mote_targets (r : Result String LoadedModules) : IO (Result String LoadedModules) := do {
    match r {
        Result.err e => return (Result.err e),
        Result.ok loaded => do {
            let motes <- mote_target_candidates (get_loaded_all loaded);
            let bad <- first_targetless_mote motes;
            match bad {
                Option.none => return (Result.ok loaded),
                Option.some m => return (Result.err (targetless_mote_error m))
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
    let mote <- mote_of_module info;
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

/// ONE line saying why, printed BEFORE the walk that says what.
///
/// The failure this exists for is the out-of-the-box one: an external mote
/// with no installed toolchain. `prelude` is seeded into every file's
/// closure, so if it does not resolve from the target file's own directory,
/// nothing that file `use`s will resolve either -- and the run that follows
/// opens with one `unresolved module:` line per module and then a wall of
/// `unknown variable` for the names those modules would have supplied. Both
/// name the SYMPTOM and neither names `monadup`, which is the thing the user
/// has to type. This line goes first so it is the one that gets read.
///
/// Fired on the RESOLUTION of `prelude` rather than on any missing module,
/// which is what makes it once per run instead of once per ambient miss
/// (the trio all miss together, four lines in the ordinary case) -- and it
/// is the same resolution `resolve_module_file` then performs for the walk,
/// not a second opinion about it.
///
/// Silent when `prelude` resolves. A run where prelude is found and some
/// other module is not has a named culprit already (`unresolved module:
/// <that one>`, plus whatever the manifest gate says about it), and is not
/// the case this is for.
def report_missing_toolchain (base_dir : String) : IO Unit := do {
    let found <- resolve_module_file base_dir prelude_module_path;
    match found {
        Option.some _ => return unit,
        Option.none => do {
            let root <- Mote.toolchain_root;
            let has_sources <- toolchain_has_ambient_sources root;
            match Mote.toolchain_missing_hint root has_sources {
                Option.none => return unit,
                Option.some line => println line
            }
        }
    }
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
///
/// `source` is the in-memory variant: `Option.some` takes the target
/// module's text from the caller instead of from disk, which is what a
/// language server needs for an editor buffer. Only the TARGET module is
/// affected -- the dependency walk below still reads real files. Every
/// non-server caller goes through the `Option.none` wrapper under this
/// one.
#[partial]
def load_file_modules_cached_go (file_path : String) (source : Option String) (cache : ModuleInfoCache) (verbose : Bool) : IO LoadedAndCache {
    let base_dir : String := extract_directory file_path;
    let module_name : String := module_name_from_path file_path;
    let mp : ModulePath := ModulePath.mp [Identifier.id module_name];
    module_line verbose module_name;
    let module <- load_target_module base_dir mp source;
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
                    // Said HERE, before the walk, and only when the ambient
                    // tier is unresolvable -- see
                    // `report_missing_toolchain`'s own note on why the one
                    // line that names `monadup` goes above the wall.
                    report_missing_toolchain main_base_dir;
                    let no_visited : List ModuleInfo := List.empty;
                    let no_visiting : List ModulePath := List.empty;
                    let walked <- collect_dep_module_infos (pending_from main_base_dir direct_deps_with_prelude) no_visiting no_visited cache verbose;
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

/// Read the target module from disk. The shape every non-server caller
/// wants; see `load_file_modules_cached_go` for the in-memory variant.
#[partial]
def load_file_modules_cached (file_path : String) (cache : ModuleInfoCache) (verbose : Bool) : IO LoadedAndCache :=
    load_file_modules_cached_go file_path Option.none cache verbose

/// Backwards-compatible wrapper: a standalone load with a fresh cache.
/// Every caller that isn't threading a whole-run cache uses this.
/// `verbose` forwards to the per-module trace (`std/src/log.mo`).
#[partial]
pub def load_file_modules (file_path : String) (verbose : Bool) : IO (Result String LoadedModules) := do {
    let r <- load_file_modules_cached file_path module_info_cache_empty verbose;
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
///
/// **`true` is not usable, and the reason is not cost.** Measured
/// 2026-09-23: it hands `check_module_with_scope` a multi-module decl
/// list, and that function also runs `check_termination_all` over
/// whatever it is given -- a pass whose own doc comment
/// (`lang/src/termination.mo`) states its precondition, one module's own
/// declarations before qualification, which is what makes its name-half
/// comparison sound. On a closure it reports 188 spurious
/// `No recursive parameters found for '__Dict_...'` diagnostics across 7
/// of 18 `slow_tests/typecheck_init_tests.mo` tests, and its
/// cubic-in-|defs| cost does not finish on this compiler's own ~2200-decl
/// closure. Making it usable means running the termination half once per
/// OWNING module rather than over the flat list -- the grouping exists
/// upstream as `flatten_module_decl_groups`' `List DeclGroup` and is
/// flattened away before the checker sees it. Nothing needs it today:
/// the sweep's check phase body-checks every `.mo` file in the corpus as
/// its own target, so every dependency is covered without this flag.
/// Full measurements and the code shape:
/// `plans/bootstrapping/check-deps-memory-blowup.md`.
/// The post-expansion scope, as its own def so the struct literal has a
/// declared return type to desugar against -- see the call site for why
/// neither an inline literal nor an annotated `let` inside the branch
/// works there.
#[partial]
def rebuild_target_scope (target_mp : ModulePath) (decls : List Decl) : Scope :=
    { module_id := target_mp, scope := build_scope_from_decls target_mp decls, parent := Option.none, incomplete_match_ok := false }

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

/// Read the target module from disk and elaborate it. The shape every
/// non-server caller wants; `check_file_cached` and `elaborate_loaded_
/// modules` both land here.
#[partial]
pub def elaborate_loaded_modules_cached (file_path : String) (check_deps : Bool) (cache : ModuleInfoCache) (verbose : Bool) : IO ElaboratedAndCache :=
    elaborate_loaded_modules_cached_go file_path check_deps Option.none cache verbose

/// The real body; `source` is threaded down to the target module's load,
/// so a language server can elaborate a buffer. `Option.none` is every
/// existing caller -- see the wrapper above.
#[partial]
def elaborate_loaded_modules_cached_go (file_path : String) (check_deps : Bool) (source : Option String) (cache : ModuleInfoCache) (verbose : Bool) : IO ElaboratedAndCache := do {
    let t_load : I64 <- Bench.now;
    let lc <- load_file_modules_cached_go file_path source cache verbose;
    // Manifest enforcement (package-system.md 2a/5d) before any elaboration
    // work: a mote reaching into one it never declared, or one that names no
    // target that exists, is a manifest error -- and saying so beats letting
    // it surface as whatever name happens to go missing first.
    //
    // Two sibling gates rather than one, each first-error-wins and each
    // independently revertable, so a bisect separates a bad dependency check
    // from a bad target check.
    let checked_deps <- gate_declared_deps lc.loaded;
    let loaded_result <- gate_mote_targets checked_deps;
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
            let scope : Scope := { module_id := target_mp, scope := scope_data, parent := Option.none, incomplete_match_ok := false };
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
    let r <- elaborate_loaded_modules_cached file_path check_deps module_info_cache_empty verbose;
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
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none, incomplete_match_ok := false };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags <- check_module_with_scope scope decl_list locals Option.none false;
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
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none, incomplete_match_ok := false };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags <- check_module_with_scope scope decl_list locals Option.none false;
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
/// is a one-line source plus the verdict, so they share this -- and so do
/// the hole-in-infer-position tests in the section after next, which is why
/// this trio is named for the checker rather than for either rule.
def check_diags_of_source (src : String) (module_name : String) : IO (List String) := do {
    let path : ModulePath := ModulePath.mp (List.cons (Identifier.id module_name) List.empty);
    match parse_all_decls src {
        ParseResult.success _ decl_list => do {
            let sd : ScopeData := build_scope_from_decls path decl_list;
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none, incomplete_match_ok := false };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            check_module_with_scope scope decl_list locals Option.none false
        },
        ParseResult.fail _ => do { return List.cons "PARSE FAILED" List.empty }
    }
}

#[partial]
def diags_contain (needle : String) (diags : List String) : Bool :=
    match diags {
        List.empty => false,
        List.cons d rest => if String.contains d needle then true else diags_contain needle rest,
    }

def diags_lack (needle : String) (diags : List String) : Bool :=
    if diags_contain needle diags then false else true

// --- Tests: --affine (check_module_with_scope_affine) ---
//
// Phase 4 of the enforcement plan: the M2 rule's first END-TO-END
// tests. Everything in `usage.mo`/`affine.mo` tests hand-built
// `Term`/`BinderUse` values; these parse real source through the real
// check driver and assert the RENDERED diagnostics, covering the
// whole chain no unit test reaches (parse -> scope build -> ordinary
// check -> affine::check_def -> render_type_error) — the same chain
// `monad check --affine` runs.

/// `check_diags_of_source`'s affine sibling, so a test can call BOTH
/// and assert the flag's exact effect: ordinary clean, affine not.
///
/// Promotion first, like the real driver: `monad check --affine` runs the
/// same elaborate order (`promote_instance_defs` before type-checking, so
/// a source with an `instance` grows `__Dict_*` value defs the walk must
/// gate). Without this the helper checks the raw decl list and the
/// dict-value gate has nothing to gate.
def check_affine_diags_of_source (src : String) (module_name : String) : IO (List String) := do {
    let path : ModulePath := ModulePath.mp (List.cons (Identifier.id module_name) List.empty);
    match parse_all_decls src {
        ParseResult.success _ decl_list => do {
            let promoted : List Decl := promote_instance_defs decl_list;
            let sd : ScopeData := build_scope_from_decls path promoted;
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none, incomplete_match_ok := false };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            check_module_with_scope_affine scope promoted locals Option.none false
        },
        ParseResult.fail _ => do { return List.cons "PARSE FAILED" List.empty }
    }
}

/// The corpus's dominant violation shape, end to end: an unannotated
/// binder handed to a callee twice. Both uses are call arguments
/// (non-owning, `usage.mo`'s `up_app_arg`), so the M2 rule's verdict
/// is `copy_required` — the borrow-shaped fix — not
/// `value_used_after_move`. The ordinary check passing is the flag's
/// whole semantics in one assertion: same file, one more rule.
#[test]
def test_affine_check_rejects_a_twice_used_binder : IO Bool := do {
    let src : String := "type T { mk }\ndef f (x : T) (y : T) : T := x\ndef twice (a : T) : T := f a a";
    let ordinary : List String <- check_diags_of_source src "probe";
    let affine : List String <- check_affine_diags_of_source src "probe";
    return (I64.beq (List.length ordinary) 0
        && diags_contain "is used 2 times but is affine" affine
        && I64.beq (List.length affine) 1)
}

/// The rule's other verdict, end to end: two CONSTRUCTOR stores of one
/// binder are two owning uses, so no borrow can help and the reported
/// error is `value_used_after_move` with its own wording.
#[test]
def test_affine_check_rejects_a_double_store : IO Bool := do {
    let src : String := "type T { mk }\ntype P { mkp (l : T) (r : T) }\ndef pair (a : T) : P := P.mkp a a";
    let ordinary : List String <- check_diags_of_source src "probe";
    let affine : List String <- check_affine_diags_of_source src "probe";
    return (I64.beq (List.length ordinary) 0
        && diags_contain "is moved 2 times; no borrow can fix this" affine
        && I64.beq (List.length affine) 1)
}

/// The negative space: a binder used exactly once (moved out as the
/// def's own result) is affine-legal, and the affine walk reports
/// NOTHING for it — the gate is the same empty-list-means-clean shape
/// the ordinary check uses, so this fails if the wiring ever confuses
/// "appending more diagnostics" with "always reporting".
#[test]
def test_affine_check_accepts_a_single_use : IO Bool := do {
    let src : String := "type T { mk }\ndef once (a : T) : T := a";
    let affine : List String <- check_affine_diags_of_source src "probe";
    return (I64.beq (List.length affine) 0)
}

/// An `instance`-bearing module synthesizes `__Dict_*` value defs (and the
/// promoted method defs) into the checked decl list -- promotion is in
/// `check_affine_diags_of_source` for exactly that reason, so this tests
/// the walk against the same decl shapes the real `--affine` driver sees.
/// Asserts both walks stay clean on them: the affine walk's `def_d` arm
/// gates dict value defs the same way the ordinary walk's does
/// (`is_dict_value_def` -- the synthetic bodies are codegen artifacts
/// `type_check` can mis-validate; the ordinary walk's own doc comment
/// records the `bound_var` failure that gate exists to prevent, which
/// arises in the full elaborate pipeline rather than this unit path).
#[test]
def test_affine_check_accepts_an_instance_module : IO Bool := do {
    let src : String := "type Pair (A : Type) (B : Type) { pair (l : A) (r : B) }\nclass Copy A {\n    def copy : A -> Pair A A\n}\ninstance Copy I64 {\n    def copy (x : I64) : Pair I64 I64 := Pair.pair x x\n}";
    let ordinary : List String <- check_diags_of_source src "probe";
    let affine : List String <- check_affine_diags_of_source src "probe";
    return (I64.beq (List.length ordinary) 0
        && Bool.not (diags_contain "bound_var" affine)
        && I64.beq (List.length affine) 0)
}

/// The rule's own case: a constructor field whose type is a function FROM
/// the type being declared. Rejected by the reference
/// (`target-rust/release/monad-rs check` on exactly this source, 2026-09-23).
/// Asserting the message, not just non-emptiness, is what makes this fail if
/// the diagnostic's wording drifts away from `TypeError::Generic`'s.
#[test]
def test_check_module_strict_pos_rejects_negative_self : IO Bool := do {
    let diags : List String <- check_diags_of_source "type Bad { mkBad (f : Bad -> I64) }" "probe";
    return (diags_contain "non-strictly positive occurrence of Bad" diags && I64.beq (List.length diags) 1)
}

/// Recursion in the codomain, one constructor field per shape: a direct
/// field, an arrow whose RESULT is the type, and an arrow whose DOMAIN is
/// itself an arrow (two flips, so positive). All three are accepted by the
/// reference on the same source.
#[test]
def test_check_module_strict_pos_accepts_positive_self : IO Bool := do {
    let src : String := "type Tree { leaf (n : I64), node (l : Tree) (r : Tree) }\ntype Fwd { mkFwd (k : I64 -> Fwd) }\ntype Neg { mkNeg (h : (Neg -> I64) -> I64) }";
    let diags : List String <- check_diags_of_source src "probe";
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
    let diags : List String <- check_diags_of_source "type Q { mkQ (f : probe::Q -> I64) }" "probe";
    return (diags_contain "non-strictly positive occurrence of Q" diags)
}

#[test]
def test_check_module_strict_pos_qualified_other_module_is_not : IO Bool := do {
    let diags : List String <- check_diags_of_source "type Q { mkQ (f : other::Q -> I64) }" "probe";
    return (diags_lack "non-strictly positive occurrence" diags)
}

/// A dotted type name is compared whole -- the elaborator stores a bare
/// reference as the name's dotted `show_name_path` spelling, so `D.E` has to
/// match `D.E` and not just its last segment.
#[test]
def test_check_module_strict_pos_dotted_name : IO Bool := do {
    let diags : List String <- check_diags_of_source "type D.E { mkE (g : D.E -> I64) }" "probe";
    return (diags_contain "non-strictly positive occurrence of D.E" diags)
}

/// A struct with the same shape is NOT flagged: the reference runs this for
/// `Decl::Type` only, and `check_decl_with_scope` routes a struct to
/// `check_struct_with_scope` instead. Without this the check would be one
/// `Decl.struct_d` arm away from over-rejecting, and nothing else says so.
#[test]
def test_check_module_strict_pos_skips_structs : IO Bool := do {
    let diags : List String <- check_diags_of_source "struct S { f : S -> I64 }" "probe";
    return (diags_lack "non-strictly positive occurrence" diags)
}

// --- Tests: the hole-in-infer-position arm ---
//
// The reference's `App(Lam{param_typ: Hole}, arg)` arms
// (`core/src/core_check.rs:1582-1593` in `check`, the twin at `:946-964` in
// `infer`) do not CHECK their argument against the unannotated parameter's
// type; they INFER it -- and `infer` on a hole is
// `InferError::CannotInferHole` (`:884`), rendered "cannot infer the type of
// a hole; add a type annotation". So the reference REJECTS
// `def k : I64 := (fn x => x) _`, while the self-hosted checker, which has no
// separate infer mode (`type_check a Term.hole` IS infer mode there),
// accepted it. `infer_position_hole` (`lang/typecheck/infer.mo`) is that arm
// ported, and these are its two halves.
//
// The arm is SYNTACTIC on the callee's term shape -- the reference's own test
// is a `matches!` on `fun.strip_ctx()` -- and that width is load-bearing
// rather than incidental, which is what three earlier candidate rules each
// got wrong. It is also why the producer half matters: the reference's
// bare-name lambda param is `param(i, Hole)` (`core/src/parser.rs:464-466`),
// the port's was a bare sort at level 1 until this phase, and with a bare
// sort standing in for a placeholder, `infer_position_hole` could tell
// neither p6 nor the written-`Type` row apart.
//
// Synthetic, and the corpus cannot cover it: the divergence's own rows are
// programs the reference refuses, so no `.mo` file in the repo contains one.
// The other half is the must-keep-ACCEPTING set, which is what fails silently
// if the arm is widened by one construct -- and it was: three candidate rules
// each fit nearly all of the matrix and each is refuted by exactly one row
// (s2, because the curried case's inner callee is an app rather than a
// literal lambda; s1, because a declared `_` behaves exactly like an absent
// annotation; r1/r3, because the reference accepts both).
//
// Every row is measured against `target-rust/release/monad-rs check` on this same
// source, and against the compiled self-hosted binary. `T` is declared EMPTY
// (`type T {}`) so the rows need no constructor and no `open` -- each row's
// value is a lambda -- and `T` doubles as row r2's non-arrow type. That is
// also why the matrix's `I64` spellings are `T -> T` here: the arm is
// type-agnostic, and `I64` is not in scope with no dependency loaded.
//
// Two rows of the recorded 15-probe matrix are deliberately absent, for two
// different reasons:
//
//   * `p5` (`List.cons 1 _`) needs `std` in scope, which
//     `build_scope_from_decls` over a bare source string does not have. Rows
//     p3 and p4 cover its class: a non-lambda callee taking a hole argument,
//     accepted;
//   * `r2` (`def k : T := (fn x => x)`) is still ACCEPTED by the self-hosted
//     checker. A lambda checked against a non-function type is the separate
//     "the expected-type channel is a hint, not an obligation" unsoundness --
//     nine further positions are in that same family -- and not this arm's, so
//     it is recorded in `plans/bootstrapping/self-hosted-compiler-review-2.md`
//     rather than pinned here as intended behaviour.

/// The matrix's shared preamble: the three named callee shapes a row can
/// reach -- `apply`, whose second parameter is declared `T -> T`; `f1`, the
/// same declaration reached through an arrow head; and `f2`, whose parameter
/// is declared `_`.
def hole_infer_preamble : String := "type T {}\n\ndef apply (g : (T -> T) -> (T -> T)) (x : T -> T) : T -> T := g x\ndef f1 (x : T -> T) : T -> T := x\ndef f2 (x : _) : T -> T := (fn z => z)\n"

def hole_infer_src (row : String) : String := hole_infer_preamble ++ row

/// Row `p6`, the arm's own case. The argument is a bare hole and the callee is
/// a literal lambda that never wrote its parameter's type down, so
/// `app_arg_expected_type`'s answer for it is itself a hole -- which is the
/// whole point: a check *against* a hole succeeds, and the reference does not
/// check here at all, it infers.
///
/// The message is asserted, not merely non-emptiness, because it is what pins
/// the diagnostic to `TypeError::custom`'s rendering -- the reference's
/// `infer_error_location` returns `None` for `CannotInferHole`
/// (`core_check_module.rs`) and renders against the enclosing decl, which is
/// exactly what `TypeError.custom` does. The count is asserted too: a second
/// diagnostic would mean the arm also disturbed the ordinary check behind it.
#[test]
def test_hole_in_infer_position_rejects_unannotated_lam_param : IO Bool := do {
    let diags : List String <- check_diags_of_source (hole_infer_src "def p6 : T -> T := (fn x => x) _") "probe";
    return (diags_contain "cannot infer the type of a hole; add a type annotation" diags && I64.beq (List.length diags) 1)
}

/// Row `s1`: a *declared* `_` parameter rejects exactly like the absent
/// annotation of p6, because `let`/lambda desugaring produces `Term.hole` for
/// both spellings. This is the row that refutes "a declared `_` is rigid, so
/// only an absent annotation is unsolved".
#[test]
def test_hole_in_infer_position_rejects_declared_hole_lam_param : IO Bool := do {
    let diags : List String <- check_diags_of_source (hole_infer_src "def s1 : T -> T := (fn (x : _) => x) _") "probe";
    return (diags_contain "cannot infer the type of a hole; add a type annotation" diags && I64.beq (List.length diags) 1)
}

/// Row `s2`, the row that kills the obvious over-wide rule. The callee is
/// itself an *application*, not a literal lambda, so the arm is not reached at
/// all and the inner lambda's hole parameter is ordinary -- the reference
/// accepts, and its own arm's test is a syntactic `matches!` on the callee for
/// exactly this reason.
#[test]
def test_hole_in_infer_position_accepts_application_callee : IO Bool := do {
    let diags : List String <- check_diags_of_source (hole_infer_src "def s2 : T -> T := (fn x => fn y => x) (fn z => z) _") "probe";
    return (I64.beq (List.length diags) 0)
}

/// Row `p1`: the callee is a named def whose second parameter is declared
/// `T -> T`, so its argument's expected type is informative and the hole is an
/// ordinary hole in a check. Accepted by the reference.
#[test]
def test_hole_in_infer_position_accepts_named_callee : IO Bool := do {
    let diags : List String <- check_diags_of_source (hole_infer_src "def p1 : T -> T := apply (fn x => x) _") "probe";
    return (I64.beq (List.length diags) 0)
}

/// Row `p3`: the same shape with an atomic argument. Accepted.
#[test]
def test_hole_in_infer_position_accepts_named_callee_atomic_arg : IO Bool := do {
    let diags : List String <- check_diags_of_source (hole_infer_src "def p3 : T -> T := f1 _") "probe";
    return (I64.beq (List.length diags) 0)
}

/// Row `p4`: a named callee whose own parameter is declared `_`. Distinct from
/// p1 because the callee's signature is uninformative -- and still accepted,
/// which is the half that says the arm keys on the *callee's term shape* and
/// not on the expected type being a hole.
#[test]
def test_hole_in_infer_position_accepts_named_callee_hole_param : IO Bool := do {
    let diags : List String <- check_diags_of_source (hole_infer_src "def p4 : T -> T := f2 _") "probe";
    return (I64.beq (List.length diags) 0)
}

/// Row `p7`: a literal-lambda callee whose parameter type IS written down.
/// Accepted -- so the arm's `param_typ` test has to look at what the lambda
/// actually wrote, not merely at the callee being a lambda.
#[test]
def test_hole_in_infer_position_accepts_annotated_lam_param : IO Bool := do {
    let diags : List String <- check_diags_of_source (hole_infer_src "def p7 : T -> T := (fn (x : T -> T) => x) _") "probe";
    return (I64.beq (List.length diags) 0)
}

/// Row `s3`: the argument is an ascription, which the parser desugars to an
/// application of an annotated identity lambda, so no hole is in infer
/// position. Accepted.
#[test]
def test_hole_in_infer_position_accepts_ascribed_arg : IO Bool := do {
    let diags <- check_diags_of_source (hole_infer_src "def s3 : T -> T := (fn x => x) (_ : T -> T)") "probe";
    return (I64.beq (List.length diags) 0)
}

/// Row `p2`: a def body that is a bare hole. Not an application, so the arm is
/// never reached and the body's hole checks against the declared type, as the
/// reference does. Accepted.
#[test]
def test_hole_in_infer_position_accepts_bare_hole_body : IO Bool := do {
    let diags <- check_diags_of_source (hole_infer_src "def p2 : T -> T := _") "probe";
    return (I64.beq (List.length diags) 0)
}

/// Rows `r1` and `p8` together. They are two rows of the recorded matrix --
/// an atomic argument and a compound one -- and they collapse into one case
/// once the concrete type is a lambda type, since a lambda is the only value
/// available with no dependency loaded. The property they pin is that a
/// non-hole argument is untouched by the arm, whatever its shape.
#[test]
def test_hole_in_infer_position_accepts_non_hole_arg : IO Bool := do {
    let diags <- check_diags_of_source (hole_infer_src "def r1 : T -> T := (fn x => x) (fn z => z)\ndef p8 : T -> T := (fn x => x) (fn z => z)") "probe";
    return (I64.beq (List.length diags) 0)
}

/// Row `r3`: the lambda IS the value, with no application anywhere. Accepted,
/// and the row that refutes "the reference rejects inferring an unannotated
/// lambda" -- it is only the *argument* of a hole-parametered one that is
/// inferred.
#[test]
def test_hole_in_infer_position_accepts_bare_lam_value : IO Bool := do {
    let diags <- check_diags_of_source (hole_infer_src "def r3 : (T -> T) -> (T -> T) := (fn x => x)") "probe";
    return (I64.beq (List.length diags) 0)
}

/// Row `r4`: a named callee with a lambda argument -- the combination of p1's
/// callee and r1's argument. Accepted.
#[test]
def test_hole_in_infer_position_accepts_named_callee_lam_arg : IO Bool := do {
    let diags <- check_diags_of_source (hole_infer_src "def r4 : T -> T := apply (fn x => x) (fn z => z)") "probe";
    return (I64.beq (List.length diags) 0)
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
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none, incomplete_match_ok := false };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags <- check_module_with_scope scope decl_list locals Option.none false;
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
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none, incomplete_match_ok := false };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags <- check_module_with_scope scope decl_list locals Option.none false;
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
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none, incomplete_match_ok := false };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags <- check_module_with_scope scope decl_list locals Option.none false;
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
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none, incomplete_match_ok := false };
            let locals : LocalScope := { vars := List.empty, parent := Option.none };
            let diags <- check_module_with_scope scope decl_list locals Option.none false;
            return (match diags {
                List.empty => true,
                List.cons _ _ => false
            })
        },
        ParseResult.fail _ => do { return false }
    }
}

// --- Tests: a field pattern's field types are substituted against the
// scrutinee (`plans/implementations/field-pattern-type-args-not-
// substituted.md`) ---
//
// A field read is not a projection: `field_access_chain` (`lang/src/
// parser/lower_parse.mo`) desugars `p.first` into a one-case BARE field
// pattern, so these rows drive the same `resolve_field_pattern_case` path
// a written `P.mk { first, .. }` takes, from source, through the whole
// parse -> scope -> check pipeline. They are source-level on purpose: the
// unit rows in `lang/src/tests/infer_tests.mo` pin the field's TYPE
// directly, and these pin what a program actually sees.
//
// `P`'s two parameters are instantiated with two DIFFERENT concrete types
// so that substituting the wrong one is a visible failure rather than an
// accident that still type-checks -- which is also what the `bad_first`
// row below exists to prove: a substitution that made everything pass
// would be no better than the defect.

def field_pattern_preamble : String :=
    "type T { t }\ntype U { u }\nstruct Mono { a : T, b : U }\ntype P A B { mk (first : A) (second : B) }\n"

def field_pattern_src (row : String) : String := field_pattern_preamble ++ row

/// The half that REPORTS: a generic field read meeting a declared return
/// type. Before the fix `p.first` was typed with `P`'s own parameter `A`
/// -- a free named sentinel nothing ever solves -- so this failed with
/// "type mismatch: expected A, found T". The message is asserted as well
/// as the count, so a rewording of the mismatch diagnostic cannot let
/// this row pass while the defect is back.
#[test]
def test_field_pattern_generic_first_is_substituted : IO Bool := do {
    let diags : List String <- check_diags_of_source (field_pattern_src "def first_of (p : P T U) : T := p.first") "probe";
    return (I64.beq (List.length diags) 0 && diags_lack "expected A" diags)
}

/// The SECOND parameter, which is what says the substitution is
/// positional in the right direction rather than mapping every parameter
/// to the first type argument.
#[test]
def test_field_pattern_generic_second_is_substituted : IO Bool := do {
    let diags : List String <- check_diags_of_source (field_pattern_src "def second_of (p : P T U) : U := p.second") "probe";
    return (I64.beq (List.length diags) 0 && diags_lack "expected B" diags)
}

/// The half that was SILENT, and the row that actually catches it. Where
/// no expected type is in play the wrong type was absorbed rather than
/// reported, so a diagnostic row cannot see it directly -- but a field read
/// THROUGH such a binding can: resolving `.a` needs `p.first`'s own type to
/// be a known inductive, and `A` never is. Not `id_t p.first`, which was
/// tried first and passes either way: an argument to a def with a
/// registered signature is inferred against `Term.hole` and its type then
/// SOLVED against the parameter (`def_call_check_args`/`solve_typevars`),
/// so the parameter absorbs `A` exactly as a hole would.
#[test]
def test_field_pattern_generic_read_nests : IO Bool := do {
    let diags : List String <- check_diags_of_source (field_pattern_src "def deep (p : P Mono U) : T := p.first.a") "probe";
    return (I64.beq (List.length diags) 0)
}

/// The substitution must still REJECT a genuine mismatch: `p.first` is
/// `T`, and this row declares `U`. Without this the three rows above
/// would also pass for a "fix" that typed every field as a hole.
#[test]
def test_field_pattern_generic_wrong_field_type_is_rejected : IO Bool := do {
    let diags : List String <- check_diags_of_source (field_pattern_src "def bad_first (p : P T U) : U := p.first") "probe";
    return (diags_contain "type mismatch" diags && I64.beq (List.length diags) 1)
}

/// The NAMED spelling (`P.mk { first, .. }`), which reaches
/// `resolve_field_pattern_case`'s other branch -- the bare form above goes
/// through `resolve_bare_field_pattern`, so one row cannot cover both.
#[test]
def test_field_pattern_named_form_is_substituted : IO Bool := do {
    let diags : List String <- check_diags_of_source (field_pattern_src "def named_of (p : P T U) : T := match p { P.mk { first, .. } => first }") "probe";
    return (I64.beq (List.length diags) 0 && diags_lack "expected A" diags)
}

/// The monomorphic control: a struct with no type parameters at all, whose
/// field types have nothing to substitute. This is the row that fails if
/// the substitution damages the common case -- every corpus field read is
/// this shape.
#[test]
def test_field_pattern_monomorphic_read_is_unaffected : IO Bool := do {
    let diags : List String <- check_diags_of_source (field_pattern_src "def geta (m : Mono) : T := m.a\ndef getb (m : Mono) : U := m.b") "probe";
    return (I64.beq (List.length diags) 0)
}

// --- An `if` condition's expected type ---------------------------------
//
// `type_check_if` (`lang/typecheck/infer.mo`) used to hand the condition
// the KIND `Type` as its expected type under the name `bool_typ`. Nearly
// every condition shape ignores an expectation, so only one shape could
// see it: a field access, which desugars to a `match` whose arm type
// `type_check_cases` unifies against it. These two rows are that shape and
// its guard -- `Bool` is declared in the source because
// `check_diags_of_source` builds its scope from the source alone.

def if_cond_preamble : String :=
    "type Bool { yes, no }\ntype T { t }\nstruct Flags { x : T, done : Bool }\n"

def if_cond_src (row : String) : String := if_cond_preamble ++ row

/// The reported shape: `if f.done` is ordinary code and must check. Before
/// the fix this failed with "type mismatch: expected Bool, found Type".
#[test]
def test_if_condition_field_access_checks : IO Bool := do {
    let diags : List String <- check_diags_of_source (if_cond_src "def ask (f : Flags) : T := if f.done then f.x else f.x") "probe";
    return (I64.beq (List.length diags) 0 && diags_lack "found Type" diags)
}

/// The guard: the expectation is really `Bool`, so a condition of another
/// type is still rejected. Without this the row above would also pass for
/// a "fix" that passed `Term.hole` and checked nothing.
#[test]
def test_if_condition_non_bool_is_rejected : IO Bool := do {
    let diags : List String <- check_diags_of_source (if_cond_src "def ask2 (f : Flags) : T := if f.x then f.x else f.x") "probe";
    return (diags_contain "type mismatch" diags && I64.beq (List.length diags) 1)
}

// --- A field read through a NON-LOCAL subject ---------------------------
//
// `lower_path_ids` (`lang/parser/lower_parse.mo`) settles the "module-
// qualified global, or field access?" ambiguity on one question only -- is
// the path's first segment a local binder? -- because the parser has no
// scope. So `p.first` on a parameter is a `FieldPattern` match by the time
// the checker sees it, while `vzero.x` on a top-level def kept its whole
// dotted spelling as ONE global name and was reported as
// `unknown variable 'vzero.x'`. `try_global_field_access`
// (`lang/typecheck/infer.mo`) is the recovery; these rows are what it
// accepts and, more importantly, what it must still refuse.
//
// `Vec3` declares one field and `Other2` a DIFFERENTLY named one, which is
// what makes the last row below a discriminator rather than a restatement:
// if the recovery ever stole a read whose subject is a local, that row
// would resolve `vzero` to the GLOBAL `Vec3` and report a missing field.
//
// The plain local-parameter case (`p.first` at zero diagnostics) needs no
// row here -- the `field_pattern_*` family above is all that shape, and
// `field_access_chain` moving modules is exactly the change that could
// have disturbed it.

def global_field_preamble : String :=
    "type T { t }\nstruct Vec3 { x : T }\nstruct Other2 { y : T }\ndef vzero : Vec3 := { x := T.t }\n"

def global_field_src (row : String) : String := global_field_preamble ++ row

/// The reported shape: `vzero` is a top-level def, not a binder, so no
/// field pattern was ever built and the read failed as an unknown name.
#[test]
def test_global_field_read_resolves : IO Bool := do {
    let diags : List String <- check_diags_of_source (global_field_src "def getx : T := vzero.x") "probe";
    return (I64.beq (List.length diags) 0 && diags_lack "vzero.x" diags)
}

/// The guard that keeps the recovery from degrading into "any dotted name
/// resolves": the same subject with a field `Vec3` does not declare is
/// still an error, not a hole.
#[test]
def test_global_field_read_of_a_missing_field_is_rejected : IO Bool := do {
    let diags : List String <- check_diags_of_source (global_field_src "def gety : T := vzero.y") "probe";
    return (I64.beq (List.length diags) 1 && diags_contain "doesn't have" diags)
}

/// The regression guard, and the one that actually pins the ORDER: a local
/// named `vzero` of a DIFFERENT struct type wins over the global of the
/// same name -- the read must be desugared at parse time against the
/// binder (the parser's gate), never reconstructed by the recovery against
/// the global. Had the recovery taken it, `vzero : Other2` would have
/// become `vzero : Vec3`, and the field `y` it reads is not `Vec3`'s.
#[test]
def test_global_field_recovery_does_not_steal_a_local : IO Bool := do {
    let diags : List String <- check_diags_of_source (global_field_src "def shadowed (vzero : Other2) : T := vzero.y") "probe";
    return (I64.beq (List.length diags) 0)
}

// --- A class method must be DECLARED by the class its qualifier names -----
//
// `Map.get` (`std/src/map.mo` declares `empty`/`insert`/`lookup`/`delete`
// and no `get`) used to type-check: `ref_names_class_method` only asked
// whether the qualifier NAMED a class, then looked the bare suffix up in
// EVERY class -- and `get` does exist, in `MonadState`
// (`init/src/prelude.mo`). The resolver had the matching hole, so a
// declared-but-absent method was rewritten to a mangled symbol nothing
// emits and reached `llc`, and no gate could see it (`validate_no_
// unresolved_class_calls` can only see refs that never resolved at all).
//
// The fixture below therefore needs a SECOND class, and that is measured,
// not decorative: with `Bag.zzz` alone -- no class anywhere declaring
// `zzz` -- the pre-fix checker reports the name as unknown too, because
// the bare-name scan comes up empty. The defect is precisely the scan
// FINDING an unrelated class's method, so a row without `Other` passes
// before and after and proves nothing.

def class_method_preamble : String :=
    "class Bag A {\n\tdef put (a : A) : A\n}\n\nclass Other A {\n\tdef zzz (a : A) : A\n}\n\n"

def class_method_src (row : String) : String := class_method_preamble ++ row

/// The positive control, and the row that keeps the tightening honest:
/// a method the qualifier's own class DOES declare still resolves, so the
/// fix cannot pass by rejecting qualified references wholesale. `put`
/// exists only on `Bag`, which is what makes it a control rather than a
/// restatement of the row below.
#[test]
def test_declared_class_method_still_resolves : IO Bool := do {
    let diags : List String <- check_diags_of_source (class_method_src "def ok_use (b : I64) : I64 := Bag.put b") "probe";
    return (I64.beq (List.length diags) 0)
}

/// The defect itself: `Bag` does not declare `zzz`, `Other` does, and the
/// pre-fix checker accepted `Bag.zzz` by finding `Other`'s.
#[test]
def test_class_method_of_another_class_is_not_borrowed : IO Bool := do {
    let diags : List String <- check_diags_of_source (class_method_src "def bad_use (b : I64) : I64 := Bag.zzz b") "probe";
    return (I64.beq (List.length diags) 1 && diags_contain "Bag.zzz" diags)
}

/// ...and a suffix no class declares is reported the same way, which is
/// the arm the row above reaches through: both land in `unknown variable`
/// rather than in some third, looser path.
#[test]
def test_class_method_declared_nowhere_is_reported : IO Bool := do {
    let diags : List String <- check_diags_of_source (class_method_src "def bad_use (b : I64) : I64 := Bag.nope b") "probe";
    return (I64.beq (List.length diags) 1 && diags_contain "Bag.nope" diags)
}

// --- A qualified reference's DOMAIN comes from the class it names ---------
//
// The rows above are about WHICH method a qualified reference resolves to.
// These are about which signature its argument position learns a lambda's
// binder from, and the defect they pin is the same shape one function over:
// `class_method_declared_sig` (`lang/src/typecheck/infer.mo`) stripped the
// qualifier and scanned every class for the bare method name, which answers
// with the LAST-DECLARED class declaring it -- `scope_data_add_class_def`
// PREPENDS (`lang/scope.mo`), so `class_defs` is in reverse declaration order
// and `Box` below, declared second, is what the scan finds. So `Bag.put` took
// its domain from a class the caller never named. Two classes declaring the
// same method name with different domains is all it takes.
//
// Three things about the fixture were measured, not assumed, and each one is
// what makes these rows discriminate where an obvious spelling does not:
//
//  * a synthetic scope has NO PRELUDE (`check_diags_of_source` builds one from
//    the source's own decls), so `I64` and `Bool` are unknown variables in it
//    and a domain mentioning one is rejected by `lam_binder_hint`'s
//    `mentions_unresolved_name` gate. The domains here are therefore DECLARED
//    types (`T`, `U`); written with `I64`/`Bool` the row passes with and
//    without the fix, because the wrong domain never reaches the binder.
//  * a field read through a binder whose type is still a HOLE is not an error
//    by itself: the checker's ambiguous-name fallback resolves the field
//    whenever exactly one type declares it. `TA`/`UA` exist only to make `t`
//    and `u` ambiguous, so a missing or wrong domain becomes visible instead
//    of being rescued.
//  * a body that only APPLIES its binder cannot discriminate: application
//    arguments are never checked against parameter types here (infer-only
//    checking), so `idT x` type-checks under any binder type at all. A field
//    read is the shape that must know the binder's type, which is why every
//    row below reads one.
def class_method_domain_preamble : String :=
    "type Z { z }\n\nstruct T { t : Z }\nstruct U { u : Z }\nstruct TA { t : Z }\nstruct UA { u : Z }\n\nclass Bag A {\n\tdef put (a : A) (f : A -> A) : A\n}\n\nclass Box A {\n\tdef put (a : A) (f : U -> U) : A\n}\n\n"

def class_method_domain_src (row : String) : String := class_method_domain_preamble ++ row

/// The row that fails before the fix and is the acceptance test for it. The
/// lambda's binder must be `Bag`'s own `A`, solved to `T` by the receiver, so
/// `x.t` resolves. Measured the other way: before the fix the binder is
/// `Box`'s `U` and this reports "field pattern names a field the constructor
/// doesn't have".
#[test]
def test_qualified_class_method_domain_comes_from_its_own_class : IO Bool := do {
    let diags : List String <- check_diags_of_source (class_method_domain_src "def useit (b : T) : Z := Bag.put b (fn x => x.t)") "probe";
    return (I64.beq (List.length diags) 0)
}

/// The converse, and the reason the row above is not enough on its own: it
/// reads the field the OTHER class declares. This reports nothing before the
/// fix, because the binder really was `Box`'s `U` and the read is then
/// correct -- a wrong domain silently accepted. After the fix the binder is
/// `T`, which has no `u`, so the row fails unless the domain changed. Together
/// the pair pins the binder to `Bag`'s `A` rather than merely to "some
/// resolution".
#[test]
def test_qualified_class_method_domain_is_not_borrowed : IO Bool := do {
    let diags : List String <- check_diags_of_source (class_method_domain_src "def useit (b : T) : Z := Bag.put b (fn x => x.u)") "probe";
    return (I64.beq (List.length diags) 1 && diags_contain "doesn't have" diags)
}

/// The control: a reference to the class the bare scan already preferred, so
/// the fix must change nothing here. It is what fails if honouring the
/// qualifier damages the case that worked by luck.
#[test]
def test_class_method_domain_of_the_declared_class_still_works : IO Bool := do {
    let diags : List String <- check_diags_of_source (class_method_domain_src "def useit2 (b : U) : Z := Box.put b (fn x => x.u)") "probe";
    return (I64.beq (List.length diags) 0)
}

// --- An unannotated lambda argument's parameter type ---------------------
//
// Rows for `implementations/do-bind-binder-untyped.md`. `check_diags_of_source`
// builds a scope from the source's OWN decls only (no prelude), so these pin
// the MECHANISM -- a non-lambda callee, an argument that is an unannotated
// lambda, and a field read through that lambda's binder -- rather than the
// `do {}` spelling, which needs the real prelude and lives in
// `examples/do_block.mo` (where the corpus `check` gate covers it).
//
// `apply_r`'s `k : R -> T` is the shape a do-bind's continuation arrives in:
// `let x <- e` desugars to `Monad.bind e (fn x => <rest>)`, and the lambda is
// checked as an ARGUMENT of a callee that is not itself an inline lambda.
// `S` is a second struct declaring the same field `f`, so that a field name
// alone does not determine a unique type -- a guard against the checker's
// ambiguous-name fallback scan finding `R` and rescuing a lambda whose binder
// is still a hole.
//
// The discriminating rows below take their callee through a LOCAL binding
// (`k : (R -> T) -> T`), not `apply_r`, and that is not incidental: a call to a
// def with a REGISTERED signature never reaches the defective path at all,
// because `try_type_check_def_call` runs first and checks the lambda against
// the parameter type `R -> T` directly. `Monad.bind` is a CLASS method with no
// `def_sigs` entry, so a real do-bind gets no such rescue -- and the local
// callee is the synthetic-scope shape with that same property. The `apply_r`
// row below pins that rescued shape on purpose, so that the reason the
// discriminating rows cannot use it stays visible.
def hole_lam_arg_preamble : String :=
    "type T { t }\nstruct R { f : T }\nstruct S { f : T }\ndef apply_r (k : R -> T) (r : R) : T := k r\n"

def hole_lam_arg_src (row : String) : String := hole_lam_arg_preamble ++ row

/// The reported shape: a callee with no registered signature, an unannotated
/// lambda argument, and a field read through the lambda's binder. `q.f`
/// desugars to a bare one-case field pattern, which before the fix reached
/// `resolve_field_pattern_case` with `q`'s type a hole: "cannot resolve
/// `{ .. }`: the matched value's type isn't known here".
#[test]
def test_hole_lam_arg_learns_its_param_type : IO Bool := do {
    let diags <- check_diags_of_source (hole_lam_arg_src "def probe (k : (R -> T) -> T) (r : R) : T := k (fn q => q.f)") "probe";
    return (I64.beq (List.length diags) 0 && diags_lack "cannot resolve" diags)
}

/// The same path spelled as the explicit pattern `q.f` desugars to, so the
/// diagnosis is pinned to the surface the bug report used rather than to the
/// projection sugar alone.
#[test]
def test_hole_lam_arg_via_field_pattern : IO Bool := do {
    let diags <- check_diags_of_source (hole_lam_arg_src "def probe2 (k : (R -> T) -> T) (r : R) : T := k (fn q => match q { { f, .. } => f })") "probe";
    return (I64.beq (List.length diags) 0)
}

/// The ANNOTATED control, on the same signature-less callee: this took
/// `type_check_lam`'s correct branch all along, so it must be untouched by the
/// new domain discovery. It is what fails if that discovery damages the path
/// that already worked.
#[test]
def test_hole_lam_arg_annotated_still_checks : IO Bool := do {
    let diags <- check_diags_of_source (hole_lam_arg_src "def probe3 (k : (R -> T) -> T) (r : R) : T := k (fn (q : R) => q.f)") "probe";
    return (I64.beq (List.length diags) 0)
}

/// A callee with a REGISTERED signature, which the def-call path resolves
/// before the defective one is reached. Kept as the control that explains why
/// rows 1-2 cannot use `apply_r`: it passes with and without the fix, so a row
/// written on this shape would pin nothing. Note the argument here is also the
/// `apply_r` shape a reader is likeliest to reach for.
#[test]
def test_hole_lam_arg_named_callee_is_rescued_either_way : IO Bool := do {
    let diags <- check_diags_of_source (hole_lam_arg_src "def probe5 (r : R) : T := apply_r (fn q => q.f) r") "probe";
    return (I64.beq (List.length diags) 0)
}

/// The domain is REAL, not a wildcard: `q` is now `R`, and `R` has no field
/// `g`. Without this row a "fix" that handed the lambda the hole in a
/// different dress would pass the three above.
///
/// Measured: this row also FAILS before the fix, but for the other reason --
/// with `q` a hole the message is "cannot resolve `{ .. }`", and with `q : R`
/// it is "field pattern names a field the constructor doesn't have". So it is
/// a second discriminator on the MESSAGE, not only a guard: it is the row that
/// fails if the fix ever starts reporting the domain case via the
/// unknown-type path again.
#[test]
def test_hole_lam_arg_enforces_the_domain : IO Bool := do {
    let diags <- check_diags_of_source (hole_lam_arg_src "def bad (r : R) : T := apply_r (fn q => q.g) r") "probe";
    return (diags_contain "doesn't have" diags && I64.beq (List.length diags) 1)
}

#[test]
def test_check_file_reports_missing_file : IO Bool := do {
    let empty_cache : ModuleInfoCache := module_info_cache_empty;
    let result <- check_file_cached empty_cache "definitely/does/not/exist.mo" false;
    return (reports_missing_file result)
}

/// The pure half of `test_check_file_reports_missing_file`: does `result`
/// carry exactly one diagnostic, and does it say the file is missing?
///
/// The checked value arrives as a plain argument -- through `Monad.bind`,
/// not by matching its `io` constructor, which is deliberately not ambient.
def reports_missing_file (result : FileCheckAndCache) : Bool :=
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
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none, incomplete_match_ok := false };
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
    let diags <- check_synthetic_source src;
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
    let diags <- check_synthetic_source src;
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
            let scope : Scope := { module_id := path, scope := sd, parent := Option.none, incomplete_match_ok := false };
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
            let result <- elaborate_loaded_modules test_file false false;
            match result {
                Result.err _ => return false,
                Result.ok em => do {
                    let locals : LocalScope := { vars := List.empty, parent := Option.none };
                    let diags <- check_module_with_scope em.scope em.target_decls locals Option.none false;
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

/// A manifest declaring a NON-default `[lib] path`, which no manifest in this
/// tree does -- the default restated is indistinguishable from no declaration
/// at all, so only this shape can tell "the declaration won" from "the default
/// was returned".
def declared_lib_fixture : String :=
  "[mote]\nname = \"init\"\nversion = \"0.1.0\"\n\n[lib]\npath = \"lib/main.mo\"\n"

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
def test_mote_dep_files_reaches_prelude_through_init : IO Bool := do {
    match Mote.parse_manifest "" lang_manifest_fixture {
        Option.none => return false,
        Option.some m => do {
            let xs <- mote_dep_files m prelude_module_path;
            return (sole_candidate_is xs "../init/src/prelude.mo")
        }
    }
}

/// A one-segment path means "that mote's own library root", the same rule
/// `mote_path_within` applies to the mote's own name. Nothing sits at
/// `../init` on disk here, so this is the no-manifest fallback; the DECLARED
/// case is the test below, where the answer is a file no default could name.
#[test]
def test_mote_dep_files_bare_name_is_that_motes_lib : IO Bool := do {
    match Mote.parse_manifest "" lang_manifest_fixture {
        Option.none => return false,
        Option.some m => do {
            let init_xs <- mote_dep_files m init_module_path;
            let std_xs <- mote_dep_files m std_module_path;
            return (sole_candidate_is init_xs "../init/src/lib.mo"
                    && sole_candidate_is std_xs "../std/src/lib.mo")
        }
    }
}

/// A dependency's declared `[lib] path` is followed, joined onto the
/// DEPENDENCY's own directory rather than the importer's.
#[test]
def test_mote_dep_lib_files_follows_the_dependencys_declaration : Bool :=
    match Mote.parse_manifest "" lang_manifest_fixture {
        Option.none => false,
        Option.some m => match Mote.parse_manifest "../init" declared_lib_fixture {
            Option.none => false,
            Option.some dep =>
                sole_candidate_is (mote_dep_lib_files m "init" (Option.some dep)) "../init/lib/main.mo"
        }
    }

/// ...and the two cases where no declaration is read: a directory carrying no
/// manifest falls back to the convention, and an undeclared mote contributes
/// NOTHING so that the cascade's own answer stands.
#[test]
def test_mote_dep_lib_files_without_a_manifest : Bool :=
    match Mote.parse_manifest "" lang_manifest_fixture {
        Option.none => false,
        Option.some m =>
            sole_candidate_is (mote_dep_lib_files m "init" Option.none) "../init/src/lib.mo"
            && List.is_empty (mote_dep_lib_files m "jsonschema" Option.none)
    }

/// A qualified path names a file inside the dependency's `src/`.
#[test]
def test_mote_dep_files_qualified_path_names_the_dep_file : IO Bool := do {
    match Mote.parse_manifest "" lang_manifest_fixture {
        Option.none => return false,
        Option.some m => do {
            let list_xs <- mote_dep_files m (ModulePath.mp [Identifier.id "std", Identifier.id "list"]);
            let ir_xs <- mote_dep_files m (ModulePath.mp [Identifier.id "llvm", Identifier.id "ir"]);
            return (sole_candidate_is list_xs "../std/src/list.mo"
                    && sole_candidate_is ir_xs "../llvm/src/ir.mo")
        }
    }
}

/// An undeclared mote contributes NOTHING, so the cascade's own answer
/// stands and the failure is the ordinary "module not found" rather than a
/// bogus manifest path.
#[test]
def test_mote_dep_files_is_empty_for_an_undeclared_mote : IO Bool := do {
    match Mote.parse_manifest "" lang_manifest_fixture {
        Option.none => return false,
        Option.some m => do {
            let xs <- mote_dep_files m (ModulePath.mp [Identifier.id "jsonschema", Identifier.id "schema"]);
            return (List.is_empty xs)
        }
    }
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
    let r <- resolve_ambient_file "lang/src" prelude_module_path ["init", "src", "__no_such_module__.mo"];
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
    let r <- resolve_ambient_file "/__no_such_mote_dir__" prelude_module_path ["init", "src", "__no_such_module__.mo"];
    match r {
        Option.none => return true,
        Option.some _ => return false
    }
}

/// Exactly three segments, spelled out. Every `mote_segments` answer is
/// three (a mote, `src`, a file), so this asserts the count as well as the
/// spelling.
def segments_are_three (segs : List String) (x : String) (y : String) (z : String) : Bool :=
    match segs {
        List.empty => false,
        List.cons a rest => match rest {
            List.empty => false,
            List.cons b rest2 => match rest2 {
                List.cons c rest3 => match rest3 {
                    List.empty => String.beq a x && String.beq b y && String.beq c z,
                    List.cons _ _ => false
                },
                List.empty => false
            }
        }
    }

/// The one reading of a module path as mote-relative segments -- shared by
/// the CWD-relative cascade (`mote_relative_file`) and the installed-
/// toolchain tier (`Mote.toolchain_candidates`), so a row here is a row
/// about both.
#[test]
def test_mote_segments_read_a_qualified_module : Bool :=
    let mp : ModulePath := ModulePath.mp [Identifier.id "std", Identifier.id "map"] in
    segments_are_three (mote_segments mp) "std" "src" "map.mo"

/// A lone name is that mote's LIBRARY root, not `<name>.mo` -- the rule
/// `mote_relative_file` already had, now stated in one place.
#[test]
def test_mote_segments_of_a_bare_name_is_its_lib_root : Bool :=
    segments_are_three (mote_segments init_module_path) "init" "src" "lib.mo"

/// The JOINED spelling is unchanged by that refactor, which is what makes
/// it behavior-preserving for `motes/<name>/src/...` and the cascade's own
/// `mote_path` candidate.
#[test]
def test_mote_relative_file_joins_the_segments : Bool :=
    let ir : ModulePath := ModulePath.mp [Identifier.id "llvm", Identifier.id "ir"] in
    if String.beq (mote_relative_file ir) "llvm/src/ir.mo"
    then String.beq (mote_relative_file init_module_path) "init/src/lib.mo"
    else false

/// The ambient trio's segment lists REPRODUCE the literals they replaced --
/// which is what keeps every working directory the old literals resolved in
/// resolving the same way now.
#[test]
def test_ambient_segments_join_to_the_old_literals : Bool :=
    if String.beq (join_path_segments ["init", "src", "prelude.mo"] "") "init/src/prelude.mo"
    then if String.beq (join_path_segments ["init", "src", "lib.mo"] "") "init/src/lib.mo"
        then String.beq (join_path_segments ["std", "src", "lib.mo"] "") "std/src/lib.mo"
        else false
    else false

/// The installed-toolchain tier with no root at all: a miss. That is the
/// ordinary state of a machine with no `~/.monad`, and the tier must not
/// build candidate paths off a root that is not there.
#[test]
def test_toolchain_first_existing_without_a_root_is_a_miss : IO Bool := do {
    let r <- toolchain_first_existing Option.none ["init", "src", "prelude.mo"];
    match r {
        Option.none => return true,
        Option.some _ => return false
    }
}

/// ...and with a root, it is the root's candidates that are probed: the
/// segments joined onto it, first existing wins.
///
/// The probe file is written by this row rather than named from the corpus,
/// because the spelling it is looked up under is root-relative and these
/// rows run from more than one working directory -- `<cwd>/init/src/
/// prelude.mo` would pass from the checkout root and fail from inside a
/// mote. `/tmp` is absolute, and the harness already depends on it
/// (`${TMPDIR:-/tmp}`).
///
/// Its NAME carries the pid, like every other file a test writes here: a
/// fixed `/tmp/monad_toolchain_probe.mo` is one name shared by every
/// concurrent `monad test` on the machine, so a sibling run's leftover file
/// would satisfy this row's lookup even if its own write never happened --
/// and the row would pass without having probed anything.
#[test]
def test_toolchain_first_existing_probes_the_root : IO Bool := do {
    let name := "monad_toolchain_probe_" ++ I64.to_string process_id ++ ".mo";
    IO.write_file (Path.path ("/tmp/" ++ name)) "// written by lang/src/module.mo's toolchain-root row\n";
    let r <- toolchain_first_existing (Option.some "/tmp") [name];
    match r {
        Option.none => return false,
        Option.some p => return (String.ends_with p name)
    }
}

/// A mote the machine's toolchain root provides: a hit, and the shape it is
/// keyed on is the mote DIRECTORY holding a `mote.toml` -- the same thing
/// `mote_named_at` probes beside the working directory, said against the
/// root instead. Pid-named and written by this row for the same reason the
/// probe above is.
#[test]
def test_installed_mote_at_finds_a_provided_mote : IO Bool := do {
    let dir := "/tmp/monad_installed_" ++ I64.to_string process_id;
    exec_cmd "mkdir" ["-p", dir ++ "/probe"];
    IO.write_file (Path.path (dir ++ "/probe/mote.toml")) "[mote]\nname = \"probe\"\nversion = \"0.1.0\"\n";
    let found <- installed_mote_at (Option.some dir) "probe";
    return found
}

/// No root, no provided motes: the ordinary state of a machine with no
/// `~/.monad`, where the gate must fall back to the working-directory probe
/// and its hint (rather than exempting every name as "installed").
#[test]
def test_installed_mote_at_without_a_root_is_a_miss : IO Bool := do {
    let found <- installed_mote_at Option.none "init";
    return (Bool.not found)
}

/// A root is not enough -- the manifest is what makes a directory a mote.
/// A name with no directory under the root (and a directory with no
/// manifest) must miss, or "provided" would mean "anything you can spell".
#[test]
def test_installed_mote_at_requires_the_manifest : IO Bool := do {
    let dir := "/tmp/monad_installed_" ++ I64.to_string process_id;
    exec_cmd "mkdir" ["-p", dir ++ "/bare"];
    let absent <- installed_mote_at (Option.some dir) "not_a_mote";
    let manifestless <- installed_mote_at (Option.some dir) "bare";
    return (Bool.not absent && Bool.not manifestless)
}

/// The sibling convention, and the one the hardcoded `../<name>` happened to
/// be right for: the manifest's own directory is one level below the working
/// directory, so the mote beside it is `../foo`. This repo is that layout
/// (`std/mote.toml` -> `path = "../init"`), which is why the old literal
/// survived -- it is wrong only for the layouts nothing here uses.
#[test]
def test_dep_path_hint_beside_the_manifest_dir : Bool :=
    match dep_path_hint "greet" "foo" {
        Option.none => false,
        Option.some p => String.beq p "../foo"
    }

/// The case that literal got wrong: the mote is beside the WORKING
/// directory while the manifest IS the working directory, so the value is
/// the mote's own name. `monad check` in a flat external layout is exactly
/// this, and `mote_named_at` finds the mote there first -- measured before
/// this changed, in `scripts/check-external-mote.sh`.
#[test]
def test_dep_path_hint_from_the_working_directory : Bool :=
    match dep_path_hint "" "foo" {
        Option.none => false,
        Option.some p => String.beq p "foo"
    }

/// Every real segment of the manifest's directory costs one `../`, and a
/// `motes/<name>` find keeps its own directory prefix -- one rule for both,
/// so a nested workspace and the repo's own `motes/` layout are the same
/// computation.
#[test]
def test_dep_path_hint_counts_every_level_down : Bool :=
    match dep_path_hint "greet/src" "motes/foo" {
        Option.none => false,
        Option.some p => String.beq p "../../motes/foo"
    }

/// A `.` names no level, so it contributes no `../`. Both spellings reach
/// the manifest in practice (a bare `monad check` passes `.` on some paths
/// and `""` on others), and the hint must not depend on which.
#[test]
def test_dep_path_hint_of_a_dot_dir_is_the_working_directory : Bool :=
    match dep_path_hint "." "foo" {
        Option.none => false,
        Option.some p => String.beq p "foo"
    }

/// The two shapes the two strings cannot be related across: a `..` segment,
/// and an absolute manifest directory (`monad check /abs/src/lib.mo`
/// discovers one). Refusing beats guessing here -- the caller says where the
/// mote is instead, since a plausible path that opens nothing is the one
/// failure a resolution hint must not have.
#[test]
def test_dep_path_hint_refuses_the_shapes_it_cannot_relate : Bool :=
    match dep_path_hint ".." "foo" {
        Option.none => match dep_path_hint "/abs/greet" "foo" {
            Option.none => true,
            Option.some _ => false
        },
        Option.some _ => false
    }

/// The undeclared message, rendered from the flat layout that used to print
/// `/mote.toml` and `../foo`: the manifest is the working directory's own
/// `mote.toml`, and the path is the mote's own name.
///
/// The locator half is asserted **whole** (`which is at `foo``), not by
/// substring: the two rows below once checked only "does it mention
/// mote.toml" and "does it mention the path", so a message that rendered as
/// `which is there at foo`` -- a stray backtick, and no opening one -- passed
/// this row and shipped. That defect was found by running the compiler in the
/// layout, not by reading it, which is what this assertion is here to spare
/// the next reader.
#[test]
def test_undeclared_mote_error_names_working_directory_paths : Bool :=
    match Mote.parse_manifest "" bare_depender_manifest_fixture {
        Option.none => false,
        Option.some m =>
            let info : ModuleInfo :=
                ModuleInfo.mk (ModulePath.mp [Identifier.id "lib"]) "src/lib.mo" List.empty in
            let u : ModulePath := ModulePath.mp [Identifier.id "foo", Identifier.id "lib"] in
            let msg : String := undeclared_mote_error m info u "foo" "foo" in
            if String.contains msg "to mote.toml"
            then (if String.contains msg "which is at `foo`"
                  then (if String.contains msg "path = \"foo\""
                        then Bool.not (String.contains msg "/mote.toml")
                        else false)
                  else false)
            else false
}

/// The sibling layout through the same renderer: the manifest's own
/// directory in the hint, so the two halves agree about where the file is.
#[test]
def test_undeclared_mote_error_names_a_nested_manifest : Bool :=
    match Mote.parse_manifest "greet" bare_depender_manifest_fixture {
        Option.none => false,
        Option.some m =>
            let info : ModuleInfo :=
                ModuleInfo.mk (ModulePath.mp [Identifier.id "lib"]) "greet/src/lib.mo" List.empty in
            let u : ModulePath := ModulePath.mp [Identifier.id "foo", Identifier.id "lib"] in
            let msg : String := undeclared_mote_error m info u "foo" "foo" in
            if String.contains msg "to greet/mote.toml"
            then String.contains msg "path = \"../foo\""
            else false
    }

/// The depender's manifest, in its own shape: a lib target and no
/// dependencies -- which is what makes the `use foo::lib` above undeclared.
def bare_depender_manifest_fixture : String :=
  "[mote]\nname = \"game\"\nversion = \"0.1.0\"\n\n[lib]\npath = \"src/lib.mo\"\n"

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
def test_mote_dep_files_prelude_within_init_itself : IO Bool := do {
    match Mote.parse_manifest "" init_self_manifest_fixture {
        Option.none => return false,
        Option.some m => do {
            let xs <- mote_dep_files m prelude_module_path;
            return (sole_candidate_is xs "src/prelude.mo")
        }
    }
}

/// The same arm reached by the mote's own NAME rather than through the
/// `prelude` re-spelling: a bare `<mote>` means that mote's library root, so
/// from inside `init/` its own lib root resolves to `src/lib.mo`.
#[test]
def test_mote_dep_files_own_name_within_itself : IO Bool := do {
    match Mote.parse_manifest "" init_self_manifest_fixture {
        Option.none => return false,
        Option.some m => do {
            let xs <- mote_dep_files m init_module_path;
            return (sole_candidate_is xs "src/lib.mo")
        }
    }
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
