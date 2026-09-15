/// Where the located parse's extra time actually goes.
///
/// Locating every term on every path (`parse_all_decls`, `lang/module.mo`)
/// cost `check cli/src/main.mo` 57.5s -> 86.8s. An interleaved A/B of the
/// `--verbose` phase table showed **all** of it inside `load_file_modules`
/// (45.7-46.3s -> 75.7-75.9s) with every downstream phase flat --
/// `resolve_infix_decls` +4%, `build_scope_from_decls` and `names_of_decls`
/// unchanged. So the "a located tree has ~2x the nodes and every pass walks
/// them" theory is wrong: the passes do not care. The cost is in producing
/// the tree, not in consuming it.
///
/// This benchmark splits producing it into the three steps that differ,
/// on one real file, in one process:
///
///   parse        `decls_skip ...` -- identical in both modes, the control.
///   build_table  `build_loc_table` -- collect spans, sort, resolve offsets
///                to line/col, rekey into a `HashMap String Location`.
///                ONLY in the located mode.
///   lower_bare   `lower_parse_decls lower_ctx_bare` -- what the plain mode
///                did.
///   lower_loc    `lower_parse_decls (lower_ctx_locating table)` -- the same
///                walk, plus a `str_map_lookup` and a `Term.ctx` allocation
///                per located node.
///   expand       `expand_decls` on each, since macro expansion then walks
///                a bigger tree.
///
/// Run: `cargo run --release -- test bench/parser_locate_cost.mo`
use io {IO}
open IO {println, read_file}
use std.bench {now, report_since}
use lang.types {Decl, Location}
use lang.parser.core {ParseResult}
use lang.parser.lower_parse {ParseDecl, collect_decl_rems, lower_ctx_bare, lower_ctx_locating, lower_parse_decls}
use lang.parser {build_loc_table, decls_skip, rekey_by_rem, rems_to_offsets, skip_docstrings, skip_spaces}
use lang.parser.position {resolve_offsets_in_file}
use lang.typecheck.macro_queue {expand_decls}
use std.map {}


#[partial]
def pre_decls (r : ParseResult (List ParseDecl)) : List ParseDecl :=
    match r {
        ParseResult.success _ ds => ds,
        ParseResult.fail _ => List.empty,
    }


/// Forces a lowered decl list. A benchmark that measures nothing is worse
/// than one that measures the wrong thing (AGENTS.md item 25).
#[partial]
def decl_count (ds : List Decl) : I64 := List.length ds


/// One-key probe, since a `HashMap` has no cheap size -- same trick
/// `qualify_modules`' own sub-timing uses.
#[partial]
def table_probe (t : HashMap String Location) : I64 :=
    match str_map_lookup "" t {
        Option.some _ => 1,
        Option.none => 0,
    }


#[partial]
def run_locate_cost (path : String) : IO Bool := do {
    let src <- IO.read_file (Path.path path);
    println (String.concat "file: " (String.concat path
        (String.concat " (" (String.concat (I64.to_string (String.length src)) " bytes)"))));

    // The control: the raw parse, identical in both modes.
    let t_parse : I64 <- Bench.now;
    let pre : List ParseDecl := pre_decls (decls_skip (skip_docstrings (skip_spaces src)) List.empty);
    let n_pre : I64 := List.length pre;
    Bench.report_since "  parse (shared by both modes) " t_parse;

    // Located-mode extra #1: build the position table.
    let t_table : I64 <- Bench.now;
    let table := build_loc_table src pre;
    let _probe : I64 := table_probe table;
    Bench.report_since "  build_loc_table (located only)" t_table;

    // build_loc_table split into its own four steps, since it is the term
    // that matters: collect the spans, map them to absolute offsets,
    // resolve each to a line/column, then rekey into the lookup table.
    let t_c : I64 <- Bench.now;
    let rems : List I64 := List.reverse (collect_decl_rems pre List.empty);
    let n_rems : I64 := List.length rems;
    Bench.report_since "    .collect_decl_rems         " t_c;
    let t_o : I64 <- Bench.now;
    let offs : List I64 := rems_to_offsets (String.length src) rems List.empty;
    let n_offs : I64 := List.length offs;
    Bench.report_since "    .rems_to_offsets          " t_o;
    let t_r : I64 <- Bench.now;
    let resolved := resolve_offsets_in_file src offs;
    let n_res : I64 := List.length resolved;
    Bench.report_since "    .resolve_offsets_in_file  " t_r;
    let t_k : I64 <- Bench.now;
    let _tbl2 : I64 := table_probe (rekey_by_rem (String.length src) resolved str_map_empty);
    Bench.report_since "    .rekey_by_rem             " t_k;
    println (String.concat "    spans: " (I64.to_string n_rems));

    // The same lowering walk, without and with wrapper construction.
    let t_bare : I64 <- Bench.now;
    let bare : List Decl := lower_parse_decls lower_ctx_bare pre;
    let n_bare : I64 := decl_count bare;
    Bench.report_since "  lower_parse_decls BARE       " t_bare;

    let t_loc : I64 <- Bench.now;
    let located : List Decl := lower_parse_decls (lower_ctx_locating table) pre;
    let n_loc : I64 := decl_count located;
    Bench.report_since "  lower_parse_decls LOCATED    " t_loc;

    // And macro expansion over each, since it walks whatever it is handed.
    let t_eb : I64 <- Bench.now;
    let n_eb : I64 := decl_count (expand_decls bare);
    Bench.report_since "  expand_decls on BARE         " t_eb;

    let t_el : I64 <- Bench.now;
    let n_el : I64 := decl_count (expand_decls located);
    Bench.report_since "  expand_decls on LOCATED      " t_el;

    println (String.concat "  decls: pre " (String.concat (I64.to_string n_pre)
        (String.concat " bare " (String.concat (I64.to_string n_bare)
            (String.concat " located " (I64.to_string n_loc))))));
    // Both lowerings must produce the same number of decls -- one that
    // dropped some would look faster rather than look wrong.
    return (I64.gt n_pre 0 && I64.beq n_bare n_loc && I64.beq n_eb n_el)
}


/// A mid-size real file: 73 KB, ~1469 located spans.
#[test]
def bench_locate_cost_types : IO Bool := run_locate_cost "lang/src/types.mo"

/// A small one, for the ratio (AGENTS.md item 37: compare two sizes).
#[test]
def bench_locate_cost_id : IO Bool := run_locate_cost "init/src/id.mo"
