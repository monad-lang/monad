/// Isolated benchmark for the DEBUG parse — `decls_parser_located`
/// (`lang/parser.mo`) versus the plain `decls_parser` on the same input.
///
/// Exists because a `--verbose` self-compile WITHOUT `--release` ran
/// 28035824ms (7h48m) against 275424ms with it, and every timed phase was
/// within noise of the fast run. Subtracting them leaves ~7h44m — 99.4% of
/// the run — in `with_located_decls` (`cli/src/main.mo`), which re-reads and
/// re-parses the whole dependency graph to attach `Term.ctx` position
/// wrappers. The FIRST parse of those same 66 files is 45685ms, so the
/// located parse is ~615x slower for the same work. Debug info is ON by
/// default (`--release` opts out), so that is the default `monad compile`.
///
/// A ratio that large is a pathology, not a constant factor, and the
/// suspect is named in the code: `resolve_offsets_in_file`
/// (`lang/parser/position.mo`) checks `is_ascending offsets` and otherwise
/// fell back to `resolve_one_by_one`, whose own doc comment called it "the
/// correct-but-quadratic path" — it scanned the whole file per offset.
/// `build_loc_table` (`lang/parser.mo`) claimed the ascending property held
/// by construction. It does not: `a + b` parses to `app (app (+) a) b`, so
/// pre-order reaches the operator before the operand left of it.
///
/// CONFIRMED and FIXED here. Before, on this machine:
///   init/id.mo      675 bytes,   30 spans  ascending YES   27ms ->    36ms
///   lang/types.mo 73000 bytes, 1469 spans  ascending NO   1753ms -> 287766ms
/// `resolve_offsets_in_file` now sorts instead of degrading, and the same
/// medium case reads 1276ms -> 2012ms: the located parse went 287766ms ->
/// 2012ms, -99.3%. Keep this benchmark as the standing guard -- it is the
/// only thing here that runs in seconds rather than hours.
///
/// So this benchmark does two things, and the second is the important one:
///   1. Times both parsers on one real source file, in ONE process, so
///      machine load cannot distort the comparison (AGENTS.md item 24).
///   2. Rebuilds `build_loc_table`'s own offset list by calling the exact
///      same three functions in the same order, and reports whether
///      `is_ascending` actually holds. That is a direct yes/no on the
///      hypothesis, and it costs milliseconds rather than an overnight run.
///
/// Run: `cargo run --release -- test bench/parser_located.mo`
use io {IO}
open IO {println, read_file}
use std::bench {now, report_since}
use lang::types {Decl}
use lang::parser::core {ParseResult}
use lang::parser::position {is_ascending}
use lang::parser::lower_parse {ParseDecl, collect_decl_rems}
use lang::parser {decls_parser, decls_parser_located, decls_skip, rems_to_offsets, skip_docstrings, skip_spaces}
use std::map {}


/// How many decls a parse produced. Forces the result inside the span it
/// is being timed in -- a benchmark that measures nothing is worse than
/// one that measures the wrong thing (AGENTS.md item 25).
#[partial]
def parsed_count (r : ParseResult (List Decl)) : I64 :=
    match r {
        ParseResult.success _ ds => List.length ds,
        ParseResult.fail _ => 0,
    }


/// The `List ParseDecl` `build_loc_table` is handed, reached the same way
/// `decls_parser_located` reaches it.
#[partial]
def parse_decls_only (input : String) : ParseResult (List ParseDecl) :=
    decls_skip (skip_docstrings (skip_spaces input)) List.empty


#[partial]
def pre_decls (r : ParseResult (List ParseDecl)) : List ParseDecl :=
    match r {
        ParseResult.success _ ds => ds,
        ParseResult.fail _ => List.empty,
    }


/// `build_loc_table`'s own first three lines, verbatim, so what this
/// reports is what that function actually feeds `resolve_offsets_in_file`.
#[partial]
def loc_table_offsets (whole_file : String) (ds : List ParseDecl) : List I64 :=
    let total : I64 := String.length whole_file in
    let rems : List I64 := List.reverse (collect_decl_rems ds List.empty) in
    rems_to_offsets total rems List.empty


/// The first descending step, or -1 when the list is ascending. Named so a
/// failure report can point at a concrete pair rather than just "false".
#[partial]
def first_inversion (offsets : List I64) : I64 :=
    match offsets {
        List.empty => 0 - 1,
        List.cons a rest => first_inversion_from a rest 1,
    }

#[partial]
def first_inversion_from (prev : I64) (offsets : List I64) (idx : I64) : I64 :=
    match offsets {
        List.empty => 0 - 1,
        List.cons b rest =>
            if I64.lt b prev then idx else first_inversion_from b rest (idx + 1),
    }


#[partial]
def run_located_bench (path : String) : IO Bool := do {
    let src <- IO.read_file (Path.path path);
    let bytes : I64 := String.length src;
    println (String.concat "file: " (String.concat path
        (String.concat " (" (String.concat (I64.to_string bytes) " bytes)"))));

    // The offset list first: it is the diagnostic, and it is cheap.
    let pre : List ParseDecl := pre_decls (parse_decls_only src);
    let offsets : List I64 := loc_table_offsets src pre;
    let n_off : I64 := List.length offsets;
    let asc : Bool := is_ascending offsets;
    let inv : I64 := first_inversion offsets;
    println (String.concat "  spans: " (String.concat (I64.to_string n_off)
        (String.concat "   is_ascending: " (if asc then "YES (walked as-is)" else "NO  (sorted first)"))));
    if asc then return unit
    else println (String.concat "  first descending step at index " (I64.to_string inv));

    // Then the two parses, back to back in one process.
    let t_plain : I64 <- Bench.now;
    let plain : I64 := parsed_count (decls_parser src);
    Bench.report_since "  decls_parser         " t_plain;
    let t_loc : I64 <- Bench.now;
    let located : I64 := parsed_count (decls_parser_located src);
    Bench.report_since "  decls_parser_located " t_loc;

    // Both parsers must agree on the decl count. A located parse that
    // silently produced fewer decls would look faster here rather than
    // showing up as a wrong answer -- the same guard
    // `bench/parser_take_while.mo` uses for its byte scanners.
    println (String.concat "  decls: plain " (String.concat (I64.to_string plain)
        (String.concat " located " (I64.to_string located))));
    return (I64.gt plain 0 && I64.beq plain located)
}


/// A small file, to establish the shape cheaply.
#[test]
def bench_located_parse_small : IO Bool := run_located_bench "init/src/id.mo"


/// A mid-size real file. The ratio between this and the small case is what
/// says whether the located parse is superlinear in file size -- AGENTS.md
/// item 37's rule: compare two sizes and look at the ratio, because a
/// share measured at one scale says nothing about another.
#[test]
def bench_located_parse_medium : IO Bool := run_located_bench "lang/src/types.mo"
