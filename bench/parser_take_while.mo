/// Isolated micro-benchmark for `take_while`
/// (`lang/parser/combinators.mo`), the self-hosted parser's single
/// hottest loop — every whitespace skip, identifier, number and string
/// literal in the whole grammar goes through it.
///
/// Exists because AGENTS.md item 27 measured `load_file_modules`
/// (read + parse) at 2519ms of `elaborate_loaded_modules`' 3732ms (67%)
/// on `check examples/hello.mo`, i.e. two thirds of elaboration is the
/// parser running interpreted over ~1529 lines of prelude/init/std. That
/// number says WHERE the time goes but not what shape it has, and the
/// same rule that governs every other perf change in this codebase
/// applies here (see AGENTS.md's BTreeMap-regression writeup, item 4):
/// measure the specific loop before rewriting it, because chain-depth
/// and Big-O reasoning have twice failed to predict this interpreter.
///
/// What `take_while_loop` does per CHARACTER today: `is_empty input`,
/// `utf8_char_width input` (a `String.get` native plus up to four
/// `U8.lt`), `String.slice input 0 width` (a native that ALLOCATES a
/// fresh one-character string), the predicate call, and a `String.drop`
/// to recurse. The predicates are themselves comparison chains over
/// one-character strings — `is_space` up to four `String.beq`,
/// `is_ident_char` reaching `is_alphanumeric` -> `is_alpha` -> four
/// helpers, `is_digit` a ten-way chain.
///
/// Two dimensions are measured separately because they answer different
/// questions:
///
///   - **short**: many calls over a token-sized run (8 chars). This is
///     what real parsing actually does — every token is short and the
///     call volume is enormous — so it mixes per-CALL overhead with
///     per-character cost, and is the number that should track a real
///     `check` speedup.
///   - **long**: few calls over a long run (2048 chars). Isolates
///     per-CHARACTER cost with per-call overhead amortized away, which
///     is what a change to the scanning strategy itself should move.
///
/// Runs stay well under the interpreter's recursion limit either way:
/// `take_while_loop` is deliberately self-tail-recursive (see its own
/// doc comment) and `core_eval.rs` has tail-call optimization (item 8),
/// but `lang/parser/position.mo`'s own note records that scanning a
/// whole large file in one call used to blow the stack, so this
/// benchmark does not try to.
use std.bench {now, report_since}
use lang.parser.core {ParseResult}
use lang.parser.combinators {take_while, take_while_byte}
use lang.parser.char_preds {is_ident_char, is_ident_char_byte, is_space, is_space_byte}

open ParseResult {fail, success}


/// Repeatedly double `s` until it reaches `target` bytes. Doubling, not
/// append-one-at-a-time: `String.concat` allocates a fresh string per
/// call, so building an n-byte input one character at a time would be
/// O(n^2) in allocation and would dominate the thing being measured.
#[partial]
def grow_to (s : String) (target : I64) : String :=
    if I64.lt (String.length s) target
    then grow_to (String.concat s s) target
    else s


/// How much `take_while` consumed. Also the reason the loops below
/// accumulate: without consuming the result the whole call could in
/// principle be skipped, and a benchmark that measures nothing is worse
/// than one that measures the wrong thing (AGENTS.md item 25).
#[partial]
def consumed (r : ParseResult String) : I64 :=
    match r {
        success _ out => String.length out,
        fail _ => 0
    }


#[terminating]
def scan_spaces (i : I64) (n : I64) (input : String) (acc : I64) : I64 :=
    if I64.beq i n
    then acc
    else scan_spaces (i + 1) n input (acc + consumed (take_while is_space input))


#[terminating]
def scan_idents (i : I64) (n : I64) (input : String) (acc : I64) : I64 :=
    if I64.beq i n
    then acc
    else scan_idents (i + 1) n input (acc + consumed (take_while is_ident_char input))


#[terminating]
def scan_spaces_byte (i : I64) (n : I64) (input : String) (acc : I64) : I64 :=
    if I64.beq i n
    then acc
    else scan_spaces_byte (i + 1) n input (acc + consumed (take_while_byte is_space_byte input))


#[terminating]
def scan_idents_byte (i : I64) (n : I64) (input : String) (acc : I64) : I64 :=
    if I64.beq i n
    then acc
    else scan_idents_byte (i + 1) n input (acc + consumed (take_while_byte is_ident_char_byte input))


/// `calls` * `run_len` characters scanned by each predicate, so the two
/// shapes below are directly comparable per character.
def run_bench (calls : I64) (run_len : I64) (label : String) : IO Bool := do {
    let spaces : String := grow_to " " run_len;
    let idents : String := grow_to "a" run_len;
    let sp_start : I64 <- Bench.now;
    let sp_total := scan_spaces 0 calls spaces 0;
    Bench.report_since (String.concat "take_while is_space      " label) sp_start;
    let id_start : I64 <- Bench.now;
    let id_total := scan_idents 0 calls idents 0;
    Bench.report_since (String.concat "take_while is_ident_char " label) id_start;
    let spb_start : I64 <- Bench.now;
    let spb_total := scan_spaces_byte 0 calls spaces 0;
    Bench.report_since (String.concat "  BYTE is_space_byte     " label) spb_start;
    let idb_start : I64 <- Bench.now;
    let idb_total := scan_idents_byte 0 calls idents 0;
    Bench.report_since (String.concat "  BYTE is_ident_char_byte " label) idb_start;
    // All four totals are `calls * consumed-per-call` and must be
    // positive -- proof the loops actually ran and the predicates
    // actually matched. The byte totals must EQUAL their string
    // counterparts: the two scanners are required to consume exactly the
    // same input, and a byte scan that stopped early would show up here
    // rather than as a silently faster wrong answer.
    return (I64.gt sp_total 0 && I64.gt id_total 0
        && I64.beq spb_total sp_total && I64.beq idb_total id_total)
}


/// Token-shaped: short runs, high call volume. `grow_to` rounds up to a
/// power of two, so this is 8 characters per call.
#[test]
def bench_take_while_short_runs : IO Bool := run_bench 4000 8 "short (4000 calls x 8 chars)"


/// Character-cost-shaped: long runs, low call volume. Same total
/// characters scanned as the short case (32000), so the two numbers
/// differ only by per-call overhead.
#[test]
def bench_take_while_long_runs : IO Bool := run_bench 16 2048 "long  (16 calls x 2048 chars)"
