/// The external-tool glue: `mlir-opt`, `mlir-translate`, `mlir-runner`, seen
/// from outside. The `llvm/src/link.mo` analogue.
///
/// ## Why every call goes through `Proc.capture`
///
/// `exec_cmd` returns only an exit status. That is adequate for `llc` (it
/// works, or the link fails loudly) and NOT adequate for `mlir-opt`: a
/// failing pass pipeline reports its ENTIRE signal as a stderr diagnostic,
/// so a bare `exec_cmd` would reduce "`arith.addi` operand types differ" to
/// "exit 1". `plans/bootstrapping/mlir-codegen.md` records that as one of
/// the three hard blockers Phase 0 existed to retire, and it was retired in
/// `std`: `Proc.capture` (`std/src/process.mo`) runs the
/// `sh -c "... > errfile 2>&1"` redirect, reads the merged output back and
/// removes the file. This module is the only thing in `mlir/` that calls it.
///
/// The cost is one fork and one temp file per call, and it is real: it is
/// why `cache.mo` (Phase 2) must make a warm rebuild do **zero**
/// `mlir-opt` invocations. Nothing here can fix that; being explicit about
/// it is what stops a future caller from adding a call in a hot path.
///
/// ## A tool result is an outcome, not a string
///
/// Every entry point returns `MlirToolRun`: the exit code, the merged
/// output, and the tool's name. Three fields rather than one, because a
/// diagnostic that cannot be reproduced is not much use -- a user reading
/// "mlir-opt rejected the module" wants the tool's own text, and Phase 2's
/// cache key wants the version string. Merging them into one string would
/// make every caller re-parse.
///
/// ## Absence is a first-class answer
///
/// `mlir-opt` is not on PATH unless the dev shell was rebuilt, and a plain
/// checkout has no MLIR at all. `scripts/check-mlir-toolchain.sh` probes
/// with `command -v`; here `MlirToolRun.is_missing` exists so a caller can
/// say "no toolchain, use the reference body" rather than surfacing a
/// confusing `sh: mlir-opt: not found`. `sh` reports a missing command as
/// exit 127 -- the POSIX shell's own convention, not a guess -- and the
/// output is checked too, because a tool that exits 127 on its own is a
/// different (and reportable) failure.

use std::process {Proc.capture}
use lib::pipeline {MlirPipeline, render}

/// One tool invocation's outcome.
pub struct MlirToolRun {
    /// The tool's exit status. `127` means the shell could not find it (see
    /// `is_missing`), which is the toolchain-absent signal.
    code : I64,
    /// Everything the tool wrote, stdout and stderr MERGED. Merged on
    /// purpose: which stream carries a tool's interesting text is not
    /// something a caller should have to know, and `mlir-opt`'s whole
    /// diagnostic channel is stderr.
    output : String,
    /// The program name, so a caller can name what failed without
    /// hard-coding it a second time.
    tool : String,
}

/// `MlirToolRun` for a tool that just ran.
pub def MlirToolRun.of (tool : String) (result : Pair I64 String) : MlirToolRun :=
    match result {
        Pair.pair code output => { code := code, output := output, tool := tool },
    }

/// Whether the run failed only because the tool is not installed.
///
/// 127 is the POSIX shell's "command not found", and `Proc.capture` runs the
/// tool through `sh -c`. A 127 from the TOOL itself is indistinguishable by
/// exit code alone, which is why the output is checked too: a missing shell
/// command says `not found`.
pub def MlirToolRun.is_missing (run : MlirToolRun) : Bool :=
    match run {
        { code, output, .. } => I64.beq code 127 && String.contains output "not found",
    }

/// Whether the tool ran and succeeded.
pub def MlirToolRun.is_ok (run : MlirToolRun) : Bool := match run {
    { code, .. } => I64.beq code 0,
}

/// A one-line failure description that carries the tool's OWN text.
///
/// The whole point of capturing. A caller that prints this gets MLIR's
/// diagnostic, with its `file:line:col` intact, rather than "exit 1".
pub def MlirToolRun.message (run : MlirToolRun) : String :=
    match run {
        { code, output, tool } =>
            if I64.beq code 0 then
                tool ++ ": ok"
            else if I64.beq code 127 && String.contains output "not found" then
                String.concat tool
                    ": not found on PATH (is the dev shell built? nix/packages.nix pins llvmPackages_21, mlir included)"
            else
                tool ++ " exited " ++ I64.to_string code ++ ":\n" ++ output,
    }

/// `mlir-opt --pass-pipeline=<pipeline> <input> -o <output>`.
///
/// `--verify-each` is passed by `run_mlir_opt_verified` and NOT here,
/// because the flag costs a verifier run after every pass: a caller that
/// only wants the text (a golden emit) should not pay for it, and the one
/// that wants the drift defence (the round-trip harness) always should.
#[partial]
pub def run_mlir_opt (pipeline : MlirPipeline) (input : String) (output : String) : IO MlirToolRun := do {
    let r <- Proc.capture "mlir-opt" [
        String.concat "--pass-pipeline=" (render pipeline), input, "-o", output,
    ];
    return (MlirToolRun.of "mlir-opt" r)
}

/// The same call with `--verify-each`, which puts the verifier after every
/// pass so a lowering that produces structurally invalid IR fails at the
/// pass that broke it rather than several stages later.
///
/// Both invocations exist rather than a `Bool` parameter because the flag's
/// position in argv matters to no one and its COST does: a golden emit and
/// a drift check are different jobs, and a caller reading a call site
/// should see which one it is.
#[partial]
pub def run_mlir_opt_verified (pipeline : MlirPipeline) (input : String) (output : String) : IO MlirToolRun := do {
    let r <- Proc.capture "mlir-opt" [
        "--verify-each",
        String.concat "--pass-pipeline=" (render pipeline), input, "-o", output,
    ];
    return (MlirToolRun.of "mlir-opt" r)
}

/// `mlir-opt <input> -o <output>` with no pipeline: a parse and re-print.
///
/// This is the ROUND-TRIP check, and it is the one operation that cannot be
/// expressed through `run_mlir_opt` because it takes no `--pass-pipeline` at
/// all. Decision 2's defence against MLIR release churn is exactly this:
/// emit -> `mlir-opt` -> compare the bytes, so a changed pretty-printer
/// shows up as a diff rather than as a silent format change.
#[partial]
pub def run_mlir_opt_reprint (input : String) (output : String) : IO MlirToolRun := do {
    let r <- Proc.capture "mlir-opt" [input, "-o", output];
    return (MlirToolRun.of "mlir-opt" r)
}

/// `mlir-translate --mlir-to-llvmir <input> -o <output>`.
///
/// No pipeline argument: `mlir-translate` is a pure format converter, so
/// what it can express is a property of the module's dialect, not of a
/// pass list. Passing one would be a category error the tool rejects.
#[partial]
pub def run_mlir_translate (input : String) (output : String) : IO MlirToolRun := do {
    let r <- Proc.capture "mlir-translate" ["--mlir-to-llvmir", input, "-o", output];
    return (MlirToolRun.of "mlir-translate" r)
}

/// `mlir-runner <input> --entry-point=<fn> <args...>`: run a module on the
/// CPU and let its `func.return` value out, with no linking.
///
/// Phase 3 uses this for per-kernel numeric assertions. The runner needs
/// the shared libraries a lowered module calls (`libmlir_c_runner_utils`
/// for `memref` allocation and printing) -- and those are NOT in the
/// nixpkgs MLIR output -- so `extra_argv` is a parameter rather than
/// something this function discovers: a caller with a working
/// `-shared-libs=` line supplies it, and one without gets the tool's own
/// error instead of a hard-coded path to a library that may not exist.
#[partial]
pub def run_mlir_runner (input : String) (entry_point : String) (extra_argv : List String) : IO MlirToolRun := do {
    let r <- Proc.capture "mlir-runner" (List.append [
        input, String.concat "--entry-point=" entry_point,
    ] extra_argv);
    return (MlirToolRun.of "mlir-runner" r)
}

/// Whether `mlir-opt` is on PATH.
///
/// `--version` rather than `command -v`: there is no `which` native, so the
/// cheapest probe is to run the tool and see whether the shell found it. It
/// costs one fork, which is why it is a separate, explicitly-named function
/// a caller invokes ONCE rather than per compile.
pub def mlir_opt_available : IO Bool := do {
    let r <- Proc.capture "mlir-opt" ["--version"];
    let run := MlirToolRun.of "mlir-opt" r;
    return (MlirToolRun.is_ok run)
}

/// The toolchain's version, for the cache key (Phase 2 hashes the tool
/// version strings, so a toolchain upgrade invalidates artifacts instead of
/// silently serving one `mlir-opt`'s output as another's).
///
/// Parsed out of `--version`'s `LLVM version 21.1.8` line rather than
/// echoed whole, so the key does not change when the banner's wrapping
/// does. `""` when the tool is absent or its version cannot be parsed, and
/// a cache key treating `""` as "unknown version" is the honest behaviour:
/// it forces a miss rather than a false hit.
pub def mlir_opt_version : IO String := do {
    let r <- Proc.capture "mlir-opt" ["--version"];
    let run := MlirToolRun.of "mlir-opt" r;
    if MlirToolRun.is_missing run then return ""
    else return (version_line run.output)
}

// ─── version extraction ──────────────────────────────────────────────
//
// Pure, so it is testable without a toolchain -- which matters because the
// one thing this module cannot test on a machine with no MLIR is its tool
// calls. The scanner walks `text` once for an `x.y.z` run; see
// `version_from`.

/// The first `x.y.z` in `text`, or `""`.
///
/// The same extraction `scripts/check-mlir-toolchain.sh` does with
/// `grep -oE '[0-9]+\.[0-9]+\.[0-9]+'`, for the same reason: version
/// agreement between `mlir-opt` and `llc` is what the pin exists to
/// guarantee, and comparing whole banners would make a wording change look
/// like a version change.
pub def version_line (text : String) : String :=
    version_from text (String.length text) 0

/// Scan from `i` for a digit that starts a `d+.d+.d+` run.
///
/// `#[terminating]`: `i` counts UP, bounded by `len`, which the structural
/// checker cannot see -- the same annotation `llvm/src/target.mo`'s
/// `letters_from` needs for the same reason.
#[terminating]
def version_from (text : String) (len : I64) (i : I64) : String :=
    if I64.lt i len then
        if is_digit (String.slice text i 1) then scan_on text len i (version_at text len i)
        else version_from text len (i + 1)
    else ""

/// Keep scanning when the digit run at `i` did not form a version.
///
/// A failed attempt must not end the search: a log line reading
/// `built on 2026-11-13; LLVM version 21.1.8` starts with a digit run that
/// is a date, and answering `""` there would make `mlir_opt_version` report
/// "unknown" on a machine where the version is right there. So the empty
/// answer from `version_at` is the continue signal, and a non-empty one is
/// the result.
#[terminating]
def scan_on (text : String) (len : I64) (i : I64) (found : String) : String :=
    if String.is_empty found then version_from text len (i + 1) else found

/// The `d+.d+.d+` run starting at `i` as a three-component version, or `""`
/// when the run at `i` is not one.
///
/// A FOUR-part run answers its first three components (`21.1.8` for
/// `21.1.8.1`), which is what `grep -oE '[0-9]+\.[0-9]+\.[0-9]+'` does in
/// `scripts/check-mlir-toolchain.sh`. That agreement is the point: the
/// script's version comparison and this cache key must extract the same
/// string from the same banner, or a bump that satisfies one would look
/// like a bump to the other.
def version_at (text : String) (len : I64) (i : I64) : String :=
    let major_end := digits_end text len i in
    if I64.beq major_end i then ""
    else component_after text len major_end i 1

/// The `.`-separated component boundary at `end`, when `index` components
/// have been consumed. `start` is where the run began, so the answer is a
/// SLICE of the original text rather than a rebuilt string -- a rebuilt one
/// would be `"21.1.8"` for input `"v21.1.8"` too, which is fine, but also
/// for `"0021.1.8"`, which is not the version the tool printed.
#[terminating]
def component_after (text : String) (len : I64) (end : I64) (start : I64) (index : I64) : String :=
    if I64.lt end len then
        if String.beq (String.slice text end 1) "." then
            let next := end + 1 in
            let next_end := digits_end text len next in
            if I64.beq next_end next then ""
            else if I64.beq index 2 then String.slice text start (next_end - start)
            else component_after text len next_end start (index + 1)
        else ""
    else ""

/// Index of the first non-digit at or after `i`.
#[terminating]
def digits_end (text : String) (len : I64) (i : I64) : I64 :=
    if I64.lt i len then
        if is_digit (String.slice text i 1) then digits_end text len (i + 1) else i
    else i

/// `true` when `s` (one byte) is an ASCII digit.
pub def is_digit (s : String) : Bool :=
    String.beq s "0" || String.beq s "1" || String.beq s "2" || String.beq s "3"
        || String.beq s "4" || String.beq s "5" || String.beq s "6"
        || String.beq s "7" || String.beq s "8" || String.beq s "9"

// ─── tests: the pure half ────────────────────────────────────────────
//
// The tool CALLS cannot be tested without MLIR installed, and the mote's
// tests must run on a machine with none (Phase 1's acceptance). So what is
// tested here is everything that does not fork: the outcome predicates and
// the version parser. `scripts/check-mlir-goldens.sh` is where the calls
// are exercised, opt-in and skip-clean, exactly as
// `scripts/check-mlir-toolchain.sh` is.

/// MLIR 21.1.8's real `--version` output, trimmed to the two lines that
/// matter. The banner is what `mlir_opt_version` parses in practice.
#[test]
def test_version_from_the_real_banner : Bool :=
    String.beq (version_line "LLVM (http://llvm.org/):\n  LLVM version 21.1.8\n  Optimized build.\n")
        "21.1.8"

/// A single-component or two-component run is not a version. `clang
/// version 21` and `21.1` are both real shapes of a truncated banner, and
/// answering `21` would put a version in the cache key that no tool
/// printed.
#[test]
def test_a_partial_run_is_not_a_version : Bool :=
    String.beq (version_line "LLVM 21") ""
        && String.beq (version_line "LLVM 21.1") ""

/// A digit run that is NOT a version must not stop the scan. Real banners
/// put dates and timings beside the version line, and `2026-11-13` starts
/// with four digits that form no `.`-separated triplet -- so a scanner that
/// gave up on the first digit run would answer `""` on input where `21.1.8`
/// is present. This is the case that makes `scan_on` necessary.
#[test]
def test_a_failed_attempt_keeps_scanning : Bool :=
    String.beq (version_line "built on 2026-11-13; LLVM version 21.1.8 (4.8s)")
        "21.1.8"

/// A float like `4.8` is two components, and `4.8s` after a version must
/// not be preferred over the version itself -- the first COMPLETE run
/// wins, in text order.
#[test]
def test_the_first_complete_run_wins : Bool :=
    String.beq (version_line "4.8s then 21.1.8") "21.1.8"

/// A four-part run answers its first three components, matching
/// `grep -oE '[0-9]+\.[0-9]+\.[0-9]+'` in `scripts/check-mlir-toolchain.sh`
/// -- the script and the cache key must agree about what the version IS.
#[test]
def test_a_four_part_run_answers_its_first_three : Bool :=
    String.beq (version_line "21.1.8.1") "21.1.8"

/// Text with no version at all answers `""`, which is what makes
/// `mlir_opt_version` fall back to "unknown" rather than to garbage.
#[test]
def test_no_version_is_empty : Bool :=
    String.beq (version_line "no digits here") ""
        && String.beq (version_line "") ""

/// The outcome predicates, over outcomes built by hand. 127-with-"not
/// found" is a missing tool; 1-with-a-diagnostic is a real failure, and the
/// two must not be confused -- a caller that treats the second as the first
/// hides a compile error as "no toolchain".
#[test]
def test_missing_and_failed_are_different : Bool :=
    let absent := MlirToolRun.of "mlir-opt" (Pair.pair 127 "sh: 1: mlir-opt: not found") in
    let failed := MlirToolRun.of "mlir-opt"
        (Pair.pair 1 "module.mlir:2:12: error: 'arith.addi' op operand types differ") in
    MlirToolRun.is_missing absent
        && Bool.not (MlirToolRun.is_ok absent)
        && Bool.not (MlirToolRun.is_missing failed)
        && Bool.not (MlirToolRun.is_ok failed)

/// A successful run's message is not its output -- the output of a
/// successful `mlir-opt -o file` is empty, and a message that echoed it
/// would say nothing.
#[test]
def test_ok_message_names_the_tool : Bool :=
    String.beq (MlirToolRun.message (MlirToolRun.of "mlir-opt" (Pair.pair 0 ""))) "mlir-opt: ok"

/// A failure's message carries the tool's own diagnostic text, which is the
/// whole reason `Proc.capture` is used.
#[test]
def test_failure_message_carries_the_diagnostic : Bool :=
    let run := MlirToolRun.of "mlir-opt"
        (Pair.pair 1 "broken.mlir:2:12: error: 'arith.addi' op operand types differ") in
    String.contains (MlirToolRun.message run)
        "broken.mlir:2:12: error: 'arith.addi' op operand types differ"
