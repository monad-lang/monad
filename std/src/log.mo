/// `--verbose` progress logging for the self-hosted compiler: one line
/// per pipeline stage and one line per module load, ANSI-colored when the
/// environment supports it.
///
/// Why this module exists: the bootstrap self-compile runs for minutes
/// (interpreted) and, with `--verbose`, used to print only the target
/// module -- the dependency walk and the codegen stages were silent, so
/// a long run gave no way to tell a healthy compile from a wedged one
/// (that invisibility is half of why `monad:bootstrap-compile`'s old
/// `timeout 1200` killed healthy runs: nothing in the output said
/// "progressing"). The CI task now runs untimed and relies on this trace
/// instead (devenv.nix, ci.yml's hang-guard comments).
///
/// Rules the call sites depend on:
/// - every helper gates on `verbose` ITSELF, so a call site is one call
///   and `if verbose then ... else return unit` noise does not spread
///   through the loading chain (`ok_line`/`fail_line` are deliberately
///   NOT gated: the finish/failure lines print in both modes, as they
///   did before this module existed);
/// - prints are IO effects only, never term rewrites -- the emitted IR
///   is identical with or without them (the bootstrap ladder's
///   fixpoint property depends on that, so keep it true);
/// - granularity is per-stage and per-module, never per-def: this code
///   runs inside the compiler being timed, and a per-def print in the
///   compile path would slow the very thing it instruments. (The
///   `check` command's own per-def trace is separate and stays as is.)
///
/// Colors: `std.ansi`'s `colors_enabled` checks NO_COLOR (always wins,
/// the off switch) / FORCE_COLOR / TERM=dumb, with deliberately no
/// isatty check -- so piped CI job logs get colors too, which Forgejo
/// and GitHub render in the run view.

use io {IO}
open IO {println}
// `Ansi.fail`/`Ansi.pass` are DOTTED names -- see std/ansi.mo's own doc
// comment on `Ansi.fail` for why a bare `def fail` there poisoned the
// whole loaded set (parser's bare ParseResult `fail` ctor got rewritten
// to it by qualify's `resolve_owner` rule 3, which knows defs only).
use lib::ansi {bold, colors_enabled, dim, fail, pass}
use lib::bench {since}

/// `wrap s` (a pure `String -> String` ANSI wrapper from `std.ansi`,
/// e.g. `bold`/`dim`/`pass`/`fail`) applied only when colors are on.
/// `colored` (std.ansi) already does this env check for plain colors;
/// this is the same for style wrappers, which have no checked variant.
def styled (s : String) (wrap : String -> String) : IO String := do {
    let enabled : Bool <- colors_enabled;
    if enabled then return (wrap s) else return s
}

/// One pipeline stage starting: `-> stage: <label>`, dim arrow, bold
/// label. Print this immediately BEFORE the stage's `Bench.now` start
/// reading, so a user watching a long stage sees life before it
/// finishes -- the stage's own `bench_step`/`report_since` timing line
/// (kept as is) announces completion with the elapsed time.
def stage (verbose : Bool) (label : String) : IO Unit :=
    if verbose then do {
        let arrow : String <- styled "-> " dim;
        let name : String <- styled ("stage: " ++ label) bold;
        println (arrow ++ name);
        return unit
    } else return unit

/// One module being loaded (read + parse): dim `  loading module:
/// <name>`. Call it immediately BEFORE the load so it acts as a live
/// progress indicator, not a post-hoc log -- a hang inside the load
/// leaves the line as the last thing printed, which names the culprit.
def module_line (verbose : Bool) (name : String) : IO Unit :=
    if verbose then do {
        let line : String <- styled ("  loading module: " ++ name) dim;
        println line;
        return unit
    } else return unit

/// One module being re-parsed with source positions for DWARF debug
/// info (`with_located_decls`, the `--debug` path): dim, like
/// `module_line`, but a distinct label so a slow re-parse pass is not
/// mistaken for the first load.
def debug_module_line (verbose : Bool) (name : String) : IO Unit :=
    if verbose then do {
        let line : String <- styled ("  locating (debug re-parse): " ++ name) dim;
        println line;
        return unit
    } else return unit

/// Success line (e.g. "Compilation finished"): bold green, ungated.
def ok_line (s : String) : IO Unit := do {
    let line : String <- styled s Ansi.pass;
    println line
}

/// Failure line (e.g. "FAILED at stage: typecheck"): bold red, ungated.
def fail_line (s : String) : IO Unit := do {
    let line : String <- styled s Ansi.fail;
    println line
}

/// A stage's elapsed-time line, colored to match `stage`: dim
/// `<label> <ms>ms`. Same content as `Bench.report` (so anything
/// grepping `--verbose` output for "label Nms" keeps working), just
/// visually grouped under its stage.
def timing_line (label : String) (t0 : I64) : IO Unit := do {
    let elapsed : I64 <- Bench.since t0;
    let line : String <- styled (label ++ " " ++ I64.to_string elapsed ++ "ms") dim;
    println line
}