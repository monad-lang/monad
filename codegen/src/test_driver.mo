/// A `monad test` subcommand for the self-hosted compiler's own CLI
/// (`cli/src/main.mo`), analogous to `cargo test`: discover every
/// `#[test]`-attributed `def` in a target file, synthesize a driver
/// program that calls each of them and reports PASS/FAIL, compile that
/// driver via the existing native codegen pipeline
/// (`codegen.emit`), and hand the result back to `cli/src/main.mo`
/// to link and run.
///
/// Kept as its own file rather than folded into the already-1857-line
/// `codegen/emit.mo` — isolates the genuinely novel logic
/// (discovery + source synthesis) from existing, working codegen.
///
/// **Architecture decision**: the driver is synthesized as ordinary
/// `.mo` SOURCE TEXT (string-templated), not a hand-built de-Bruijn
/// `Term` AST — then fed through the already-proven
/// `lang.module.try_parse_decls`, the same entry point
/// `cli/src/main.mo`'s own `compile_file` fallback path already uses.
/// Hand-building a correct de-Bruijn-indexed `Term.lam`/`Term.app`/
/// `Term.var` tree with numerically-correct relative indices for N
/// sequential test calls is real, avoidable risk — string-templating a
/// small ordinary program and letting the real parser produce the
/// `Def` is how every other `Def` in this codebase gets produced.
///
/// **Supported test shapes**: `Bool`, `IO Bool`, `Result`, and
/// `IO Result`, classified per def by `classify_test_def` below. A
/// `Result`-returning test is judged by its constructor — `ok` is a
/// pass, `err` a failure — mirroring the Rust reference's
/// `detect_test_result_value` (`rust/core/src/lib.rs`), which unwraps an
/// `IO` wrapper first and then looks at the payload's constructor.
/// (The Rust twin classifies VALUES at run time; this classifies the
/// DECLARED TYPE at discovery time and the driver does the unwrap in
/// source it synthesizes — the same end semantics reached from the
/// only place a source-synthesizing runner can reach it.)
///
/// **Unwired-native gate**: every native a test reaches must be wired in
/// the native backend. `validate_no_unwired_natives` (called below,
/// deliberately) fails the driver compile fast otherwise, and
/// `cli/src/main.mo` reports that particular failure as a SKIP rather
/// than a test failure. The concurrency natives (`fork_io`,
/// `await_fiber`, `poll_fiber`, `cancel_fiber`, `sleep_io`, and the
/// `scope_*` family) are wired now, so
/// `std/src/concurrent/{fiber,combine,poll}_test.mo` run through this
/// driver; the gate remains the guard for any future unwired native.
use lib::decls {filter_reachable_decls}
use lib::qualify {qualified_def_name_str, qualify_modules}
use lang::types {
    Attribute, Class, DebugName, Decl, Def, ModulePath, NamePath, Term, has_attr, i64, id, no_attrs, num, package_private,
    show_identifier, struct_lit, use_bare,
}
use lib::emit {
    CompileInput, compile_db_module_with_debug, compile_input_of_modules, emit_type_head_is_io,
    gate_then, validate_reachable_elaborated
}
use lib::symbols {
    bare_npath, module_path_to_str, name_path_to_str, symbol_identifier,
}
use parsec::number {parse_i64}
use lib::validate {
    report_elab_stats, validate_no_colliding_def_symbols,
    validate_no_undesugared_struct_lits, validate_no_undesugared_elims,
    validate_no_unwired_natives
}
use llvm::ir {LLVMModule}
use lang::module {
    BestEffortElab, LoadedModules, ModuleInfo, best_effort_errors, get_loaded_all,
    get_loaded_main, resolve_open_aliases_in_modules, try_parse_decls,
}
use lang::scope {
    collect_classes, strip_all_leading_binders,
    validate_no_unresolved_class_calls,
}
use std::list {List.intercalate, List.length}
use std::log {fail_line}
use std::stream {StreamError, StreamError.is_not_found}

// ─── Discovery ──────────────────────────────────────────────────────

/// Whether `d` carries a bare `#[test]` attribute. Mirrors the Rust
/// reference's `Def::has_test_attr` (`rust/core/src/term.rs`), via the
/// already-shared `has_attr` helper (`lang/types.mo`).
#[partial]
def is_test_def (d : Def) : Bool :=
    match d {
        Def.mk {name := _name, typ := _typ, term := _term, constraints := _constraints, attrs, vis := _vis, ..} => has_attr (Identifier.id "test") attrs,
    }

/// Every top-level `Def` in `decl_list` carrying a bare `#[test]`
/// attribute. Mirrors the Rust reference's own discovery precedent
/// (`rust/core/src/lib.rs:886-892`, `module.defs().filter(has_test_attr)`)
/// — scoped to the given decl list only. Callers should pass the
/// TARGET FILE's own unprefixed decls (`.decl_list`
/// (get_loaded_main loaded)`), not its transitive `use` dependencies'
/// decls, matching that same precedent — a dependency's own tests
/// aren't this file's tests.
#[partial]
def discover_test_defs (decl_list : List Decl) : List Def :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.def_d def_val =>
                    if is_test_def def_val
                    then List.cons def_val (discover_test_defs rest)
                    else discover_test_defs rest,
                _ => discover_test_defs rest,
            },
    }

/// A discovered test, with everything the driver generator needs to
/// call it correctly.
///
/// `display` is the name shown in output: the target module's path
/// joined with `::` plus the test's own bare name, matching the Rust
/// runner's `module::sub::test_name` presentation.
pub struct TestSpec {
    display : String,
    call : String,
    io_test : Bool,
    result_test : Bool
}

/// The marker prefix the driver writes into its result file (see the
/// synthesis section header): the file's whole content is this prefix
/// followed by the failure count in decimal. Exported so the parent
/// (`cli/src/main.mo`) parses it with the SAME spelling the driver
/// wrote, rather than a hand-copied literal the two could drift on.
pub def result_file_marker : String := "__MONAD_TEST__ "

/// Read back what the driver's result file carries: the failure count.
///
/// `Option.none` for anything the driver would not have written --
/// empty content (the normal shape of "the driver died before writing
/// it"), a missing/wrong marker, or a non-numeric remainder.
pub def parse_driver_result (raw : String) : Option I64 :=
    if I64.lt (String.length raw) (String.length result_file_marker)
    then Option.none
    else if String.beq (String.slice raw 0 (String.length result_file_marker)) result_file_marker
    then parse_i64 (String.trim (String.drop (String.length result_file_marker) raw))
    else Option.none

/// The driver's report as the parent read it: `none` when there is no
/// usable count -- a missing file (the driver died before writing it) or
/// any other read failure, which `driver_report_note` names.
pub def driver_report_parsed (report : Result StreamError String) : Option I64 :=
    match report {
        Result.ok raw => parse_driver_result raw,
        Result.err _ => Option.none
    }

/// What to add to "driver exited N" about the report read: nothing for a
/// missing file (that IS the crash being reported), the reason for any
/// other failure, so an unreadable report never passes for a crash.
pub def driver_report_note (report : Result StreamError String) : String :=
    match report {
        Result.ok _ => "",
        Result.err e =>
            if StreamError.is_not_found e then ""
            else " (reading its report failed: " ++ e.message ++ ")"
    }

/// Classify one `#[test]` def by its declared return type.
///
/// Leading binders come off first (`strip_all_leading_binders`): a test
/// with implicit type params still returns `Bool` underneath, and the
/// binders are not part of the shape we dispatch on. What is left is
/// checked with codegen's own `emit_type_head_is_io` -- deliberately the
/// SAME predicate `unwrap_io_return_blocks` uses to decide whether a
/// `main` return needs unwrapping, so a test the driver binds with `<-`
/// is exactly a test codegen agrees is `IO`-headed.
#[partial]
def classify_test_def (display_prefix : String) (d : Def) : TestSpec :=
    let bare : String := name_path_to_str (Def.name d) in
    let typ : Term := strip_all_leading_binders d.typ in
    let is_io : Bool := emit_type_head_is_io typ in
    // A `Result` test is judged by its constructor, and an
    // `IO (Result ...)` test by the payload's constructor -- same
    // order the Rust reference checks in (`detect_test_result_value`
    // unwraps `IO` first). The payload of `IO X` is the single
    // argument of the `IO` application.
    let judged : Term := if is_io then io_type_payload typ else typ in
    let is_result : Bool := emit_type_head_is_result judged in
    { display := display_prefix ++ bare, call := bare, io_test := is_io, result_test := is_result }

/// The payload of an `IO X` application -- the single argument of the
/// app whose head is `IO` (which `emit_type_head_is_io` peels nested
/// apps to find). Precondition: `t`'s head IS `IO`.
#[partial]
def io_type_payload (t : Term) : Term :=
    match t {
        Term.app _f arg => arg,
        _ => t,
    }

/// Whether `t`'s head is the builtin `Result` -- the type-shape twin
/// of `emit_type_head_is_io` (`codegen/emit.mo`), for the driver's
/// `Result`-test classification.
#[partial]
def emit_type_head_is_result (t : Term) : Bool :=
    emit_type_head_is_result_go t

#[partial]
def emit_type_head_is_result_go (t : Term) : Bool :=
    match t {
        Term.var _idx dbg => match dbg {
            DebugName.named id_ => String.beq (symbol_identifier id_) "Result",
            DebugName.unnamed => false,
        },
        Term.app f _arg => emit_type_head_is_result_go f,
        _ => false,
    }

#[partial]
def classify_test_defs (display_prefix : String) (defs : List Def) : List TestSpec :=
    match defs {
        List.empty => List.empty,
        List.cons d rest =>
            List.cons (classify_test_def display_prefix d) (classify_test_defs display_prefix rest),
    }

/// The `module::sub::` prefix every test name in one file shares.
///
/// Built with `List.intercalate`, NOT `types.join_identifiers` -- the
/// latter hangs (see the self-tail-call/join_identifiers writeup); this
/// is the same job done with a library function that works.
#[partial]
def display_prefix_of (mp : ModulePath) : String :=
    match mp {
        ModulePath.mk ids => List.intercalate "::" (List.map show_identifier ids) ++ "::",
    }

/// Rename a target module's own top-level `main`, if it has one.
///
/// A file may legitimately define BOTH `#[test]` defs and a `main` (17
/// slow_tests files, `examples/structs.mo`, and `cli/src/main.mo`
/// itself). Both mains cannot survive into one binary: `rename_main`
/// (`codegen/emit.mo`) rewrites every `main`-tailed symbol to
/// `main_monad` and `dedup_funcs_by_name` keeps the FIRST one, and the
/// user's modules precede the driver in the spliced list -- so the
/// user's `main` would win and the driver would never run, silently
/// reporting nothing.
///
/// The user's `main` is renamed rather than dropped, which keeps the
/// def reachable for anything that refers to it by its NEW name. It
/// does NOT preserve a test that calls `main`: renaming rewrites the
/// definition only, never the call sites, so such a call is left
/// naming a `main` that no longer exists. Latent today -- no corpus
/// file has a test that calls its own `main` -- and the honest fix if
/// one appears is to rewrite the call sites too, not to keep the
/// original name.
///
/// The renamed `main` is NOT invoked (the Rust runner never invokes it
/// either, and calling it would both pollute reachability and run the
/// program's real side effects during a test run).
///
/// The new name avoids `__user_main` deliberately: `ends_with_main`
/// (`codegen/symbols.mo`) has a latent `String.slice` length bug,
/// and a future fix to it would make any `*_main` name collide here all
/// over again. `__monad_user_entry` ends in no such suffix.
#[partial]
def rename_user_main (decls : List Decl) : List Decl :=
    match decls {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.def_d def_val =>
                    if String.beq (name_path_to_str (Def.name def_val)) "main"
                    then List.cons (Decl.def_d (renamed_entry_def def_val)) (rename_user_main rest)
                    else List.cons d (rename_user_main rest),
                _ => List.cons d (rename_user_main rest),
            },
    }

/// `def_val` with only its name replaced. Every other field is copied
/// across explicitly -- `Def` has seven, and a struct-update shorthand
/// here would be one more thing to get wrong silently.
#[partial]
def renamed_entry_def (def_val : Def) : Def :=
    match def_val {
        Def.mk {name := _name, typ, term, constraints, attrs, vis, params, ..} =>
            Def.mk (bare_npath "__monad_user_entry") typ term constraints attrs vis params,
    }

// ─── Driver source synthesis ────────────────────────────────────────
//
// Synthesizes `.mo` SOURCE TEXT for a driver `def main : IO I64 { ... }`
// that times and calls each discovered test, prints a colored
// PASS/FAIL line per test with its duration, prints a per-file summary,
// and evaluates to the NUMBER OF FAILURES.
//
// **The driver's real report is its result FILE, not its exit code.**
// `exec_cmd` gives the parent process an exit code and nothing else (no
// stdout capture), and an exit code is one byte: a failure COUNT of
// more than 255 wraps, so a large file could never report through it
// (`lang/src/parser.mo`, at 288 tests, used to be refused outright for
// exactly that reason). The driver therefore writes
// `__MONAD_TEST__ <failed-count>` to a per-binary result file
// (`IO.write_file`, path embedded by the parent via
// `compile_loaded_modules_to_test_ir`) right before returning, and the
// parent reads THAT back as the authoritative per-test result -- which
// is what makes the parent's `X/Y total tests passed` summary count
// tests (plus, in its denominator, files that never compiled) rather
// than files. The exit code still carries the failure
// count (kept so a driver binary run by hand from the shell still says
// something), but the parent treats a missing or unparseable result
// file -- a driver that died before writing it -- as "the driver
// crashed", never trusting the possibly-wrapped code.
//
// **`main` is `IO I64` with a do-block body.** An earlier version of
// this file used a bare `I64` let-chain because an `IO I64` main was
// believed to produce a garbage exit code. That is no longer true (and
// the belief may always have been about a since-fixed bug):
// `unwrap_io_return_blocks` (`codegen/emit.mo`) unwraps an
// IO-typed `main` return at the C boundary, verified directly --
// `def main : IO I64 { return 5 }` compiles and exits 5. The do-block
// shape is what makes `IO Bool` tests bindable with `<-` at all.
//
// Colors are raw ESC bytes in the emitted string literals, matching
// `std/src/ansi.mo`'s own proven approach, and are unconditional for
// parity with the Rust runner. The driver deliberately does NOT depend
// on `std::ansi`: bringing that module in would both require it to be
// loaded (it need not be) and expose the driver to the `Style`
// name-collision trap in `qualify_modules`' own owner resolution. Its
// only dependency is `io`, which is always loaded.
//
// Every generated local is index-based (`__n0`, `__b0`, `__d0`, `__r0`,
// `__f0`, ...) rather than named after the test, so a test named like
// one of the driver's own temporaries cannot collide with it.

#[partial]
def synth_idx_name (prefix_ : String) (idx : I64) : String := prefix_ ++ I64.to_string idx

/// One test's worth of driver statements: read the clock, run the test,
/// read the clock again, print the verdict, fold the failure into the
/// running count.
///
/// `prev_fail` is the name of the accumulator this statement adds to.
/// The accumulator is threaded by NAME through explicit `I64.add`
/// calls, one per test, rather than summed in a trailing `a + b + c`
/// chain. That is not a style choice: a chained `+` whose left operand
/// is itself an `+` application cannot have its carrier type inferred,
/// so the second `+` falls back to the GENERIC `Add A` dictionary,
/// whose `Add_A_add` calls `__Dict_Add_A` calls its own shim calls
/// `Add_A_add` -- unbounded recursion, and the driver binary segfaults
/// before printing anything. That is precisely the bug that made every
/// multi-test file fail while single-test files passed (one `+`
/// inferred fine; two did not).
#[partial]
def synth_test_stmts (spec : TestSpec) (idx : I64) (esc : String) : String :=
    // Destructured, NOT read field-by-field as `spec.call` etc: a
    // struct field read in argument position compiles to field 0
    // through the self-hosted backend (the "named-call arg field access
    // reads field 0" bug), which silently substituted `display` for
    // `call` and emitted `let __b0 := m::t1;` -- source the parser then
    // rejected, dropping the driver's whole `main`. A `.mk` pattern
    // binds each field by position and is unaffected.
    match spec {
        TestSpec.mk display call io_test result_test =>
            synth_test_stmts_with display call io_test result_test idx esc,
    }

#[partial]
def synth_test_stmts_with (display : String) (call : String) (io_test : Bool) (result_test : Bool) (idx : I64) (esc : String) : String :=
    let n_start : String := synth_idx_name "__n" (idx * 2) in
    let n_end : String := synth_idx_name "__n" (idx * 2 + 1) in
    let b : String := synth_idx_name "__b" idx in
    let dur : String := synth_idx_name "__d" idx in
    let r : String := synth_idx_name "__r" idx in
    let f : String := synth_idx_name "__f" idx in
    // The `Result` holder. A fresh prefix rather than reusing `__r`
    // (the report-print temporary just below): a `Result` test's
    // verdict bind would otherwise collide with it.
    let q : String := synth_idx_name "__q" idx in
    let bind_op : String := if io_test then " <- " else " := " in
    let green : String := esc ++ "[32m" in
    let red : String := esc ++ "[31m" in
    let reset : String := esc ++ "[0m" in
    let pass_lit : String := "\"" ++ green ++ "PASS" ++ reset ++ " " ++ display ++ " (\"" in
    let fail_lit : String := "\"" ++ red ++ "FAIL" ++ reset ++ " " ++ display ++ " (\"" in
    // `println (...)` is parenthesized on purpose: application binds
    // tighter than `++`, so `println "x" ++ e` parses as
    // `(println "x") ++ e` and the duration silently never prints.
    let report : String :=
        "    let " ++ r ++ " := (if " ++ b ++
        " then println (" ++ pass_lit ++ " ++ __fmt_dur " ++ dur ++ " ++ \")\")" ++
        " else println (" ++ fail_lit ++ " ++ __fmt_dur " ++ dur ++ " ++ \")\"));\n" in
    let fail_acc : String :=
        if I64.beq idx 0
        then "    let " ++ f ++ " := (if " ++ b ++ " then 0 else 1);\n"
        else "    let " ++ f ++ " := I64.add " ++ synth_idx_name "__f" (idx - 1) ++
            " (if " ++ b ++ " then 0 else 1);\n" in
    // A `Result` test binds its call to a holder and derives the
    // verdict from the constructor (`ok` passes, `err` fails) -- the
    // source-level twin of the Rust runner's `detect_test_result_value`.
    // A plain test binds the call straight to the verdict local. Both
    // use the same `bind_op`, so an `IO (Result ...)` test's holder is
    // bound with `<-` exactly like an `IO Bool` test's verdict is.
    let test_bind : String :=
        if result_test
        then "    let " ++ q ++ bind_op ++ call ++ ";\n" ++
            "    let " ++ b ++ " := match " ++ q ++ " { Result.ok _ => true, Result.err _ => false };\n"
        else "    let " ++ b ++ bind_op ++ call ++ ";\n" in
    "    let " ++ n_start ++ " <- IO.current_time_nano;\n" ++
    test_bind ++
    "    let " ++ n_end ++ " <- IO.current_time_nano;\n" ++
    "    let " ++ dur ++ " := I64.sub " ++ n_end ++ " " ++ n_start ++ ";\n" ++
    report ++ fail_acc

#[partial]
def synth_all_test_stmts (specs : List TestSpec) (idx : I64) (esc : String) : String :=
    match specs {
        List.empty => "",
        List.cons spec rest =>
            synth_test_stmts spec idx esc ++ synth_all_test_stmts rest (idx + 1) esc,
    }

/// `format_duration` parity (`rust/core/src/lib.rs`), written in Monad.
///
/// The native (`IO.current_time_nano`, std/src/io.mo) returns raw
/// nanoseconds and does no conversion at all; every unit boundary and
/// the two-digit fraction are computed here, so both runners format
/// identically. There is no `I64.mod` (`init/src/number.mo`), hence the
/// explicit `d - w * unit` remainder arithmetic.
///
/// **Rounding.** The reference is `{:.2}` on a float, which rounds
/// half-away-from-zero and CARRIES into the whole part; the ms/s
/// branches therefore compute total HUNDREDTHS first (`(d + half) /
/// unit_per_hundredth`) and only then split off whole and fraction.
/// Rounding the fraction alone cannot carry: `1999996ns` gave
/// `1.99ms` where the reference gives `2.00ms`, and `999999999ns` has
/// to become `1000.00ms`, whole part included.
///
/// The µs branch deliberately does NOT round: the reference is
/// `{:.0}` applied to `as_micros()`, an integer count that has already
/// truncated, so truncation IS the matching semantics there.
///
/// The `d < 0` clamp exists because the host clock is the wall clock
/// (`SystemTime::now`, see `std/src/io.mo`), so a backwards step can
/// make an interval negative; a negative duration has no sensible
/// rendering and would otherwise print a `-` with a padded fraction.
///
/// Kept as SOURCE TEXT that the driver embeds, with `fmt_dur_ns` below
/// as a real-code twin for testing. The duplication is deliberate: the
/// driver is a standalone program that cannot call back into the
/// compiler, so the logic has to exist as text; `test_fmt_dur_source_
/// rounds_half_up` guards the two against drifting apart.

def fmt_dur_source : String :=
    "def __pad2 (n : I64) : String :=\n" ++
    "    if I64.lt n 10 then \"0\" ++ I64.to_string n else I64.to_string n\n" ++
    "\n" ++
    "def __fmt_dur (d : I64) : String :=\n" ++
    "    if I64.lt d 0 then \"0ns\"\n" ++
    "    else if I64.lt d 1000 then I64.to_string d ++ \"ns\"\n" ++
    "    else if I64.lt d 1000000 then I64.to_string (I64.div d 1000) ++ \"µs\"\n" ++
    "    else if I64.lt d 1000000000 then\n" ++
    "        let __h : I64 := I64.div (I64.add d 5000) 10000 in\n" ++
    "        I64.to_string (I64.div __h 100) ++ \".\" ++ __pad2 (I64.sub __h (I64.mul (I64.div __h 100) 100)) ++ \"ms\"\n" ++
    "    else\n" ++
    "        let __h : I64 := I64.div (I64.add d 5000000) 10000000 in\n" ++
    "        I64.to_string (I64.div __h 100) ++ \".\" ++ __pad2 (I64.sub __h (I64.mul (I64.div __h 100) 100)) ++ \"s\"\n"

/// A real-code twin of the `__fmt_dur` that `fmt_dur_source` above
/// embeds as text, kept identical to it line for line so the
/// formatting can actually be unit-tested -- the embedded copy only
/// ever exists inside a generated driver, which no test can call.
/// Any change to one MUST be made to the other; see that def's own
/// doc comment for why the duplication is structural rather than
/// laziness.
pub def fmt_dur_ns (d : I64) : String :=
    if I64.lt d 0 then "0ns"
    else if I64.lt d 1000 then I64.to_string d ++ "ns"
    else if I64.lt d 1000000 then I64.to_string (I64.div d 1000) ++ "µs"
    else if I64.lt d 1000000000 then
        let h : I64 := I64.div (I64.add d 5000) 10000 in
        I64.to_string (I64.div h 100) ++ "." ++ fmt_dur_pad2 (I64.sub h (I64.mul (I64.div h 100) 100)) ++ "ms"
    else
        let h : I64 := I64.div (I64.add d 5000000) 10000000 in
        I64.to_string (I64.div h 100) ++ "." ++ fmt_dur_pad2 (I64.sub h (I64.mul (I64.div h 100) 100)) ++ "s"

def fmt_dur_pad2 (n : I64) : String :=
    if I64.lt n 10 then "0" ++ I64.to_string n else I64.to_string n

#[partial]
pub def synthesize_test_driver_source (specs : List TestSpec) (file_path : String) (result_path : String) : String :=
    let total : I64 := List.length specs in
    // A raw ESC byte in the literal, exactly as `std/src/ansi.mo` does
    // it -- the driver must not `use` that module (see the header), so
    // the byte is written here directly.
    let esc : String := "" in
    // With no tests there is no `__fN` accumulator to name, so the
    // failure count is the literal 0. `compile_loaded_modules_to_test_ir`
    // reports "no #[test] defs found" before ever getting here, but this
    // function still has to emit source that parses -- `__f-1` does not,
    // and a driver that fails to parse is reported as a mystery rather
    // than as "this file has no tests".
    let last_fail : String := if I64.beq total 0 then "0" else synth_idx_name "__f" (total - 1) in
    let red : String := esc ++ "[31m" in
    let reset : String := esc ++ "[0m" in
    let tail : String := " tests passed in " ++ file_path in
    // `open IO {println}`: without it the driver's own bare
    // `println`/`current_time_nano` calls resolve for CODEGEN (which
    // finds natives independently of the checker's `Scope`) but NOT for
    // elaboration, which builds a real `Scope` and requires every name
    // to resolve -- and a `main` that fails to elaborate is silently
    // discarded, taking the driver with it. `IO` itself needs no import:
    // it is ambient, re-exported by `init/src/lib.mo`.
    "open IO {println}\n" ++
    "\n" ++
    fmt_dur_source ++
    "\n" ++
    "def main : IO I64 {\n" ++
    synth_all_test_stmts specs 0 esc ++
    "    let __total := " ++ I64.to_string total ++ ";\n" ++
    "    let __passed := I64.sub __total " ++ last_fail ++ ";\n" ++
    "    let __summary := (if I64.beq " ++ last_fail ++ " 0" ++
    " then I64.to_string __passed ++ \"/\" ++ I64.to_string __total ++ \"" ++ tail ++ "\"" ++
    " else I64.to_string __passed ++ \"/\" ++ I64.to_string __total ++ \"" ++ tail ++ ": " ++ red ++ "FAILED" ++ reset ++ "\");\n" ++
    "    let __rs := println __summary;\n" ++
    // The result FILE is the driver's authoritative report (see the
    // synthesis header). Written AFTER the summary so a driver that dies
    // mid-print still leaves no file -- the parent then reads "crashed",
    // not a stale count. No trailing newline in the content: the parent
    // trims anyway, and keeping the payload to `marker ++ digits` means
    // `parse_driver_result` never has to reason about which whitespace
    // the native write may or may not have appended.
    "    let __w <- IO.write_file (Path.path \"" ++ result_path ++ "\") (" ++
    "\"" ++ result_file_marker ++ "\" ++ I64.to_string " ++ last_fail ++ ");\n" ++
    "    return " ++ last_fail ++ ";\n" ++
    "}\n"

// ─── Full pipeline ──────────────────────────────────────────────────

/// The exact error `compile_loaded_modules_to_test_ir` returns for a
/// file with no `#[test]` defs at all -- a benign, expected outcome
/// (most library files have no tests), NOT a failure.
///
/// A named constant with a matching predicate because the caller has to
/// tell this case apart from a real compile failure, and the obvious
/// cheap test does not work: this message and an unresolved-instance
/// error (``no instance found for `Foldable.foldl` ``) BOTH start with
/// `no `, so a prefix test silently treats every instance failure as
/// "this file has no tests" -- exactly the misclassification that let
/// broken files pass as skipped.
pub def no_tests_error_message : String := "no #[test] defs found"

/// Whether an error from `compile_loaded_modules_to_test_ir` is the
/// benign no-tests case. Full-string equality, never a prefix -- see
/// `no_tests_error_message`.
pub def is_no_tests_error (e : String) : Bool :=
    String.beq e no_tests_error_message

/// Discover -> synthesize -> parse -> collision-check -> splice into
/// the decl list -> reachability-filter -> compile. Mirrors
/// `codegen.emit.compile_loaded_modules_to_ir`'s own body, but
/// with the extra splice step -- a plain `#[test]`-bearing file has no
/// pre-existing `main` for that function's own reachability rooting to
/// find, so this builds one first.
///
/// Test discovery runs over the TARGET FILE's own decls only
/// (the main `ModuleInfo`'s own `.decl_list`) -- matches the
/// Rust reference's own precedent (`rust/core/src/lib.rs`,
/// `module.defs().filter(has_test_attr)`, that module's own defs only,
/// not transitive `use` deps) -- while compilation still uses the FULL
/// loaded set (`get_loaded_all`), so the driver's calls into the
/// target file's own tests still resolve everything those tests
/// themselves call, transitively, the normal way.
/// What a successful driver compile hands back: the module to link, and
/// how many tests it contains.
///
/// The count travels with the module because the parent
/// (`cli/src/main.mo`) needs it to interpret the driver's report -- the
/// failure COUNT in the result file (see the synthesis header) is only
/// meaningful against the file's own total, which the driver itself does
/// not restate in the file.
pub struct TestIrResult {
    mod_ : LLVMModule,
    total_tests : I64
}

/// `result_path` is where the driver writes its `__MONAD_TEST__ <failed>`
/// marker (see the synthesis header): a per-binary file under the
/// parent's pid-unique out dir, threaded in from `cli/src/main.mo`'s
/// `run_test_file_tail`.
///
/// `triple` is the machine the driver is being built for, and it comes in
/// as a parameter rather than from `compile_db_module`'s own default
/// because THIS driver is linked and run immediately: a header naming some
/// other machine is an `llc`-built object of the wrong architecture at
/// `clang`'s link. `run_test_file_tail` has already probed it for the
/// link, so this costs nothing extra.
#[partial]
pub def compile_loaded_modules_to_test_ir (loaded : LoadedModules) (result_path : String) (triple : String) : IO (Result String TestIrResult) := do {
    let target_mi : ModuleInfo := get_loaded_main loaded;
    let target_decls := target_mi.decl_list;
    let test_defs := discover_test_defs target_decls;
    if List.is_empty test_defs then do {
        return Result.err no_tests_error_message
    } else do {
        let prefix_ : String := display_prefix_of target_mi.path;
        let specs : List TestSpec := classify_test_defs prefix_ test_defs;
        let driver_source := synthesize_test_driver_source specs target_mi.file_path result_path;
        match try_parse_decls driver_source {
            Option.some driver_decls =>
                compile_test_driver_with loaded driver_decls (List.length specs) triple,
            Option.none => do {
                return Result.err "internal error: failed to parse synthesized test driver (this is a monad-test bug, not a problem with the target file)"
            }
        }
    }
}

/// The parsed-driver continuation of `compile_loaded_modules_to_test_ir`
/// above. Extracted into its own def, rather than the match arm it lived
/// in, when `qualify_modules` became IO (it now carries the stage
/// sub-timing): a `<-` bind nested inside a match-arm `do` block --
/// itself inside `if`/`else do` blocks -- desugars to something
/// `elaborate_decl_with_scope` rejects, which `elaborate_module_decls_
/// best_effort` then falls back on SILENTLY, leaving this file's
/// annotated struct literals un-desugared and tripping the
/// `validate_no_undesugared_struct_lits` gate at a stage far from the
/// real failure. At a def's top level the same bind elaborates fine --
/// `codegen.emit`'s `compile_loaded_modules_to_ir` has the identical
/// call.
#[partial]
def compile_test_driver_with (loaded : LoadedModules) (driver_decls : List Decl) (total_tests : I64) (triple : String) : IO (Result String TestIrResult) := do {
    // Per-module, BEFORE the modules are flattened -- see
    // `lang.module`'s `resolve_open_aliases_in_module_info`
    // (applied to an already-flattened list, one module's
    // alias shadows an unrelated local elsewhere). The
    // driver is its own module, in the list from the start,
    // so its `open IO {println}` resolves like any other
    // module's; it also lets `qualify_modules` see it, since
    // its body calls real library defs (`I64.to_string`,
    // `++`) by bare name.
    let driver_mp : ModulePath := ModulePath.mk (List.cons (Identifier.id "__test_driver") List.empty);
    let driver_mod : ModuleInfo := ModuleInfo.mk driver_mp "" driver_decls;
    let aliased_mods := resolve_open_aliases_in_modules (List.append (get_loaded_all loaded) (List.cons driver_mod List.empty));
    // A target file may define its own `main` alongside its
    // tests; rename it out of the way -- see `rename_user_main`
    // for why the driver's `main` would otherwise lose to it.
    let target_for_rename : ModuleInfo := get_loaded_main loaded;
    let with_driver := rename_user_main_in_modules target_for_rename.path aliased_mods;
    let qualify_result <- qualify_modules false with_driver;
    // Annotated rebinding: `qualify_result` arrives from a
    // do-notation bind -- an unannotated lambda binder
    // once desugared -- and the checker then cannot infer
    // a scrutinee type for the matches below, leaving `ok`
    // ambiguous between `Result` and emit.mo's own
    // `CompileResult`. The annotation pins it (the error's
    // own prescribed fix; emit.mo's call site matches the
    // bound value where its type is already resolvable).
    let qr : Result String (List ModuleInfo) := qualify_result;
    let qualified_ok : Bool := match qr {
        Result.ok _ => true,
        Result.err _ => false,
    };
    // The fallback below used to be silent, which made a
    // qualification failure look like "the driver
    // compiled but found no tests". It is the one branch
    // here that cannot produce a working binary, so say
    // so.
    let _qnote <- match qr {
        Result.ok _ => do { return unit },
        Result.err qe => do { fail_line ("test driver: qualify_modules failed (" ++ qe ++ ")"); return unit },
    };
    let qualified_mods := match qr {
        Result.ok ms => ms,
        // Keep the pre-qualification modules on failure:
        // this driver's job is to RUN tests, and a
        // qualification error is reported by the real
        // compile path with a proper message.
        Result.err _ => with_driver,
    };
    // The same front end `build` runs (`compile_input_of_modules`).
    // The driver's own summary line (`I64.to_string __passed ++
    // "/" ++ ...`) has computed operands, which the syntactic
    // `resolve_class_calls_decls` below can only resolve once
    // elaboration has run.
    let target_mp : ModulePath := match get_loaded_main loaded { ModuleInfo.mk mp_ _ _ => mp_ };
    let input : CompileInput <- compile_input_of_modules target_mp qualified_mods false;
    let elab_report : BestEffortElab := input.report;
    let elaborated : List Decl := input.decls;
    let dispatched_decls := elaborated;
    // The root has to match the branch actually taken
    // above: on the fallback the decls are still
    // UNqualified, and rooting at `__test_driver::main`
    // would match nothing at all, quietly compiling an
    // empty program instead of surfacing the failure.
    let driver_root : String :=
        if qualified_ok
        then qualified_def_name_str driver_mp (bare_npath "main")
        else "main";
    let reachable := filter_reachable_decls (List.cons driver_root List.empty) dispatched_decls;
    report_elab_stats false (best_effort_errors elab_report) elaborated reachable;
    // Validate the REACHABLE decls, not the full spliced
    // graph -- see `codegen.emit`'s own
    // `compile_loaded_modules_to_ir` / `validate_no_
    // unresolved_class_calls`'s own doc comment for why
    // (a bug in dead code the test driver never actually
    // exercises must not block every other test in the
    // same file from running).
    let dispatched_classes := collect_classes dispatched_decls;
    match test_driver_gates (validate_reachable_elaborated elab_report reachable) dispatched_classes reachable {
        Result.err e => return (Result.err e),
        Result.ok _ =>
            // The same fail-fast gate the real compile
            // path runs (`compile_loaded_modules_to_ir`).
            // This path skipped it, which is how a test
            // reaching an unwired native produced a
            // binary that SIGSEGVs on a "return Unit"
            // stub instead of a clear message.
            // `cli/src/main.mo` turns this particular
            // error into a SKIP; see the gate note in
            // this file's header.
            match validate_no_unwired_natives reachable {
                Result.err e => return (Result.err e),
                Result.ok _ => do {
                    let result : TestIrResult := { mod_ := compile_db_module_with_debug reachable Option.none List.empty triple, total_tests := total_tests };
                    return (Result.ok result)
                },
            },
    }
}

/// The checker-handoff gates the test driver runs over its reachable decls,
/// in `compile_loaded_modules_to_ir`'s order; the first failure wins.
#[partial]
def test_driver_gates (elab_gate : Result String (List Decl)) (classes : List Class) (reachable : List Decl) : Result String (List Decl) :=
    gate_then
        (gate_then
            (gate_then elab_gate (validate_no_unresolved_class_calls classes reachable))
            (gate_then
                (validate_no_undesugared_struct_lits reachable)
                (validate_no_undesugared_elims reachable)))
        (validate_no_colliding_def_symbols reachable)

/// Apply `rename_user_main` to the module whose path is `target_mp`,
/// leaving every other loaded module untouched.
///
/// Scoped to the target because only the target's `main` competes with
/// the driver's: a dependency's `main` is not reachable from the driver
/// and never reaches codegen at all.
#[partial]
def rename_user_main_in_modules (target_mp : ModulePath) (mods : List ModuleInfo) : List ModuleInfo :=
    match mods {
        List.empty => List.empty,
        List.cons m rest =>
            let renamed : ModuleInfo :=
                if String.beq (module_path_to_str m.path) (module_path_to_str target_mp)
                then ModuleInfo.mk m.path m.file_path (rename_user_main m.decl_list)
                else m in
            List.cons renamed (rename_user_main_in_modules target_mp rest),
    }

// ─── Duration formatting ────────────────────────────────────────────
//
// Reference: `format_duration` (rust/core/src/lib.rs) -- `{nanos}ns`,
// `{:.0}µs` on `as_micros()`, `{:.2}ms`, `{:.2}s`.

// ─── `parse_driver_result` ──────────────────────────────────────────
//
// The parent's side of the protocol (`cli/src/main.mo` reads the file
// back with these exact semantics): anything that is not
// `__MONAD_TEST__ <digits>` -- including an empty read from a missing
// file -- is `Option.none`, which the parent classifies as a driver
// crash. A permissive parser here would silently resurrect the old
// "wrapped exit code read as all-pass" failure mode.
