// Which triple a build is for, and what the LLVM tools must be told about
// it.
//
// Three fields rather than one, because the tools do not agree and the ABI
// is not derivable from the triple. Measured 2026-10-06 against llc 21.1.8:
//
//   * `llc` REJECTS `riscv64gc-unknown-linux-gnu` -- the spelling both
//     `clang --print-target-triple` and nixpkgs' sysroot use -- with
//     "unable to get target for ..."; llc wants `riscv64-unknown-linux-gnu`.
//     Hence `llc_triple`.
//   * llc's default for that triple is soft-float, which does not match the
//     rv64gc/lp64d sysroot `pkgsCross.riscv64` builds against, and no triple
//     spelling selects the hard-float ABI. Hence `llc_flags`.
//
// An EMPTY `llc_triple` means "pass no `-mtriple`": llc then takes the triple
// from the module header, which is `triple`. So for every target whose
// spelling llc already accepts the header is the whole answer, and the
// native argv is unchanged from what it was before this file existed.
//
// The C compiler is deliberately NOT told a triple here. `runtime.c` is
// compiled and the objects are linked by whatever `clang` is on PATH, and
// each cross leg puts that target's own cc there (a two-line
// `writeShellScriptBin "clang"` shim exec'ing `pkgsCross.<x>.stdenv.cc`).
// Handing such a wrapper `--target=` fights it: nixpkgs' own cc-wrapper
// refuses outright on riscv64 with "unsupported option
// '-fzero-call-used-regs=used-gpr' for target 'riscv64-unknown-linux-gnu'".

use std::process {Proc.capture}
use std::io {IO.get_env}
open IO {println}

/// One target: the spelling the toolchain is addressed by, the spelling llc
/// needs if it differs, and the ABI flags no spelling can carry.
pub struct TargetSpec {
    triple : String,
    llc_triple : String,
    llc_flags : List String,
}

/// The targets this compiler has a measured spelling for. A name that is not
/// here is still accepted -- see `TargetSpec.resolve` -- and gets the same
/// string for both tools and no flags, which is right for everything but
/// riscv64, which is here for three reasons: llc spells its triple differently,
/// its ABI is not derivable from that spelling, and nixpkgs' riscv64 cc links
/// PIE, so llc's default non-PIC object dies at the link with
/// `relocation R_RISCV_HI20 ... recompile with -fPIC`.
pub def TargetSpec.known_targets : List TargetSpec := [
    TargetSpec.mk "x86_64-unknown-linux-gnu" "" List.empty,
    TargetSpec.mk "aarch64-unknown-linux-gnu" "" List.empty,
    TargetSpec.mk "aarch64-apple-darwin" "" List.empty,
    TargetSpec.mk "riscv64gc-unknown-linux-gnu" "riscv64-unknown-linux-gnu" [
        "-mattr=+m,+a,+f,+d,+c", "-target-abi=lp64d", "-relocation-model=pic",
    ],
    TargetSpec.mk "wasm32-unknown-wasip1" "" List.empty,
    TargetSpec.mk "wasm32-unknown-unknown" "" List.empty,
]

/// The two wasm profiles behind the wasm triples. Everything else is the
/// host's native target.
pub type TargetKind {
    native,
    wasi,
    web,
}

/// `kind`'s name in diagnostics (`native`, `wasi`, `web`).
pub def TargetKind.name (kind : TargetKind) : String := match kind {
    TargetKind.native => "native",
    TargetKind.wasi => "wasi",
    TargetKind.web => "web",
}

/// Whether `kind` is one of the wasm profiles.
pub def TargetKind.is_wasm (kind : TargetKind) : Bool := match kind {
    TargetKind.native => false,
    TargetKind.wasi => true,
    TargetKind.web => true,
}

/// Classify a resolved triple. Any `wasm*` spelling is a wasm profile --
/// non-`wasm32` ones are then rejected by `TargetPlan.resolve` rather than
/// silently treated as native and linked with the host toolchain.
pub def TargetKind.of_triple (triple : String) : TargetKind :=
    if String.starts_with "wasm" triple
    then if String.contains triple "wasi" then TargetKind.wasi else TargetKind.web
    else TargetKind.native

/// The output suffix for `kind` (`.wasm` for both wasm profiles).
pub def TargetKind.output_ext (kind : TargetKind) : String := match kind {
    TargetKind.native => "",
    TargetKind.wasi => ".wasm",
    TargetKind.web => ".wasm",
}

/// Everything `llvm/src/link.mo` needs to know about a target beyond the
/// llc triple: which C compiler and flags, which runtime platform define,
/// and the output suffix. Kept OFF `TargetSpec` so that its nine
/// construction sites and every existing caller stay unchanged.
pub struct TargetPlan {
    kind : TargetKind,
    triple : String,
    clang : String,
    compile_flags : List String,
    link_flags : List String,
    runtime_defines : List String,
    output_ext : String,
}

/// The plan for a native target: same bare `clang`, no flags, no suffix.
pub def TargetPlan.native_plan (triple : String) : TargetPlan :=
    TargetPlan.mk TargetKind.native triple "clang" List.empty List.empty List.empty
        (TargetKind.output_ext TargetKind.native)

/// A wasm plan, addressed through the wasi-sdk `clang` by absolute path.
/// This is the deliberate exception to the "do not pass --target to the C
/// compiler" rule above: wasi-sdk IS the target toolchain, not a nixpkgs
/// cc-wrapper being shimmed.
pub def TargetPlan.for_wasm (kind : TargetKind) (triple : String) (clang : String) (sysroot : String) : TargetPlan :=
    match kind {
        TargetKind.wasi => TargetPlan.mk kind triple clang
            ["--target=" ++ triple, "--sysroot=" ++ sysroot]
            ["--target=" ++ triple, "--sysroot=" ++ sysroot, "-Wl,-z,stack-size=8388608"]
            ["-DMONAD_TARGET_WASI"] (TargetKind.output_ext kind),
        TargetKind.web => TargetPlan.mk kind triple clang
            ["--target=wasm32-unknown-unknown", "-ffreestanding", "-fno-builtin"]
            ["--target=wasm32-unknown-unknown", "-nostdlib", "-Wl,--no-entry",
             "-Wl,--export-memory",
             // `monad_main` is exported by runtime/src/platform_web.c's
             // `__attribute__((export_name("monad_main")))`; a
             // `--export=monad_main` here would look for a C symbol of that
             // name and fail, because the C function is `monad_web_entry`.
             "-Wl,--export=monad_alloc", "-Wl,--export=monad_string_length",
             "-Wl,--export=monad_i64_to_string", "-Wl,-z,stack-size=1048576"]
            ["-DMONAD_TARGET_WEB"] (TargetKind.output_ext kind),
        TargetKind.native => TargetPlan.native_plan triple,
    }

/// The plan for `spec`. Native resolves without touching the environment;
/// wasm requires `WASI_SDK_PATH` and a working `bin/clang`.
#[partial]
pub def TargetPlan.resolve (spec : TargetSpec) : IO (Result String TargetPlan) := do {
    let kind := TargetKind.of_triple spec.triple;
    match kind {
        TargetKind.native => return (Result.ok (TargetPlan.native_plan spec.triple)),
        _ => do {
            if Bool.not (TargetPlan.is_supported_wasm_triple spec.triple) then
                return (Result.err (TargetPlan.unsupported_wasm_message spec.triple))
            else do {
                let env <- IO.get_env "WASI_SDK_PATH";
                match env {
                    Option.none => return (Result.err (TargetPlan.missing_sdk_message spec.triple kind)),
                    Option.some raw => do {
                        let root := String.trim raw;
                        if String.is_empty root then
                            return (Result.err (TargetPlan.missing_sdk_message spec.triple kind))
                        else do {
                            let clang := root ++ "/bin/clang";
                            let sysroot := root ++ "/share/wasi-sysroot";
                            let cap <- Proc.capture clang ["--version"];
                            match cap {
                                Pair.pair code _out =>
                                    if code == 0
                                    then return (Result.ok (TargetPlan.for_wasm kind spec.triple clang sysroot))
                                    else return (Result.err (TargetPlan.bad_sdk_message root clang)),
                            }
                        }
                    }
                }
            }
        }
    }
}

/// The wasm spellings this compiler has a runtime and link recipe for.
/// `wasm64` (and any other `wasm*`) is deliberately rejected rather than
/// silently classified as native.
pub def TargetPlan.is_supported_wasm_triple (triple : String) : Bool :=
    String.starts_with "wasm32" triple

/// The diagnostic for a wasm spelling we do not build (e.g. `wasm64`).
#[partial]
def TargetPlan.unsupported_wasm_message (triple : String) : String :=
    "error: target `" ++ triple ++ "` is not a supported wasm profile: use wasm32-unknown-wasip1 or wasm32-unknown-unknown"

#[partial]
def TargetPlan.missing_sdk_message (triple : String) (kind : TargetKind) : String :=
    "error: target `" ++ triple ++ "` (" ++ TargetKind.name kind ++ ") needs the wasi-sdk toolchain, but `WASI_SDK_PATH` is not set. Set it to the wasi-sdk root (the directory containing bin/clang and share/wasi-sysroot), or enter the project dev shell (devenv pins one)."

#[partial]
def TargetPlan.bad_sdk_message (root : String) (clang : String) : String :=
    "error: WASI_SDK_PATH=`" ++ root ++ "` does not name a wasi-sdk installation: `" ++ clang ++ "` is not executable."

/// `name` with `kind`'s output suffix, unless it already has it. The one
/// place the suffix rule lives; the CLI and the linker both call this.
pub def TargetPlan.output_name_for (kind : TargetKind) (name : String) : String :=
    let ext := TargetKind.output_ext kind in
    if String.is_empty ext then name
    else if String.ends_with name ext then name
    else name ++ ext

/// `name` with the plan's output suffix, unless it already has it.
pub def TargetPlan.output_name (plan : TargetPlan) (name : String) : String :=
    TargetPlan.output_name_for plan.kind name

/// The aliases the toolchain accepts for the two wasm profiles, canonicalised
/// before the table lookup so `--target wasm32-wasip1` reaches the measured
/// `wasm32-unknown-wasip1` entry without a `clang` probe.
pub def TargetSpec.alias (name : String) : String :=
    if String.beq name "wasm32-wasip1" then "wasm32-unknown-wasip1"
    else if String.beq name "wasm32-wasi" then "wasm32-unknown-wasip1"
    else name

/// The `-mtriple` and ABI flags `llc` gets for this target. Empty for a
/// native target, which is what keeps this change out of the native argv.
def TargetSpec.llc_argv (t : TargetSpec) : List String :=
    if String.is_empty t.llc_triple
    then t.llc_flags
    else List.cons (String.concat "-mtriple=" t.llc_triple) t.llc_flags

/// `--target`'s value -> the spec to build with.
///
/// An empty name is the machine this compiler is running on. A name in
/// `known_targets` is taken verbatim. Anything else is resolved from the
/// spelling the toolchain itself canonicalises to -- `wasm32-wasip1` answers
/// `wasm32-unknown-wasip1`, so a resolver keyed on what the user TYPED would
/// miss the entry the emitter and llc need -- and then accepted only if llc
/// registers its architecture. `--print-targets` answers the same question at
/// length.
///
/// The two lookups are deliberate: the measured five spellings resolve with no
/// fork at all, and only a name that is already unrecognised pays for the
/// probe.
#[partial]
pub def TargetSpec.resolve (name : String) : IO (Result String TargetSpec) := do {
    if String.is_empty name then do {
        let native <- TargetSpec.native;
        return (Result.ok native)
    } else do {
        match TargetSpec.lookup TargetSpec.known_targets (TargetSpec.alias name) {
            Option.some t => return (Result.ok t),
            Option.none => TargetSpec.resolve_unrecognised (TargetSpec.alias name),
        }
    }
}

/// `--target`'s value when it is not one of the measured spellings.
///
/// Split out of `resolve` only so that the `canonical` probe -- a dotted bind
/// -- does not sit immediately before a `match`; see `run_test_loop_codegen`
/// in `cli/src/main.mo` for what that costs.
#[partial]
def TargetSpec.resolve_unrecognised (name : String) : IO (Result String TargetSpec) := do {
    let want <- TargetSpec.canonical name;
    match TargetSpec.lookup TargetSpec.known_targets want {
        Option.some t => return (Result.ok t),
        Option.none => TargetSpec.unvalidated want,
    }
}

/// `want` (canonical, and not in `known_targets`) -> a spec, or a rejection.
///
/// Validation is by ARCHITECTURE, never by triple: llc lists architectures
/// (`x86-64`, not `x86_64-unknown-linux-gnu`), and it is llc that has to accept
/// what comes out of here. An llc that lists nothing at all is an absent
/// oracle, not a target set of zero -- validating against it would reject every
/// name -- so the target is accepted with a note, the same loud fallback
/// `TargetSpec.native` makes.
#[partial]
def TargetSpec.unvalidated (want : String) : IO (Result String TargetSpec) := do {
    let archs <- TargetSpec.registered_archs;
    if List.is_empty archs then do {
        println (String.concat "note: `llc --version` listed no registered targets; accepting " want);
        return (Result.ok (TargetSpec.mk want "" List.empty))
    } else if TargetSpec.arch_registered archs want then
        return (Result.ok (TargetSpec.mk want "" List.empty))
    else
        return (Result.err (TargetSpec.unknown_message want))
}

/// The spelling the toolchain canonicalises `name` to.
///
/// `clang --print-target-triple` echoes an unknown target VERBATIM, so this
/// canonicalises and does not validate -- `--target wasm32-wasip1` is how it
/// earns its keep. The nix wrapper PREPENDS its multi-target warning, so the
/// answer is the LAST non-empty line, unlike `-dumpmachine`'s first (see
/// `last_line`). A cc that cannot answer at all -- the cross legs put a
/// two-line `clang` shim on PATH that execs a gcc wrapper, which has no such
/// flag -- gets a note and the name stands as typed.
#[partial]
def TargetSpec.canonical (name : String) : IO String := do {
    let cap <- Proc.capture "clang" ["--print-target-triple", String.concat "--target=" name];
    match cap {
        Pair.pair code out => do {
            if code == 0 then do {
                let probed := TargetSpec.last_line out;
                if String.is_empty probed then do {
                    println (String.concat "note: `clang --print-target-triple` named no triple for " name);
                    return name
                } else return probed
            } else do {
                println (String.concat "note: `clang` cannot spell a triple for " name);
                return name
            }
        }
    }
}

/// Whether `t` answers to `triple`: either spelling, because `--target` accepts
/// the one `print-targets` prints in the parens as well as the table's. An
/// empty `llc_triple` names nothing -- without that guard every flagless entry
/// would answer to "".
def TargetSpec.names (t : TargetSpec) (triple : String) : Bool :=
    String.beq t.triple triple
        || (not (String.is_empty t.llc_triple) && String.beq t.llc_triple triple)

/// The first entry of `specs` that `names` accepts for `triple`.
#[partial]
def TargetSpec.lookup (specs : List TargetSpec) (triple : String) : Option TargetSpec :=
    match specs {
        List.empty => Option.none,
        List.cons hd tl =>
            if TargetSpec.names hd triple then Option.some hd else TargetSpec.lookup tl triple,
    }

/// The table's entry for `triple`, or a bare spec that is told no `-mtriple`.
///
/// Pure, so `native` consults the table without a second probe: a host the
/// table measured -- riscv64 is the one that matters -- gets its ABI and PIC
/// flags, where a host it did not (darwin's version-suffixed
/// `arm64-apple-darwin24.x`) gets today's flagless spec. x86_64-unknown-linux-gnu
/// is a table hit whose entry is already flagless, so its native argv is
/// byte-identical to what it was before targets existed.
#[partial]
def TargetSpec.table_or (triple : String) : TargetSpec :=
    match TargetSpec.lookup TargetSpec.known_targets triple {
        Option.some t => t,
        Option.none => TargetSpec.mk triple "" List.empty,
    }

/// The triples a store may hold artifacts under, for `gc` to spare.
///
/// A build keys with the RESOLVED spec's `triple`, so the table's own fields
/// cover every `--target` -- `resolve` answers a table hit with the entry
/// verbatim, either spelling of it. `native_triple` is appended because a host
/// the table does not know (darwin's version-suffixed `arm64-apple-darwin24.x`)
/// keys under its probe verbatim. A `--target` accepted by `unvalidated` keys
/// under a name no list here holds, so `gc` still collects it.
#[partial]
pub def TargetSpec.keep_triples (native_triple : String) : List String :=
    List.append (TargetSpec.triples_of TargetSpec.known_targets) [native_triple]

/// The `triple` field of each spec, in order.
#[partial]
def TargetSpec.triples_of (specs : List TargetSpec) : List String :=
    match specs {
        List.empty => List.empty,
        List.cons hd tl => List.cons hd.triple (TargetSpec.triples_of tl),
    }

/// The architectures llc on PATH was built with, from `llc --version`.
#[partial]
pub def TargetSpec.registered_archs : IO (List String) := do {
    let cap <- Proc.capture "llc" ["--version"];
    match cap {
        Pair.pair _code out => return (TargetSpec.archs_of out),
    }
}

/// The `Registered Targets:` block's arch words -- the first token of every
/// line after that header. An output with no header (a failed `llc`) is empty,
/// which callers must read as "no oracle", not "no targets".
#[partial]
def TargetSpec.archs_of (text : String) : List String :=
    TargetSpec.archs_after text false

/// `rest` shrinks by one line per call and the empty `rest` is the
/// terminator. Without that case the blank-line skip below cannot stop --
/// `line_rest ""` is `""` too, so it recurs forever and the compiled driver
/// dies on the stack (the self-hosted checker sees nothing wrong).
#[partial]
def TargetSpec.archs_after (rest : String) (seen : Bool) : List String :=
    if String.is_empty rest
    then List.empty
    else let line := String.trim (TargetSpec.up_to "\n" rest) in
    if String.is_empty line then TargetSpec.archs_after (TargetSpec.line_rest rest) seen
    else if seen then List.cons (TargetSpec.up_to " " line) (TargetSpec.archs_after (TargetSpec.line_rest rest) seen)
    else if String.beq line "Registered Targets:" then TargetSpec.archs_after (TargetSpec.line_rest rest) true
    else TargetSpec.archs_after (TargetSpec.line_rest rest) seen

/// Whether llc's registered `archs` covers the architecture `triple` names.
///
/// Prefix, with `_` and `-` dropped from both sides: llc registers `x86-64`
/// where triples say `x86_64`, `riscv64` where they say `riscv64gc` (llc
/// rejects that spelling itself), and `thumb` where they say `thumbv7em`. A
/// false accept is the safe direction -- llc fails loudly on its own -- where a
/// false reject would refuse a target that works.
#[partial]
pub def TargetSpec.arch_registered (archs : List String) (triple : String) : Bool :=
    TargetSpec.any_arch archs (TargetSpec.letters (TargetSpec.first_component triple))

#[partial]
def TargetSpec.any_arch (archs : List String) (want : String) : Bool :=
    match archs {
        List.empty => false,
        List.cons hd tl =>
            if String.starts_with (TargetSpec.letters hd) want then true
            else TargetSpec.any_arch tl want,
    }

/// `s` with `_` and `-` dropped, so the two spellings of one arch compare equal.
#[partial]
def TargetSpec.letters (s : String) : String :=
    TargetSpec.letters_from s (String.length s) 0

#[terminating]
def TargetSpec.letters_from (s : String) (len : I64) (i : I64) : String :=
    if I64.lt i len then
        let c := String.slice s i 1 in
        let rest := TargetSpec.letters_from s len (i + 1) in
        if String.beq c "_" then rest
        else if String.beq c "-" then rest
        else String.concat c rest
    else ""

/// `triple`'s architecture word: everything before its first `-`.
def TargetSpec.first_component (triple : String) : String :=
    TargetSpec.up_to "-" triple

/// One `--print-targets` line: the triple, and llc's argv when it says more
/// than the triple does.
pub def TargetSpec.describe (t : TargetSpec) : String :=
    let argv := TargetSpec.joined " " (TargetSpec.llc_argv t) in
    if String.is_empty argv then t.triple
    else String.concat t.triple (String.concat "  (llc " (String.concat argv ")"))

/// A `--print-targets` line per spec, newline-separated.
#[partial]
pub def TargetSpec.describe_all (archs : List String) (specs : List TargetSpec) : String :=
    match specs {
        List.empty => "",
        List.cons hd tl =>
            let rest := TargetSpec.describe_all archs tl in
            let line := TargetSpec.marked archs hd in
            if String.is_empty rest then line else String.concat line (String.concat "\n" rest),
    }

/// `t`'s line, marked when this llc cannot build for it.
#[partial]
def TargetSpec.marked (archs : List String) (t : TargetSpec) : String :=
    if TargetSpec.arch_registered archs t.triple then TargetSpec.describe t
    else String.concat (TargetSpec.describe t)
        (String.concat "  (llc registers no " (String.concat (TargetSpec.first_component t.triple) ")"))

/// `xs` joined by `sep`; empty for an empty list.
#[partial]
pub def TargetSpec.joined (sep : String) (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons hd tl =>
            let rest := TargetSpec.joined sep tl in
            if String.is_empty rest then hd else String.concat hd (String.concat sep rest),
    }

/// The `--print-targets` architecture list, or the note that there is none --
/// an llc that could not answer must not print as an empty list of targets.
pub def TargetSpec.arch_line (archs : List String) : String :=
    if List.is_empty archs
    then "(llc --version listed none; `--target` accepts any name unvalidated)"
    else TargetSpec.joined ", " archs

/// `triple` -> what `--target` fails with.
#[partial]
def TargetSpec.unknown_message (triple : String) : String :=
    String.concat "unknown target `"
        (String.concat triple
            (String.concat "`: llc registers no `"
                (String.concat (TargetSpec.first_component triple)
                    "` architecture -- `monad print-targets` lists what this compiler knows")))

/// The target this compiler is running on.
///
/// `clang -dumpmachine` rather than `llc --version`'s "Default target": the
/// C compiler is the one that has to agree with the objects llc emits, and
/// it is the one the link step will call. The probe is then answered from
/// `known_targets`, so a host the table measured gets its flags (see
/// `table_or`). A toolchain that cannot answer
/// leaves the historical x86_64 default in place, loudly -- a silent
/// fallback here would compile for the wrong machine and fail at ld, which
/// is a worse diagnostic than the one printed.
#[partial]
pub def TargetSpec.native : IO TargetSpec := do {
    let cap <- Proc.capture "clang" ["-dumpmachine"];
    match cap {
        Pair.pair _ out => do {
            let probed := TargetSpec.first_line out;
            if String.is_empty probed then do {
                println "note: `clang -dumpmachine` named no triple; assuming x86_64-unknown-linux-gnu";
                return (TargetSpec.table_or "x86_64-unknown-linux-gnu")
            } else return (TargetSpec.table_or probed)
        }
    }
}

/// `text`'s first line, trimmed.
///
/// `Proc.capture` merges stderr, and a wrapper that warns puts the warning on
/// line 1 -- but `clang -dumpmachine` puts its answer on its FIRST line, so
/// this is the end of the stream the answer is at for that tool. A tool that
/// appends to stderr rather than prepending needs `last_line` instead.
#[partial]
def TargetSpec.first_line (text : String) : String :=
    String.trim (TargetSpec.up_to "\n" text)

/// `text`'s last non-empty line, trimmed -- for a tool that appends rather
/// than prepends, which is `clang --print-target-triple` behind the nix
/// wrapper's warning.
#[partial]
def TargetSpec.last_line (text : String) : String :=
    TargetSpec.last_line_go text ""

#[partial]
def TargetSpec.last_line_go (rest : String) (acc : String) : String :=
    if String.is_empty (String.trim rest) then acc
    else TargetSpec.last_line_go (TargetSpec.line_rest rest) (TargetSpec.first_line rest)

/// `text` after its first line (empty when it has no newline left).
#[partial]
def TargetSpec.line_rest (text : String) : String :=
    let at := TargetSpec.char_at text (String.length text) 0 "\n" in
    if I64.lt at 0 then "" else String.drop (at + 1) text

/// `s` up to its first `ch`, or the whole of `s` when `ch` does not occur.
def TargetSpec.up_to (ch : String) (s : String) : String :=
    let at := TargetSpec.char_at s (String.length s) 0 ch in
    if I64.lt at 0 then s else String.slice s 0 at

/// Byte index of the first `ch` in `text` at or after `from`, or -1.
///
/// `#[terminating]`: `from` counts UP, which the structural termination
/// checker cannot see is bounded by `len`.
#[terminating]
def TargetSpec.char_at (text : String) (len : I64) (from : I64) (ch : String) : I64 :=
    if I64.lt from len
    then if String.beq (String.slice text from 1) ch then from
         else TargetSpec.char_at text len (from + 1) ch
    else -1

/// The header line and the indented `arch - description` lines llc prints, with
/// the versions and build flags before them, which must not become arch words.
#[test]
def test_archs_of_reads_the_registered_block : Bool :=
    let text := "LLVM (http://llvm.org/):\n  LLVM version 21.1.8\n  Optimized build.\n\n  Registered Targets:\n    aarch64     - AArch64 (little endian)\n    riscv64     - 64-bit RISC-V\n    x86-64      - 64-bit X86: EM64T and AMD64\n" in
    String.beq (TargetSpec.joined "," (TargetSpec.archs_of text)) "aarch64,riscv64,x86-64"

/// An llc that failed prints no header, which is no oracle -- callers accept
/// the target rather than reject it -- so this must be empty, not garbage.
#[test]
def test_archs_of_without_the_header_is_empty : Bool :=
    List.is_empty (TargetSpec.archs_of "LLVM (http://llvm.org/):\n  LLVM version 21.1.8\n")

/// The three measured spellings llc's arch words disagree with triples about.
#[test]
def test_arch_registered_normalises_the_spellings : Bool :=
    let archs := ["aarch64", "riscv64", "thumb", "wasm32", "x86-64"] in
    TargetSpec.arch_registered archs "x86_64-unknown-linux-gnu"
        && TargetSpec.arch_registered archs "riscv64gc-unknown-linux-gnu"
        && TargetSpec.arch_registered archs "aarch64-apple-darwin"
        && TargetSpec.arch_registered archs "thumbv7em-none-eabi"
        && TargetSpec.arch_registered archs "wasm32-unknown-wasip1"

#[test]
def test_arch_registered_rejects_an_unknown_architecture : Bool :=
    TargetSpec.arch_registered ["aarch64", "x86-64"] "bogus-target-xyz" == false

/// The llc argv is printed only when it says more than the triple already does,
/// so the four targets that need no extra spelling stay one token long.
#[test]
def test_describe_names_the_llc_spelling_only_when_it_differs : Bool :=
    let riscv := TargetSpec.mk "riscv64gc-unknown-linux-gnu" "riscv64-unknown-linux-gnu" ["-mattr=+m,+a,+f,+d,+c", "-target-abi=lp64d", "-relocation-model=pic"] in
    let linux := TargetSpec.mk "x86_64-unknown-linux-gnu" "" List.empty in
    String.beq (TargetSpec.describe linux) "x86_64-unknown-linux-gnu"
        && String.beq (TargetSpec.describe riscv)
            "riscv64gc-unknown-linux-gnu  (llc -mtriple=riscv64-unknown-linux-gnu -mattr=+m,+a,+f,+d,+c -target-abi=lp64d -relocation-model=pic)"

#[test]
def test_describe_all_marks_what_this_llc_cannot_build : Bool :=
    String.beq (TargetSpec.describe_all ["aarch64"] [
        TargetSpec.mk "aarch64-unknown-linux-gnu" "" List.empty,
        TargetSpec.mk "wasm32-unknown-wasip1" "" List.empty,
    ]) "aarch64-unknown-linux-gnu\nwasm32-unknown-wasip1  (llc registers no wasm32)"

#[test]
def test_unknown_message_names_the_architecture : Bool :=
    String.beq (TargetSpec.unknown_message "bogus-target-xyz")
        "unknown target `bogus-target-xyz`: llc registers no `bogus` architecture -- `monad print-targets` lists what this compiler knows"

/// The llc spelling reaches the same entry as the measured one, so
/// `--target riscv64-unknown-linux-gnu` gets lp64d and PIC instead of the
/// empty argv a table miss would hand it.
#[test]
def test_lookup_answers_the_llc_spelling_too : Bool :=
    String.beq (TargetSpec.describe (TargetSpec.table_or "riscv64-unknown-linux-gnu"))
        (TargetSpec.describe (TargetSpec.table_or "riscv64gc-unknown-linux-gnu"))

/// The x86_64 entry is a table hit and is already flagless, which is what keeps
/// the native argv byte-identical to what it was before targets existed.
#[test]
def test_x86_64_stays_flagfree : Bool :=
    List.is_empty (TargetSpec.llc_argv (TargetSpec.table_or "x86_64-unknown-linux-gnu"))

/// A triple the table does not know passes no `-mtriple` and no flags, exactly
/// as `unvalidated` builds it: a miss, not a wrong hit.
#[test]
def test_unknown_triple_is_untouched : Bool :=
    String.beq (TargetSpec.describe (TargetSpec.table_or "bogus-target-xyz")) "bogus-target-xyz"

/// An empty name is not a spelling of anything. Every entry but riscv64 has an
/// empty `llc_triple`, so without the guard in `names` the first of them would
/// answer it.
#[test]
def test_empty_name_matches_no_entry : Bool :=
    match TargetSpec.lookup TargetSpec.known_targets "" {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_target_kind_of_triple : Bool :=
    String.beq (TargetKind.name (TargetKind.of_triple "wasm32-unknown-wasip1")) "wasi"
        && String.beq (TargetKind.name (TargetKind.of_triple "wasm32-unknown-unknown")) "web"
        && String.beq (TargetKind.name (TargetKind.of_triple "x86_64-unknown-linux-gnu")) "native"

#[test]
def test_wasm_aliases_resolve_to_a_known_entry : Bool :=
    let t := TargetSpec.table_or (TargetSpec.alias "wasm32-wasip1") in
    String.beq (TargetSpec.alias "wasm32-wasip1") "wasm32-unknown-wasip1"
        && String.beq (TargetSpec.alias "wasm32-wasi") "wasm32-unknown-wasip1"
        && String.beq t.triple "wasm32-unknown-wasip1"

#[test]
def test_wasm64_is_classified_wasm_but_rejected : Bool :=
    String.beq (TargetKind.name (TargetKind.of_triple "wasm64-unknown-unknown")) "web"
        && Bool.not (TargetPlan.is_supported_wasm_triple "wasm64-unknown-unknown")
        && TargetPlan.is_supported_wasm_triple "wasm32-unknown-wasip1"

#[test]
def test_output_ext_is_shared_by_both_wasm_profiles : Bool :=
    String.beq (TargetKind.output_ext TargetKind.wasi) ".wasm"
        && String.beq (TargetKind.output_ext TargetKind.web) ".wasm"
        && String.beq (TargetKind.output_ext TargetKind.native) ""
        && String.beq (TargetPlan.output_name_for TargetKind.web "fib") "fib.wasm"
        && String.beq (TargetPlan.output_name_for TargetKind.web "fib.wasm") "fib.wasm"

#[test]
def test_wasm_output_gets_the_wasm_suffix_once : Bool :=
    let plan := TargetPlan.for_wasm TargetKind.wasi "wasm32-unknown-wasip1" "/sdk/clang" "/sdk/sysroot" in
    String.beq (TargetPlan.output_name plan "fib") "fib.wasm"
        && String.beq (TargetPlan.output_name plan "fib.wasm") "fib.wasm"

#[test]
def test_native_output_name_is_untouched : Bool :=
    String.beq (TargetPlan.output_name (TargetPlan.native_plan "x86_64-unknown-linux-gnu") "fib") "fib"
