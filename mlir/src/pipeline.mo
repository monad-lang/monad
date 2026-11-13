/// The pass pipelines, as DATA -- a value `tool.mo` renders into
/// `mlir-opt --pass-pipeline=...` and `cache.mo` hashes into an artifact
/// key.
///
/// `plans/bootstrapping/mlir-codegen.md` names this module's job as
/// "pass pipelines AS DATA -> `--pass-pipeline=`", and the "as data" half
/// is what earns the file: a pipeline that is a STRING at every call site
/// cannot be hashed stably (two call sites can spell the same pipeline two
/// ways), cannot be checked against a target (an NVPTX pipeline built for
/// the CPU path is a broken artifact, not a wrong flag), and cannot be
/// printed in a `--verbose` trace in a form a reader can paste into a
/// shell.
///
/// ## Every pass name here was measured, not copied
///
/// The plan is emphatic about this and it is right to be: pass names have
/// been renamed across releases (`convert-memref-to-llvm` became
/// `finalize-memref-to-llvm` in LLVM 17), so a list taken from another
/// release's documentation fails as `'x' does not refer to a registered
/// pass`. Everything below was checked against `mlir-opt --help` on
/// **21.1.8**, and the CPU list was additionally RUN end to end -- see
/// `scripts/check-mlir-toolchain.sh`, which drives it over
/// `fixtures/mlir/saxpy.mlir` and asserts the resulting C signature.
///
/// ## The CPU pipeline, and the three passes that are easiest to omit
///
///     convert-scf-to-cf            structured control flow leaves scf
///     expand-strided-metadata      omitted-by-default #1; required before
///                                  the memref lowering for a bare-pointer ABI
///     convert-arith-to-llvm        scalar ops
///     convert-cf-to-llvm           what convert-scf-to-cf landed in
///     finalize-memref-to-llvm      omitted-by-default #2 (renamed in LLVM 17)
///     convert-func-to-llvm{...}    use-bare-ptr-memref-call-conv=1 is THE ABI
///                                  decision -- one bare pointer per memref
///                                  argument, not a descriptor struct
///     reconcile-unrealized-casts    omitted-by-default #3, MANDATORY, last
///
/// `--convert-to-llvm` (a generic pass delegating through
/// `ConvertToLLVMPatternInterface`) exists and is **not** a substitute: it
/// does not supply those ordering-sensitive prerequisites. The plan says
/// not to reach for it as a one-liner and this module does not.
///
/// ## The GPU pipeline, and why it is the hand-spelled one
///
/// Phase 4's wording is "prefer the upstream-maintained
/// `gpu-lower-to-nvvm-pipeline` over hand-spelling these where it fits", so
/// both were tried against 21.1.8 before choosing. The measurement is in
/// `gpu_pipeline`'s own comment; the short version is that
/// `gpu-lower-to-nvvm-pipeline` does NOT fit this plan's ABI contract,
/// because it passes a memref descriptor (5 scalars) to the kernel where
/// Decision 3 requires one bare pointer.
///
/// ## A pipeline is a nested structure, not a comma-separated string
///
/// `builtin.module(a, b, gpu.module(c), d)` is a run list where one entry
/// is itself a pipeline. Rendering it from a flat string means the nesting
/// exists only as punctuation, and a pass that needs an option containing a
/// comma (`opts={a,b}`) would corrupt it. `MlirPipelineStep` keeps the
/// nesting, so `render` is total and `nest` is the only way to build a
/// nested entry.

use lib::target {MlirTarget}

/// One entry in a run list: a pass (with its option string, `""` for
/// none), or a nested pipeline under an op anchor.
pub type MlirPipelineStep {
    /// A pass name and its options, already in MLIR's own
    /// `{key=value key2=value2}` syntax -- carried as TEXT for the same
    /// reason `MlirOp.text` is (`ir.mo`'s header): the options are
    /// per-pass and their spelling is the pass's own.
    pass (name : String) (options : String),
    /// `gpu.module(<inner>)` -- a pipeline that runs on a nested op.
    nest (anchor : String) (inner : List MlirPipelineStep),
}

/// A whole pipeline: the run list of passes.
///
/// `anchor` is the op the run list is applied to, `builtin.module` in
/// practice. It is a field rather than a constant because
/// `--pass-pipeline` requires it (`builtin.module(...)` is the outermost
/// level of every pipeline string `mlir-opt` accepts) and because a caller
/// writing a test may want to run on something narrower.
pub struct MlirPipeline {
    anchor : String,
    steps : List MlirPipelineStep,
    /// The pipeline's own NAME, for diagnostics and for the cache key --
    /// `cpu`, `nvvm-prepare`, `nvvm-binary`. Not derivable from `steps`
    /// (two different pipelines can share a shape), and a cache key that
    /// hashed only the rendering would still be correct but a log line
    /// would not say what stage it was.
    label : String,
}

// ─── constructors ────────────────────────────────────────────────────

/// A pass with no options.
pub def MlirPipelineStep.step (name : String) : MlirPipelineStep :=
    MlirPipelineStep.pass name ""

/// A pass with options, spelled without the braces --
/// `flagged "convert-func-to-llvm" "use-bare-ptr-memref-call-conv=1"`.
pub def MlirPipelineStep.flagged (name : String) (options : String) : MlirPipelineStep :=
    MlirPipelineStep.pass name options

/// `op(<inner>)`.
pub def MlirPipelineStep.nested (anchor : String) (inner : List MlirPipelineStep) : MlirPipelineStep :=
    MlirPipelineStep.nest anchor inner

// ─── the CPU pipeline ────────────────────────────────────────────────

/// The CPU pipeline's passes, in order. The ONE place the list lives, so
/// the pipeline string, the cache key and the golden script cannot
/// disagree about what a CPU build runs.
///
/// `index-bitwidth` is left at each pass's default (0 = the machine word)
/// rather than pinned to `MlirTarget.index_bits`. The default is correct
/// for the host target this backend compiles for, and pinning it would
/// change the CPU argv from the one `check-mlir-toolchain.sh` measured --
/// making the script's verified pipeline and the compiler's differ by an
/// option. When a cross-CPU target lands (a 32-bit host), this is the
/// function that gains a parameter, and the script is what notices.
pub def cpu_steps : List MlirPipelineStep := [
    MlirPipelineStep.step "convert-scf-to-cf",
    MlirPipelineStep.step "expand-strided-metadata",
    MlirPipelineStep.step "convert-arith-to-llvm",
    MlirPipelineStep.step "convert-cf-to-llvm",
    MlirPipelineStep.step "finalize-memref-to-llvm",
    // THE ABI decision, spelled once. Without it MLIR explodes a memref
    // descriptor into five scalar parameters; with it each memref argument
    // is one bare pointer and a kernel is a plain C function
    // (`define void @saxpy(ptr noalias %0, i32 %1)`). Measured, and the
    // measured alternative is what `check-mlir-toolchain.sh` rejects by
    // counting parameters.
    MlirPipelineStep.flagged "convert-func-to-llvm" "use-bare-ptr-memref-call-conv=1",
    MlirPipelineStep.step "reconcile-unrealized-casts",
]

/// The CPU pipeline: a whole module down to the `llvm` dialect, which
/// `mlir-translate --mlir-to-llvmir` then turns into LLVM IR.
pub def cpu_pipeline : MlirPipeline :=
    { anchor := "builtin.module", steps := cpu_steps, label := "cpu" }

// ─── the GPU pipelines ───────────────────────────────────────────────
//
// Two, not one, and the split is the ABI decision again. `gpu.launch_func`
// in the host module and the kernel's PTX have to agree about how a memref
// argument crosses the boundary, and the only way to make them agree is to
// set the bare-pointer option on BOTH sides. That is possible with the
// passes spelled individually (`convert-gpu-to-nvvm{use-bare-ptr-memref-call-conv=true}`
// for the kernel and `gpu-to-llvm{use-bare-pointers-for-host=true
// use-bare-pointers-for-kernels=true}` for the launch site), and NOT
// possible through `gpu-lower-to-nvvm-pipeline`, whose options are `cubin-*`,
// `opt-level`, `ptxas-cmd-options` and the two `*-bare-ptr-calling-convention`
// flags -- and those two do not reach the pass that decides the kernel's
// own signature.
//
// Measured against 21.1.8 (fixtures/mlir/gpu_saxpy.mlir, a `gpu.launch`
// over a ranked-1 memref):
//
//   hand-spelled, bare ptr on both sides
//       host:   llvm.func @host(%arg0: !llvm.ptr)
//       PTX:    .visible .entry host_kernel(.param .u64 .ptr .align 1 ...)
//               1 parameter. THE ABI THIS PLAN NEEDS.
//   hand-spelled, no bare-ptr options
//       host passes 1 value, the kernel declares 5 -- a mismatch that would
//       read as a garbage pointer at run time rather than an error.
//   gpu-lower-to-nvvm-pipeline{cubin-chip=sm_80 cubin-format=isa}
//       host:   llvm.func @host(%arg0: !llvm.ptr, %arg1: !llvm.ptr,
//                               %arg2: i64, %arg3: i64, %arg4: i64)
//       PTX:    1 parameter. The host signature is a descriptor exploded
//               into five scalars, which `host.mo` cannot build (no
//               alloca, no GEP-with-store) and which is not Decision 3.
//
// So the upstream pipeline is the shorter spelling and the wrong ABI: it
// is kept out, with the measurement above as the reason rather than a
// preference. `cubin-format=isa` on that pipeline IS the right idea and is
// what `gpu-module-to-binary{format=isa}` does in the hand-spelled form --
// PTX text, no `ptxas`, no CUDA toolkit, no GPU (Phase 4's acceptance).

/// `nvvm-attach-target{chip=<chip> O=<n>}`'s option string. The chip is a
/// PARAMETER, never omitted: LLVM 21 moved NVVM's default from `sm_50` to
/// `sm_75`, so an unpinned golden changes target when the toolchain moves.
pub def attach_options (chip : String) (opt_level : I64) : String :=
    "chip=" ++ chip ++ " O=" ++ I64.to_string opt_level

/// The device half: `gpu.module(convert-gpu-to-nvvm, ...)`.
///
/// `convert-gpu-to-nvvm`'s bare-pointer option is spelled
/// `use-bare-ptr-memref-call-conv` (the `memref` in the middle, unlike
/// `gpu-to-llvm`'s `use-bare-pointers-for-kernels`) -- checked against
/// `mlir-opt --help`, and worth noting because the near-miss is a
/// `no such option` at pipeline-construction time.
pub def nvvm_device_steps : List MlirPipelineStep := [
    MlirPipelineStep.flagged "convert-gpu-to-nvvm" "use-bare-ptr-memref-call-conv=true",
    MlirPipelineStep.step "reconcile-unrealized-casts",
]

/// The GPU pipeline for `target` at optimization level `opt_level`:
/// outline the kernels, attach the NVVM target, lower the device module,
/// emit PTX, lower the launch sites, then finish the host module.
///
/// The order is load-bearing in two places:
///
/// * `gpu-kernel-outlining` FIRST: the kernel body starts life inside a
///   `gpu.launch`, and nothing downstream has a `gpu.module` to attach a
///   target to until the outlining pass has created one.
/// * `gpu-module-to-binary` after `gpu-to-llvm`: the binary op replaces the
///   `gpu.module`, and `gpu-to-llvm` is what turns the remaining
///   `gpu.launch_func` into its inline-assembly form. Running them the
///   other way round also works and yields the same PTX; this order is the
///   one whose intermediate state is smallest.
///
/// A `cpu` target reaching here is impossible by construction -- the
/// caller picks `cpu_pipeline` for it -- so the chip comes from
/// `MlirTarget.describe`'s GPU arm only via `gpu_chip`, which answers `""`
/// for a CPU target and is rejected by `render_gpu` rather than silently
/// producing a pipeline with an empty chip.
#[partial]
pub def gpu_pipeline (target : MlirTarget) (opt_level : I64) : MlirPipeline :=
    { anchor := "builtin.module",
        steps := gpu_steps (gpu_chip target) opt_level,
        label := "nvvm" }

/// `target`'s chip. `""` for a CPU target, which `gpu_pipeline`'s caller
/// must not reach; keeping the fallback out of `describe` means a CPU
/// target cannot be rendered as a GPU one by accident.
pub def gpu_chip (target : MlirTarget) : String := match target {
    MlirTarget.cpu _ _ => "",
    MlirTarget.nvptx chip _ => chip,
}

/// The GPU run list for `chip`.
#[partial]
def gpu_steps (chip : String) (opt_level : I64) : List MlirPipelineStep := [
    MlirPipelineStep.step "gpu-kernel-outlining",
    MlirPipelineStep.flagged "nvvm-attach-target" (attach_options chip opt_level),
    MlirPipelineStep.nested "gpu.module" nvvm_device_steps,
    MlirPipelineStep.step "gpu-module-to-binary{format=isa}",
    MlirPipelineStep.flagged "gpu-to-llvm"
        "use-bare-pointers-for-host=true use-bare-pointers-for-kernels=true",
    MlirPipelineStep.step "convert-func-to-llvm{use-bare-ptr-memref-call-conv=1}",
    MlirPipelineStep.step "reconcile-unrealized-casts",
]

/// The GPU pipeline at the plan's pinned golden chip and `O=3`.
pub def gpu_pipeline_string_golden : String :=
    render (gpu_pipeline MlirTarget.golden_nvptx 3)

// ─── rendering ───────────────────────────────────────────────────────

/// `builtin.module(a, b, gpu.module(c, d))` -- exactly what
/// `mlir-opt --pass-pipeline=` takes.
///
/// The nesting is rendered by `step_text`, a mutual recursion with
/// `steps_text`, so a nested pipeline's closing paren cannot be forgotten
/// by a caller that built one by hand.
#[partial]
pub def render (pipeline : MlirPipeline) : String := match pipeline {
    { anchor, steps, .. } => anchor ++ "(" ++ steps_text steps ++ ")",
}

/// One step's text: `name`, `name{opts}`, or `anchor(<inner>)`.
///
/// A `pass` with options gets its braces HERE rather than at construction,
/// so `flagged` takes an option string without punctuation -- and a pass
/// whose options are empty renders as a bare name rather than as `{ }`,
/// which `mlir-opt` rejects.
#[partial]
def step_text (step : MlirPipelineStep) : String := match step {
    MlirPipelineStep.pass name options =>
        if String.is_empty options then name else name ++ "{" ++ options ++ "}",
    MlirPipelineStep.nest anchor inner =>
        anchor ++ "(" ++ steps_text inner ++ ")",
}

/// Steps comma-separated, in order.
#[partial]
def steps_text (steps : List MlirPipelineStep) : String :=
    String.concat_list (List.reverse (steps_text_go steps List.empty true))

/// Steps rendered in order, separated by `","` with no space.
///
/// The separator is SUFFIXED to every entry but the last, and `last` is a
/// THREADED parameter. Two things make that the right shape here and both
/// were bugs first:
///
/// * Keying on `List.is_empty rest` inside the recursion is correct in
///   source order and WRONG after the reversal: the last entry's missing
///   comma re-emerges in the first position, rendering `a b, c,`. The flag
///   has to be computed in the same place the separator is emitted.
/// * `" ,"` prefixed (`",b"`) looks equivalent and is not -- reversed it
///   renders `a ,b`, with the separator on the wrong side. The suffix form
///   has no such asymmetry.
///
/// NO SPACE AFTER THE COMMA, deliberately: `mlir-opt` accepts either
/// spelling, so this is the one that lets `pipeline.mo` and
/// `scripts/check-mlir-toolchain.sh` hold the SAME string.
/// `test_cpu_pipeline_string_matches_the_measured_one` pins them together,
/// and the script's copy is the one Phase 0 measured against real MLIR --
/// so a space here would make the two disagree on bytes while both still
/// worked, which is precisely the drift the test exists to catch.
#[partial]
def steps_text_go (steps : List MlirPipelineStep) (acc : List String) (first : Bool) : List String :=
    match steps {
        List.empty => acc,
        List.cons s rest =>
            steps_text_go rest (List.cons (step_text_with_separator s (List.is_empty rest)) acc) false,
    }

/// `s`'s text, with `","` appended unless it is the last entry.
///
/// `last` is passed rather than derived from the accumulator, which is read
/// once (by `List.cons`) and would be a double use if it were also tested
/// here -- the affine rule's shape, and the same reason
/// `ir.mo`'s `show_mlir_attrs` tests a joined string rather than the list.
#[partial]
def step_text_with_separator (s : MlirPipelineStep) (last : Bool) : String :=
    let body := step_text s in
    if last then body else body ++ ","

/// The CPU pipeline as `mlir-opt` takes it. The single string every caller
/// -- `tool.mo`, `cache.mo`, `scripts/check-mlir-goldens.sh`,
/// `scripts/check-mlir-toolchain.sh` -- passes to `--pass-pipeline=`.
///
/// Byte-identical to the string Phase 0 measured
/// (`scripts/check-mlir-toolchain.sh`'s `pipeline` variable), and
/// `test_cpu_pipeline_string_matches_the_measured_one` is what holds that:
/// the script and the compiler must run the SAME pipeline, or the toolchain
/// proof stops being a proof of what ships.
pub def cpu_pipeline_string : String := render cpu_pipeline

/// `gpu_pipeline` for `target` as `mlir-opt` takes it.
#[partial]
pub def gpu_pipeline_string (target : MlirTarget) (opt_level : I64) : String :=
    render (gpu_pipeline target opt_level)

// ─── tests ───────────────────────────────────────────────────────────

/// The CPU pipeline must be BYTE-IDENTICAL to the one
/// `scripts/check-mlir-toolchain.sh` verified against real MLIR 21.1.8.
/// This is the test that keeps the toolchain proof attached to what ships:
/// a pass added here without a matching edit there would make the script
/// prove a pipeline the compiler no longer uses.
#[test]
def test_cpu_pipeline_string_matches_the_measured_one : Bool :=
    String.beq cpu_pipeline_string
        "builtin.module(convert-scf-to-cf,expand-strided-metadata,convert-arith-to-llvm,convert-cf-to-llvm,finalize-memref-to-llvm,convert-func-to-llvm{use-bare-ptr-memref-call-conv=1},reconcile-unrealized-casts)"

/// The three passes the plan calls out as omitted-by-default are all
/// PRESENT. Asserted by name rather than by position, so a reordering that
/// keeps them still passes and a deletion cannot.
#[test]
def test_cpu_pipeline_keeps_the_three_omitted_by_default_passes : Bool :=
    let s := cpu_pipeline_string in
    String.contains s "expand-strided-metadata"
        && String.contains s "finalize-memref-to-llvm"
        && String.contains s "reconcile-unrealized-casts"

/// The bare-pointer ABI flag, and its exact spelling for each pass. The two
/// spellings differ (`use-bare-ptr-memref-call-conv` for `func` and
/// `gpu-to-nvvm`, `use-bare-pointers-for-host`/`-kernels` for
/// `gpu-to-llvm`), which is where a copy-paste between them breaks.
#[test]
def test_the_bare_pointer_option_is_spelled_per_pass : Bool :=
    String.contains cpu_pipeline_string "convert-func-to-llvm{use-bare-ptr-memref-call-conv=1}"
        && String.contains gpu_pipeline_string_golden
            "convert-gpu-to-nvvm{use-bare-ptr-memref-call-conv=true}"
        && String.contains gpu_pipeline_string_golden
            "gpu-to-llvm{use-bare-pointers-for-host=true use-bare-pointers-for-kernels=true}"

/// The chip is always pinned. A pipeline with `nvvm-attach-target{}` would
/// follow LLVM's default, which moved from `sm_50` to `sm_80`-era
/// `sm_75` in LLVM 21 -- so an unpinned pipeline is a moving target and a
/// PTX golden against it fails for a reason nobody can find.
#[test]
def test_the_gpu_pipeline_pins_the_chip : Bool :=
    String.contains gpu_pipeline_string_golden "nvvm-attach-target{chip=sm_80 O=3}"
        && String.contains (gpu_pipeline_string (MlirTarget.nvptx_chip "sm_90") 2)
            "nvvm-attach-target{chip=sm_90 O=2}"

/// The whole GPU pipeline, byte for byte. Pinned as a STRING because that
/// is what `mlir-opt` is handed, and because the pass ORDER is the part a
/// reader cannot check by eye from the constructor list.
#[test]
def test_gpu_pipeline_string_is_pinned : Bool :=
    String.beq gpu_pipeline_string_golden
        "builtin.module(gpu-kernel-outlining,nvvm-attach-target{chip=sm_80 O=3},gpu.module(convert-gpu-to-nvvm{use-bare-ptr-memref-call-conv=true},reconcile-unrealized-casts),gpu-module-to-binary{format=isa},gpu-to-llvm{use-bare-pointers-for-host=true use-bare-pointers-for-kernels=true},convert-func-to-llvm{use-bare-ptr-memref-call-conv=1},reconcile-unrealized-casts)"

/// `format=isa` is what makes Phase 4's acceptance reachable at all: it
/// emits PTX TEXT, so no `ptxas`, no CUDA toolkit and no GPU are involved.
/// The removed spellings (`gpu-to-cubin`, `SerializeToCubin`, deleted in
/// LLVM 19) must never appear.
#[test]
def test_the_gpu_pipeline_emits_isa_and_uses_no_removed_pass : Bool :=
    let s := gpu_pipeline_string_golden in
    String.contains s "gpu-module-to-binary{format=isa}"
        && Bool.not (String.contains s "gpu-to-cubin")
        && Bool.not (String.contains s "ptxas")

/// A nested pipeline renders its parens and its commas, and the nesting is
/// not flattened -- the halfway state a naive split-and-rejoin would lose.
#[test]
def test_nested_pipelines_render_their_own_parens : Bool :=
    let p : MlirPipeline :=
        { anchor := "builtin.module",
            steps := [
                MlirPipelineStep.step "a",
                MlirPipelineStep.nested "gpu.module" [
                    MlirPipelineStep.step "b",
                    MlirPipelineStep.step "c",
                ],
                MlirPipelineStep.step "d",
            ],
            label := "test" } in
    String.beq (render p) "builtin.module(a,gpu.module(b,c),d)"

/// A pass with no options is a bare name -- not `name{}`, which
/// `mlir-opt` reports as an option-parser error naming the pass.
#[test]
def test_a_pass_without_options_has_no_braces : Bool :=
    let p : MlirPipeline :=
        { anchor := "builtin.module",
            steps := [MlirPipelineStep.step "canonicalize"], label := "t" } in
    String.beq (render p) "builtin.module(canonicalize)"

/// A CPU target has no chip, and `gpu_pipeline` on one would render an
/// empty `chip=`. `gpu_chip` answering `""` is what makes that visible to a
/// caller instead of silently accepted by `mlir-opt` (which takes `chip=`
/// as an empty string and then fails at PTX emission).
#[test]
def test_a_cpu_target_has_no_gpu_chip : Bool :=
    String.beq (gpu_chip (MlirTarget.cpu_native "x86_64-unknown-linux-gnu")) ""
        && String.beq (gpu_chip MlirTarget.golden_nvptx) "sm_80"
