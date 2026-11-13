/// Where a kernel is compiled FOR: the CPU this compiler runs on, or an
/// NVIDIA GPU. The vocabulary `pipeline.mo` turns into pass options and
/// `tool.mo` turns into `mlir-translate`/`llc` arguments.
///
/// ## Why this is not `llvm::TargetSpec`
///
/// `llvm/src/target.mo` answers a different question -- "what does `llc`
/// need told about this triple" -- and answers it with `llc_triple` and
/// `llc_flags`, because `llc` disagrees with `clang` about how riscv64 is
/// spelled. MLIR has no such vocabulary: `mlir-opt` takes the target as
/// PASS OPTIONS (`nvvm-attach-target{chip=sm_80}`), and its CPU lowering
/// takes an `index-bitwidth` integer rather than a triple. Sharing the type
/// would mean carrying three fields MLIR never reads and a
/// `llc_flags` list that means nothing here.
///
/// What IS shared is the SPELLING, because the two must agree: a kernel
/// compiled for `aarch64-apple-darwin` and host code compiled for
/// `aarch64-apple-darwin` are linked into one binary, so `cpu`'s `triple`
/// is the same string `llvm::TargetSpec.triple` holds. That is a
/// convention, not a type dependency -- and it has to be a convention,
/// because `mlir` must not depend on `codegen`/`lang` and `llvm` is a
/// sibling backend rather than a shared base. Adding `llvm` as a dependency
/// of `mlir` to share a record of five strings would put the CPU backend's
/// concerns inside the GPU one.
///
/// ## The NVPTX triple is not negotiable, so it is not a field
///
/// `nvptx64-nvidia-cuda` is the only triple the NVVM path accepts for a
/// 64-bit device module; there is no spelling question to answer, unlike
/// the host's `riscv64gc` vs `riscv64` split. So `nvptx` carries a CHIP and
/// FEATURES and gets the triple from a constant -- a caller cannot spell a
/// `nvptx` target that `mlir-opt` rejects for its triple.
///
/// ## `chip` is explicit and has a pinned default
///
/// `plans/bootstrapping/mlir-codegen.md` Phase 4: **always pin `chip=`
/// explicitly**, because LLVM 21 changed NVVM's default from `sm_50` to
/// `sm_75`. An unpinned pipeline therefore silently changes target with the
/// toolchain version -- a golden PTX file would go red for a reason nobody
/// could find in the emitter. `MlirTarget.nvptx` takes the chip, and
/// `default_chip` exists only so a CALLER can say "the default" out loud
/// rather than by omission.

/// What a kernel is being compiled for.
///
/// Two constructors and no `Result`-shaped failure: an unsupported target is
/// a spelling this type cannot produce, which is stronger than a check.
/// ROCDL (Phase 7) is the next constructor; SPIR-V/Metal are out of scope
/// (upstream deleted its SPIR-V and Vulkan runners).
pub type MlirTarget {
    /// Host code: the machine this compiler runs on, addressed by the same
    /// triple `llvm::TargetSpec` uses. `index_bits` is MLIR's
    /// `index-bitwidth` -- it is a FIELD rather than a function of the
    /// triple for the reason `llvm::TargetSpec.pointer_bits` gives: it IS
    /// the ABI fact the triple only implies, and a wrong one miscompiles
    /// silently (an `index` lowered as `i32` on an LP64 host truncates every
    /// buffer subscript).
    cpu (triple : String) (index_bits : I64),
    /// An NVIDIA GPU, through NVVM. `chip` is `sm_80`-shaped and always
    /// explicit; `features` is the `+ptx60`-shaped list `nvvm-attach-target`
    /// appends to its default, `""` for none.
    nvptx (chip : String) (features : String),
}

/// The triple every NVPTX device module carries. A constant because it is
/// not a decision (see the file header).
pub def nvptx_triple : String := "nvptx64-nvidia-cuda"

/// The chip `MlirTarget.`'s callers name when they mean "the pinned
/// default". `sm_75` is LLVM 21's own NVVM default, named here so pinning it
/// explicitly is a choice rather than a coincidence: if this constant ever
/// differs from what `nvvm-attach-target` does when given no `--chip`, the
/// pinned pipeline is the one that wins.
pub def default_chip : String := "sm_75"

/// `sm_80`, the chip the plan's goldens are written against. A separate
/// constant from `default_chip` because they answer different questions:
/// `default_chip` is "what the toolchain would have done", `golden_chip` is
/// "what Phase 4's expected PTX is for". Conflating them is how a golden
/// quietly stops testing the target it documents.
pub def golden_chip : String := "sm_80"

/// A CPU target: this machine, 64-bit `index`.
///
/// The triple is a PARAMETER rather than a probe. Probing is
/// `llvm::TargetSpec.native`'s job (it shells out to `clang -dumpmachine`),
/// it costs a fork, and this mote's tests must not fork -- Phase 1's
/// acceptance is that the goldens run with no front end and no toolchain.
/// `tool.mo` is where a caller that genuinely needs the host triple gets one.
pub def MlirTarget.cpu_native (triple : String) : MlirTarget := MlirTarget.cpu triple 64

/// An NVIDIA target for `chip`, no extra features.
pub def MlirTarget.nvptx_chip (chip : String) : MlirTarget := MlirTarget.nvptx chip ""

/// The GPU a kernel is compiled for, at the pinned golden chip.
pub def MlirTarget.golden_nvptx : MlirTarget := MlirTarget.nvptx golden_chip ""

/// `nvptx64-nvidia-cuda` / the host triple. What `mlir-translate` and `llc`
/// are told, for the third `triple` shape that has nothing to do with either.
pub def MlirTarget.triple_of (target : MlirTarget) : String := match target {
    MlirTarget.cpu triple _ => triple,
    MlirTarget.nvptx _ _ => nvptx_triple,
}

/// Whether this target is a GPU, i.e. whether a kernel compiled for it is a
/// device kernel rather than a plain C function. The CPU path's whole
/// appeal (Decision 3) is that it is the LATTER.
pub def MlirTarget.is_device (target : MlirTarget) : Bool := match target {
    MlirTarget.cpu _ _ => false,
    MlirTarget.nvptx _ _ => true,
}

/// Whether two targets name the same machine.
///
/// Field-by-field rather than by rendering, so a future field cannot be
/// forgotten here and silently make two different targets compare equal --
/// which is what a cache key derived from it would do.
pub def MlirTarget.same (a : MlirTarget) (b : MlirTarget) : Bool := match a {
    MlirTarget.cpu a_triple a_bits => match b {
        MlirTarget.cpu b_triple b_bits =>
            String.beq a_triple b_triple && I64.beq a_bits b_bits,
        MlirTarget.nvptx _ _ => false,
    },
    MlirTarget.nvptx a_chip a_features => match b {
        MlirTarget.cpu _ _ => false,
        MlirTarget.nvptx b_chip b_features =>
            String.beq a_chip b_chip && String.beq a_features b_features,
    },
}

/// A one-line spelling for a diagnostic or a cache key --
/// `cpu x86_64-unknown-linux-gnu`, `nvptx sm_80+ptx60`.
///
/// The same function is the cache key's target component
/// (`plans/bootstrapping/mlir-codegen.md` Phase 2's `cache.mo` hashes
/// "text ++ pipeline ++ triple"), so it has to distinguish every target the
/// type can hold: `chip` alone would collide two feature sets, and a
/// `+`-joined feature list is what `nvvm-attach-target --features` takes.
pub def MlirTarget.describe (target : MlirTarget) : String := match target {
    MlirTarget.cpu triple bits =>
        "cpu " ++ triple ++ " (index " ++ I64.to_string bits ++ ")",
    MlirTarget.nvptx chip features =>
        if String.is_empty features then "nvptx " ++ chip
        else "nvptx " ++ chip ++ features,
}

#[test]
def test_cpu_triple_and_describe : Bool :=
    let t := MlirTarget.cpu_native "x86_64-unknown-linux-gnu" in
    String.beq (MlirTarget.triple_of t) "x86_64-unknown-linux-gnu"
        && String.beq (MlirTarget.describe t) "cpu x86_64-unknown-linux-gnu (index 64)"
        && Bool.not (MlirTarget.is_device t)

/// The device triple is a constant, not whatever a caller passed -- a
/// `nvptx` target cannot be spelled with a triple `mlir-opt` rejects.
#[test]
def test_nvptx_triple_is_the_device_constant : Bool :=
    let t := MlirTarget.golden_nvptx in
    String.beq (MlirTarget.triple_of t) "nvptx64-nvidia-cuda"
        && String.beq (MlirTarget.describe t) "nvptx sm_80"
        && MlirTarget.is_device t

/// Features are part of a target's identity, in `describe` and in `same`.
/// `+ptx60` is `nvvm-attach-target`'s own default, so a caller that spells
/// it explicitly is describing the same machine -- but `describe` has to
/// keep the strings apart, because a cache keyed on `sm_80` alone would
/// serve a `+ptx70` artifact to a `+ptx60` request.
#[test]
def test_features_are_part_of_the_spelling : Bool :=
    let plain := MlirTarget.nvptx_chip "sm_80" in
    let ptx := MlirTarget.nvptx "sm_80" "+ptx70" in
    String.beq (MlirTarget.describe plain) "nvptx sm_80"
        && String.beq (MlirTarget.describe ptx) "nvptx sm_80+ptx70"
        && Bool.not (MlirTarget.same plain ptx)

/// Same machine, two spellings of one target: equal. Different machine,
/// same kind: not.
#[test]
def test_same_compares_every_field : Bool :=
    let a := MlirTarget.cpu_native "aarch64-apple-darwin" in
    let b := MlirTarget.cpu "aarch64-apple-darwin" 64 in
    let c := MlirTarget.cpu "aarch64-apple-darwin" 32 in
    let g := MlirTarget.golden_nvptx in
    MlirTarget.same a b
        && Bool.not (MlirTarget.same a c)
        && Bool.not (MlirTarget.same a g)
        && Bool.not (MlirTarget.same g a)
        && MlirTarget.same g MlirTarget.golden_nvptx

/// The golden chip is pinned and is NOT the toolchain default, which is the
/// whole point of pinning it: LLVM 21 moved the default and a golden must
/// not move with it.
#[test]
def test_the_golden_chip_is_pinned_and_explicit : Bool :=
    String.beq golden_chip "sm_80"
        && String.beq default_chip "sm_75"
        && Bool.not (String.beq golden_chip default_chip)
