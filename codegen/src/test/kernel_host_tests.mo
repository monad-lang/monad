/// `codegen::kernel::host` -- the module assembly and the host ABI.
///
/// ## What this file has to prove
///
/// `host.mo` is small by design (Decision 3: a kernel lowers to a plain C
/// function, so `emit.mo`'s existing extern wrapper does the marshalling), and
/// what is left is exactly two claims:
///
/// 1. **The assembled module is the kernel's own `func.func`** -- the right
///    name, the right arity, and a body that came from `scalar.mo` rather than
///    being invented here. A wrong arity is not a wrong number; it is a
///    linker error, and one that points at the emitted `.o` rather than at the
///    source.
/// 2. **The C ABI is the bare-pointer one.** `Buf` -> `ptr`, a scalar keeps
///    its width, `dim_` parameters are ABSENT (they were folded into the
///    memref). This is the ABI `convert-func-to-llvm{use-bare-ptr-memref-call-conv=1}`
///    produces, and a mismatch with it is a crash rather than a diagnostic.
///
/// ## The two names, and why the test asserts BOTH
///
/// `<def>` is what the compiled object defines; `<def>__ref` is the ordinary
/// Monad body the interpreter runs. Asserting only the first would leave the
/// differential oracle unverified -- and the plan's whole correctness story is
/// that the two can be compared.
use lang::types {DebugName, Identifier, Literal, NumSuffix, Term, sentinel}
use lib::kernel::detect {KernelDiagnostic}
use lib::kernel::mono {KernelExtract}
use lib::kernel::scalar {KernelBody, emit_kernel_body}
use lib::kernel::shape {KernelShape, ParamShape, show_signature}
use lib::kernel::host {
    KernelAbi, KernelAbiParam, KernelModule, describe, kernel_abi, kernel_function,
    kernel_module, kernel_symbol, reference_symbol, render_kernel, render_module, show_abi,
}
use mlir::ir {MlirFunction, MlirModule, MlirType}
use std::list {List.any}

// ─── fixtures ────────────────────────────────────────────────────────

/// A free global reference -- what a parameter reference looks like in a
/// hand-built body.
def ref (name : String) : Term := Term.var sentinel (DebugName.named (Identifier.id name))

/// An `I64` literal.
def int_lit (v : I64) : Term := Term.lit (Literal.num v NumSuffix.i64)

/// The MEASURED `saxpy` signature: `(dst : Buf F32) (n : I64) : Unit`, with the
/// dimension folded to 16 -- the shape `shape.mo`'s own tests transcribe, so
/// the two suites agree about what a real kernel looks like.
def saxpy_shape : KernelShape :=
    KernelShape.mk "saxpy"
        [ParamShape.buffer_ "dst" MlirType.f32 [16] false
            , ParamShape.dim_ "n"]
        List.empty List.empty

/// A `Unit`-returning kernel whose body is a bare parameter reference -- enough
/// to have a real body without needing the write path.
def unit_extract (body : Term) : KernelExtract :=
    KernelExtract.mk "saxpy" List.empty body List.empty

/// A scalar-returning kernel: `(n : I64) : I64`.
def scalar_shape : KernelShape :=
    KernelShape.mk "k" [ParamShape.scalar_ "n" MlirType.i64 false]
        (List.cons MlirType.i64 List.empty) List.empty

def scalar_extract (body : Term) : KernelExtract :=
    KernelExtract.mk "k" List.empty body List.empty

// ─── 1. the two names ────────────────────────────────────────────────

/// The compiled kernel keeps the def's own symbol, so the define side and the
/// call side agree.
#[test]
def test_kernel_symbol_is_the_def_name : Bool :=
    String.beq (kernel_symbol saxpy_shape) "saxpy"

/// The reference body gets its own symbol: the two live in one binary, and one
/// symbol for both is a duplicate-definition error at link time.
#[test]
def test_reference_symbol_is_distinct : Bool :=
    String.beq (reference_symbol saxpy_shape) "saxpy__ref"
        && Bool.not (String.beq (kernel_symbol saxpy_shape) (reference_symbol saxpy_shape))

// ─── 2. the assembled module ─────────────────────────────────────────

/// The module holds exactly ONE function: helpers are inlined by `mono.mo`, so
/// nothing else is reachable, and a second function would be one `mlir-opt`
/// compiles for no caller.
#[test]
def test_the_module_holds_one_function : Bool :=
    let body : KernelBody := emit_kernel_body saxpy_shape (unit_extract (ref "dst")) in
    let m : MlirModule := kernel_module saxpy_shape body in
    I64.beq (List.length m.functions) 1

/// The function's name is the kernel's symbol, which is what makes the emitted
/// `.o` define the symbol the host calls.
#[test]
def test_the_function_is_named_for_the_kernel : Bool :=
    let body : KernelBody := emit_kernel_body saxpy_shape (unit_extract (ref "dst")) in
    let f : MlirFunction := kernel_function saxpy_shape body in
    String.beq f.name "saxpy"

/// The ARITY is the C arity: the `dim_` parameter is absent, because it was
/// folded into the memref's static shape. Emitting it would give the function
/// one parameter more than the host passes -- a link error, not a wrong number.
#[test]
def test_the_dimension_parameter_is_absent : Bool :=
    let body : KernelBody := emit_kernel_body saxpy_shape (unit_extract (ref "dst")) in
    let f : MlirFunction := kernel_function saxpy_shape body in
    I64.beq (List.length f.params) 1

/// The body is `scalar.mo`'s, not a copy: the rendered module contains the
/// `return` that emitter appends, so a `host.mo` that assembled an EMPTY body
/// would fail this while passing every test above.
#[test]
def test_the_body_comes_from_the_emitter : Bool :=
    let body : KernelBody := emit_kernel_body saxpy_shape (unit_extract (ref "dst")) in
    String.contains (render_module (kernel_module saxpy_shape body)) "return"

// ─── 3. the C ABI ────────────────────────────────────────────────────

/// A `Buf` crosses the C boundary as a bare pointer, which is Decision 3: one
/// pointer to the aligned data, not MLIR's five-word memref descriptor.
#[test]
def test_a_buffer_is_a_bare_pointer : Bool :=
    match kernel_abi saxpy_shape {
        KernelAbi.mk params _ret => match params {
            List.cons p _ => String.beq p.c_type "ptr",
            _ => false,
        },
    }

/// A `Unit` kernel returns `void` -- `Option.none`, not a made-up type.
#[test]
def test_a_unit_kernel_returns_void : Bool :=
    match kernel_abi saxpy_shape {
        KernelAbi.mk _params ret => match ret {
            Option.none => true,
            Option.some _ => false,
        },
    }

/// A scalar-returning kernel's C return type is the scalar's width, and its
/// parameter keeps that width too. `i64` here and `i64` there is the ABI's
/// claim, not a widening.
#[test]
def test_scalar_widths_are_preserved : Bool :=
    match kernel_abi scalar_shape {
        KernelAbi.mk params ret =>
            match params {
                List.cons p _ => String.beq p.c_type "i64" && match ret {
                    Option.some r => String.beq r.c_type "i64",
                    Option.none => false,
                },
                _ => false,
            },
    }

/// An `f32` parameter stays `f32` rather than becoming `f64`: the kernel was
/// compiled against the 4-byte width, and passing a double would read every
/// second element as garbage.
#[test]
def test_f32_stays_f32 : Bool :=
    let shape : KernelShape :=
        KernelShape.mk "k" [ParamShape.scalar_ "a" MlirType.f32 false]
            (List.cons MlirType.f32 List.empty) List.empty
    in
    match kernel_abi shape {
        KernelAbi.mk params ret =>
            match params {
                List.cons p _ => String.beq p.c_type "f32" && match ret {
                    Option.some r => String.beq r.c_type "f32",
                    Option.none => false,
                },
                _ => false,
            },
    }

/// The rendered C signature carries both halves -- the return type and one
/// entry per parameter -- and it is EXACT, with no trailing separator.
///
/// An exact assertion rather than a `String.contains`, because the bug this
/// pins is a stray space: the first version appended one to every entry and
/// rendered `i64(i64 )`, which a `contains` check passes happily. `describe`
/// puts this string in a `monad kernels` line, so the space is user-visible.
#[test]
def test_show_abi_renders_the_signature : Bool :=
    String.beq (show_abi (kernel_abi scalar_shape)) "i64(i64)"

/// Two parameters are COMMA-separated, which is the case a one-parameter
/// fixture cannot see: a renderer that never emits a separator passes the test
/// above and fails this one.
#[test]
def test_show_abi_separates_two_parameters : Bool :=
    let shape : KernelShape :=
        KernelShape.mk "k"
            [ParamShape.scalar_ "a" MlirType.i64 false,
                ParamShape.scalar_ "b" MlirType.f32 false]
            (List.cons MlirType.i64 List.empty) List.empty
    in
    String.beq (show_abi (kernel_abi shape)) "i64(i64, f32)"

// ─── 4. render_kernel: the readiness gate, once more ─────────────────

/// A kernel with a diagnostic renders NO text. Handing `mlir-opt` an empty
/// module would be a second, worse diagnostic than the one already reported.
#[test]
def test_a_dirty_kernel_renders_nothing : Bool :=
    let extract : KernelExtract :=
        KernelExtract.mk "saxpy" List.empty (ref "dst")
            (List.cons (KernelDiagnostic.of "saxpy" "inline" "unresolved helper") List.empty)
    in
    let m : KernelModule := render_kernel saxpy_shape extract in
    Bool.not (KernelModule.ready m) && String.is_empty m.text

/// The control: a ready kernel renders its module AND carries both names.
#[test]
def test_a_ready_kernel_renders_its_module : Bool :=
    let m : KernelModule := render_kernel saxpy_shape (unit_extract (ref "dst")) in
    KernelModule.ready m
        && String.beq m.kernel "saxpy"
        && String.beq m.reference "saxpy__ref"
        && String.contains m.text "func.func @saxpy"

// ─── 5. the summary line ─────────────────────────────────────────────

/// `describe` carries the MLIR signature AND the C ABI, because a reader
/// debugging a kernel needs both and a mismatch between them is the class of
/// bug Decision 3 exists to prevent.
#[test]
def test_describe_carries_both_views : Bool :=
    let line : String := describe saxpy_shape in
    String.contains line (show_signature saxpy_shape) && String.contains line "c:"
