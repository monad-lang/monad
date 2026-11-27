/// The third arm of `compile_db_def_ir`: a `#[kernel]` the driver compiled
/// through MLIR gets a host stub, and its ordinary body moves to `__ref`.
///
/// The stub is the only place the boxed-`i64` convention meets the kernel's
/// bare-pointer C ABI, so these tests pin its exact text: a `Buf` becomes its
/// payload address, a folded dim is not passed, a scalar keeps its width, and
/// a `void` kernel still returns a `Unit` box.
use lang::types {AttrArg, Attribute, Def, Identifier, NamePath, Term, Visibility, binder_named}
use llvm::ir {LLVMModule, emit_module}
use llvm::strmap {str_map_empty}
use lib::ctx {ctx_with_kernels, empty_ctx}
use lib::emit {compile_db_def_ir, empty_arities}
use lib::kernel::build {file_stem}
use lib::kernel::host {KernelAbi, KernelAbiParam}
use lib::test::support {check_contains}

/// `fn dst => fn n => hole` -- a parsed two-parameter def's term shape.
#[partial]
def saxpy_def : Def :=
    let body := Term.lam (binder_named (Identifier.id "dst")) Term.hole
        (Term.lam (binder_named (Identifier.id "n")) Term.hole Term.hole) in
    Def.mk (NamePath.mk [Identifier.id "saxpy"]) Term.hole body
        List.empty [Attribute.mk (Identifier.id "kernel") List.empty] Visibility.package_private List.empty

/// `saxpy (dst : Buf F32) (n : I64) : Unit`, with `n` folded into the memref.
def saxpy_abi : KernelAbi := KernelAbi.mk [KernelAbiParam.mk "dst" "ptr"] Option.none

/// `scale (x : F32) (n : I64) : F32`, nothing folded.
def scale_abi : KernelAbi :=
    KernelAbi.mk [KernelAbiParam.mk "dst" "f32", KernelAbiParam.mk "n" "i64"]
        (Option.some (KernelAbiParam.mk "_ret" "f32"))

#[partial]
def stub_text (abi : KernelAbi) : String :=
    let c := ctx_with_kernels (empty_ctx empty_arities str_map_empty str_map_empty str_map_empty str_map_empty) [("saxpy", abi)] in
    match compile_db_def_ir c saxpy_def {
        { funcs, .. } => emit_module (LLVMModule.mk "x86_64-unknown-linux-gnu" List.empty funcs List.empty Option.none List.empty),
    }

/// The stub keeps the Monad arity (both boxed params), so every call site
/// is unchanged.
#[test]
def test_stub_keeps_the_monad_arity : Bool :=
    check_contains (stub_text saxpy_abi) "define i64 @monad_extern_saxpy(i64 %p0, i64 %p1)"

/// A `Buf` crosses as its payload address, and the folded dim is dropped.
#[test]
def test_stub_passes_the_buf_payload_and_drops_the_dim : Bool :=
    let text := stub_text saxpy_abi in
    check_contains text "%t1 = call i64 @monad_buf_data_ptr(i64 %p0)"
        && check_contains text "%t2 = inttoptr i64 %t1 to i8*"
        && check_contains text "call void @saxpy(i8* %t2)\n"

/// A `void` kernel returns a real `Unit` box, not a raw 0.
#[test]
def test_void_stub_returns_unit : Bool :=
    check_contains (stub_text saxpy_abi) "%t3 = call i64 @alloc_constructor(i64 0, i64 0)\n  ret i64 %t3"

/// The ordinary body is still emitted, under the reference name.
#[test]
def test_body_moves_to_the_reference_symbol : Bool :=
    let text := stub_text saxpy_abi in
    check_contains text "define i64 @saxpy__ref("
        && Bool.not (check_contains text "define i64 @saxpy(")

/// Scalars keep their C width both ways: `f32` in, `f32` out.
#[test]
def test_scalar_stub_casts_both_ways : Bool :=
    let text := stub_text scale_abi in
    check_contains text "%t3 = call float @saxpy(float %t2, i64 %p1)"
        && check_contains text "%t4 = bitcast float %t3 to i32"

/// A kernel's artifacts are named after its symbol with `::` made portable.
#[test]
def test_kernel_file_stem_is_portable : Bool :=
    String.beq (file_stem "a.b::main::k") "a.b__main__k" && String.beq (file_stem "k") "k"
