/// IR-shape tests for the Monad-generated runtime natives
/// (`lang/codegen/runtime.mo`) -- the per-phase test pattern
/// plans/bootstrapping/self-hosted-runtime.md's Phase 1 specifies.
///
/// These assert the emitted text's own distinctive instructions, which
/// is exactly what caught the two real bugs the first render exposed:
/// an off-by-one in `i64_params` (three `%pN` params emitted for an
/// arity-2 native) and arithmetic nested directly inside `ret`
/// (`ret i64 sub i64 %p0, %p1` -- LLVM instructions cannot nest, so
/// every op needs its own SSA assignment first). Both produced
/// perfectly typechecking Monad code; only rendering the IR found them.
///
/// Behavior beyond shape (byte loops actually walking a `char*`, the
/// `List.cons` chain `monad_string_to_list` builds, `Option` tags) was
/// verified separately by linking the generated `.o` against the real
/// `lang/codegen/runtime.c` and calling each native from C -- see the
/// module's own doc comment for the representation facts that makes
/// possible.
use lang.codegen.ir {emit_module}
use lang.codegen.emit {check_contains}
use lang.codegen.runtime {runtime_native_functions}

#[partial]
def runtime_ir_text : String :=
    emit_module (LLVMModule.mk "x86_64-unknown-linux-gnu" [] runtime_native_functions [] Option.none)

/// The raw-`char*` byte access every String native is built on:
/// address arithmetic, `inttoptr` to a real pointer, then the typed
/// `load i8` (Strings are NOT boxed `StringObj` -- runtime.c:539-543).
#[test]
def test_runtime_byte_load_shape : Bool :=
    let t := runtime_ir_text in
    check_contains t "inttoptr i64 %addr_s to i8*"
        && check_contains t "load i8, i8* %qs"
        && check_contains t "zext i8 %s_b8 to i64"

/// Arity must match what `compile_native_def_wrapper_ir` passes:
/// exactly `parm_ 0 .. N-1`. An extra `%p2` here was a real bug.
#[test]
def test_runtime_arity_exact : Bool :=
    let t := runtime_ir_text in
    check_contains t "define i64 @monad_string_starts_with(i64 %p0, i64 %p1) {"
        && check_contains t "define i64 @monad_string_to_list(i64 %p0) {"
        && check_contains t "define i64 @monad_bench_now() {"

/// `List U8` marshaling via the fixed builtin tag convention:
/// `List.cons` is tag 6 with 2 fields, `List.empty` tag 5 with 0.
#[test]
def test_runtime_to_list_cons_chain : Bool :=
    let t := runtime_ir_text in
    check_contains t "%empty_con = call i64 @alloc_constructor(i64 5, i64 0)"
        && check_contains t "%con = call i64 @alloc_constructor(i64 6, i64 2)"
        && check_contains t "call i64 @monad_set_field(i64 %con, i64 1, i64 %acc)"

/// `Option U8`: `none` is tag 3 (no fields), `some` tag 4 (one).
#[test]
def test_runtime_string_get_option_tags : Bool :=
    let t := runtime_ir_text in
    check_contains t "%none_con = call i64 @alloc_constructor(i64 3, i64 0)"
        && check_contains t "%some_con = call i64 @alloc_constructor(i64 4, i64 1)"

/// Division-family ops and the zero-divisor guard both reference
/// natives the compiler's own closure needs (`std/map.mo`'s bucket
/// arithmetic). `u8_div` is `sdiv` (the reference's `wrapping_div` is
/// signed), `u64_mod` is `urem` (bucketing only needs self-consistency,
/// see its doc comment in runtime.mo).
#[test]
def test_runtime_unsigned_ops : Bool :=
    let t := runtime_ir_text in
    check_contains t "%r = urem i64 %p0, %p1"
        && check_contains t "%r = sdiv i64 %p0, %p1"
        && check_contains t "%zero_b = icmp eq i64 %p1, 0"

/// No instruction may nest inside another: every arithmetic result
/// lands in its own SSA name before `ret` consumes it.
#[test]
def test_runtime_no_nested_instructions : Bool :=
    let t := runtime_ir_text in
    check_contains t "  %r = sub i64 %p0, %p1"
        && check_contains t "  %r = mul i64 %p0, %p1"
        && not (check_contains t "ret i64 sub")
        && not (check_contains t "ret i64 mul")

/// `i >= 0` / `i >= len` are spelled with `sgt -1` and a swapped-target
/// `slt`, since the IR ADT has no `icmp_sge` variant.
#[test]
def test_runtime_no_sge_workarounds : Bool :=
    let t := runtime_ir_text in
    check_contains t "%cont = icmp sgt i64 %i, -1"
        && check_contains t "%in_range = icmp slt i64 %p1, %len"
