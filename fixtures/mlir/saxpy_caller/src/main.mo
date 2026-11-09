// The Monad side of the Phase 0 MLIR harness
// (plans/bootstrapping/mlir-codegen.md, Phase 0).
//
// It is not a program you run: `scripts/check-mlir-toolchain.sh` compiles
// it with `monad build`, having first turned `saxpy.mlir` into an object
// file and archived it as `libsaxpyfixture.a`. This file declares the
// three entry points the script asserts on.
//
// What it is FOR, in the plan's terms:
//
//   * it proves the BARE-POINTER MEMREF ABI end to end. `saxpy` and
//     `total` were lowered from `memref<16xf32>` to a bare `float*` by
//     `convert-func-to-llvm{use-bare-ptr-memref-call-conv=1}`, and this
//     file passes that pointer as a plain `Ptr` through `#[extern "c"]`.
//     The pointer comes from `ByteBuf.ptr`, which is the already-landed
//     flat-buffer path -- `Buf E` (Phase 0.5) does not exist yet.
//   * it proves the `#[extern "c"]` wrapper needs NO new codegen for a
//     kernel: `Ptr` in, `F64`/`I32` out, all casts already emitted by
//     `emit_extern_param_cast`. Phase 2's `host.mo` should therefore
//     reduce to synthesising an `ExternInfo`.
//   * it proves the narrow-integer RETURN path (`answer : I32`), which the
//     corpus barely reaches.
//
// Deliberately ONE file with no mote manifest: nothing here needs
// dependencies or `[link]` metadata, the script supplies the archive's
// path on the command line, and a manifest would just be another thing to
// keep in step. `#[test]` defs are absent for the same reason -- there is
// no `monad test` here to find them, and the script's assertions are the
// test.

// `ByteBuf` is the already-landed flat-buffer primitive (the u8 case of
// the `BufObj` heap kind `Buf E` generalises); its `ptr` is the payload
// address the kernel takes as a bare pointer.
use std::bytebuf {ByteBuf}

// `dst[i] = a * (f32)i + 1.0` over 16 elements. The scalar is an `I32`
// BIT PATTERN, not an `F32`, matching what the wrapper hands C for an
// `F32` argument (`trunc i64`, then `bitcast i32 -> float`); the MLIR side
// does the bitcast. Passing `3.0`'s bits therefore multiplies by 3.0.
#[extern "c" {link_name := "saxpy"}]
def saxpy (dst : Ptr) (a_bits : I32) : RawIO Unit

// Sum the 16 values into an `f64`. Memref in, scalar out.
//
// Pure, so it is declared with its raw return type rather than `RawIO`
// (the runtime reads memory the kernel wrote, but it allocates nothing and
// has no observable effect of its own -- the same call the plan makes for
// `strlen`).
#[extern "c" {link_name := "total"}]
def total (v : Ptr) : F64

// No memref at all: the pure-scalar path, which must keep working even if
// the bare-pointer conversion is misconfigured.
#[extern "c" {link_name := "checksum"}]
def checksum (n : I64) : F64

// A nullary narrow-integer return, for the `sext` arm of the return chain.
// A nullary def is spelled WITHOUT parens in Monad.
#[extern "c" {link_name := "answer"}]
def answer : I32

/// `3.0f32`'s IEEE-754 bit pattern, as the `I32` the kernel bitcasts back
/// to a float. Spelled as a decimal because the corpus has no `f32`
/// literal suffix, and taking the bits from `F64` would need a `to_bits`
/// native that does not exist (`implementations/float-bit-conversions.md`
/// is its own unimplemented plan). `monad check` is what keeps this
/// honest: if the boundary type ever stopped being `I32`, the call below
/// would fail to typecheck rather than silently truncate.
def three_point_zero_bits : I32 := 1077936128

/// The expected total: `sum (map (a*i + 1) [0..15])` with `a = 3.0`,
/// i.e. `3 * 120 + 16`.
def expected_total : F64 := 376.0

/// The expected `checksum 8`: `0 + 1 + ... + 7`.
def expected_checksum : F64 := 28.0

/// `answer`'s expected value, and the string the script greps for. The
/// comparison is textual because the corpus has no negative `i32` literal
/// to compare against and `I32.beq` would not help anyway; `to_string` is
/// the observable, which is exactly the reasoning
/// `motes/ffi_example/src/libc.mo` records for `atoi`/`abs`.
def expected_answer : String := "42"

def main : IO Unit := do {
    // A 64-byte buffer: `memref<16xf32>` is 16 * 4 bytes, and `ByteBuf`'s
    // payload is 64-byte aligned by construction -- which is exactly the
    // `allocated == aligned` precondition Decision 3 needs. 64 is both the
    // payload size and the alignment, which is not a coincidence: `BufObj`
    // rounds the payload up to a 64-byte boundary, so the two agree.
    let buf <- ByteBuf.alloc 64;
    let dst := ByteBuf.ptr buf;

    let _w <- saxpy dst three_point_zero_bits;

    let got_total := total dst;
    let got_checksum := checksum 8;
    let got_answer := answer;

    // Three independent numbers, printed one per line so a failure names
    // which stage broke rather than just "wrong output". `F64.to_string`
    // renders these small exact values without a decimal point (the
    // shortest round-trip form), so the script greps for `376`, `28` and
    // `42`.
    IO.println (F64.to_string got_total);
    IO.println (F64.to_string got_checksum);
    IO.println (I32.to_string got_answer);

    // Self-checking too, so `monad run` on this file is meaningful even
    // without the script: `expected_*` would otherwise be dead.
    let ok := F64.beq got_total expected_total;
    let ok2 := F64.beq got_checksum expected_checksum;
    let ok3 := String.beq (I32.to_string got_answer) expected_answer;
    if Bool.and ok (Bool.and ok2 ok3)
    then IO.println "ok"
    else IO.println "MISMATCH"
}
