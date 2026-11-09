// The Phase 0 hand-written MLIR module. NO EMITTER produces this file; it
// is written by hand on purpose, because Phase 0's whole point is to
// retire three risks before one line of emitter exists
// (plans/bootstrapping/mlir-codegen.md, Phase 0):
//
//   1. TOOLCHAIN CONTENTS. `mlir-opt`, `mlir-translate`, `mlir-runner`,
//      `llc` and `clang` all come from ONE pinned attribute set
//      (`nix/packages.nix` -> `llvmPackages_21`) and all agree on 21.1.8.
//   2. THE BARE-POINTER MEMREF ABI. `convert-func-to-llvm` with
//      `use-bare-ptr-memref-call-conv=1` turns each `memref<NxT>` argument
//      into a single pointer to the aligned data, so @saxpy below becomes
//      a plain C function `void saxpy(float*, i32)` -- which `LLVMType`
//      can already declare and call. That is what reduces `host.mo`
//      (Phase 2) to synthesising an `ExternInfo`: zero new host codegen.
//   3. DIAGNOSTICS. A pass-pipeline failure's entire signal is on stderr,
//      and `exec_cmd` returns only an exit status. `Proc.capture`
//      (std/src/process.mo) is the answer;
//      `scripts/check-mlir-toolchain.sh` has a deliberately-malformed
//      pipeline step proving MLIR's own text survives it.
//
// The module is the WHOLE pipeline in one file, because the
// ordering-sensitive passes are the part most likely to be wrong and CI
// must exercise exactly the sequence Phase 2 will use.
//
// Dialects: `func`, `arith`, `scf`, `memref`, `builtin` only -- no
// `affine`, `vector`, `tensor`, bufferization or `gpu`. That is Phase 2's
// dialect set ("Dialects: seven modules, not twelve").
//
// WHAT THE HOST HAS TO PROVIDE: one writable 64-byte buffer
// (`memref<16xf32>`), and nothing else. The kernel derives its own inputs
// from the loop index rather than reading a second buffer, so the Monad
// side never has to marshal `f32` values through a byte list -- `Buf E`
// does not exist yet (Phase 0.5) and `ByteBuf` is byte-oriented.
// `fixtures/mlir/saxpy_caller.mo` is the caller.

// Every memref dim is STATIC. Kernels take whole buffers with shapes
// constant-folded at extraction (Decision 5), never dynamic `?` dims: the
// bare-pointer convention needs `allocated == aligned`, which a dynamic
// stride would not guarantee.

// `llvm.noalias` on the memref argument is the aliasing fact Decision 5
// says linearity would eventually supply. It is declared here so the
// lowering is checked for preserving it, and so the argument-attribute
// path is exercised -- it is text, and it has to survive
// `convert-func-to-llvm`.
//
// `llvm.emit_c_interface` is deliberately ABSENT: it would generate a
// `_mlir_ciface_saxpy` taking a pointer to a memref *descriptor struct*,
// which the Monad host cannot build (no `alloca`, no array type in
// `LLVMType`). The bare-pointer convention is the entire point.
func.func @saxpy(%dst: memref<16xf32> {llvm.noalias}, %a_bits: i32) {
    // The `f32` scalar arrives as its bit pattern (`i32`), because that is
    // what the Monad wrapper hands C for an `F32` -- see
    // `emit_extern_param_cast`: `trunc i64` then `bitcast i32 -> float`.
    // Taking an `i32` and bitcasting here keeps the boundary integral and
    // matches the proven `sin : F64 -> F64` shape.
    %a = arith.bitcast %a_bits : i32 to f32

    %c0 = arith.constant 0 : index
    %c16 = arith.constant 16 : index
    %c1 = arith.constant 1 : index
    %one = arith.constant 1.0 : f32

    // The loop vocabulary: `scf.for` over an `index` induction variable.
    // This is what `scalar.mo` will emit for a bounded `for i in 0..n`,
    // and it is why kernels permit no recursion -- a termination proof is
    // not a trip count (Decision 5).
    //
    // dst[i] = a * (f32)i + 1.0, so with a = 3.0 the values are
    // 1, 4, 7, ... 46 and their total is 376.
    scf.for %i = %c0 to %c16 step %c1 {
        %i64 = arith.index_cast %i : index to i64
        %x = arith.sitofp %i64 : i64 to f32
        %t = arith.mulf %a, %x : f32
        %r = arith.addf %t, %one : f32
        memref.store %r, %dst[%i] : memref<16xf32>
    }

    return
}

// Sum a `memref<16xf32>` into an `f64` and return it. This is the
// memref-in / scalar-out shape, and it is what gives the assertion in the
// script ONE readable number instead of 16 values compared by hand.
//
// `f64` accumulation, not `f32`: every value here is a small exact
// integer, so the sum (376) is exact in both, and returning `f64` avoids
// needing an `f32`-returning extern declaration on the Monad side.
func.func @total(%v: memref<16xf32> {llvm.noalias}) -> f64 {
    %c0 = arith.constant 0 : index
    %c16 = arith.constant 16 : index
    %c1 = arith.constant 1 : index
    %zero = arith.constant 0.0 : f64

    %acc = scf.for %i = %c0 to %c16 step %c1 iter_args(%s = %zero) -> (f64) {
        %vi = memref.load %v[%i] : memref<16xf32>
        %vid = arith.extf %vi : f32 to f64
        %next = arith.addf %s, %vid : f64
        scf.yield %next : f64
    }
    return %acc : f64
}

// A pure-scalar entry: no memref at all. If the
// `use-bare-ptr-memref-call-conv` option were misspelled or dropped,
// @saxpy/@total would fail to lower while this one still linked -- the
// pair together localises the failure instead of reporting "the module
// broke".
//
// Returns 0 + 1 + ... + (n-1), so `checksum 8` is 28.0.
func.func @checksum(%n: i64) -> f64 {
    %c0 = arith.constant 0 : index
    %n_idx = arith.index_cast %n : i64 to index
    %c1 = arith.constant 1 : index
    %zero = arith.constant 0.0 : f64

    %acc = scf.for %i = %c0 to %n_idx step %c1 iter_args(%s = %zero) -> (f64) {
        %i64 = arith.index_cast %i : index to i64
        %i_d = arith.sitofp %i64 : i64 to f64
        %next = arith.addf %s, %i_d : f64
        scf.yield %next : f64
    }
    return %acc : f64
}

// A narrow-integer RETURN, so `emit_extern_param_cast`'s return-widening
// chain is exercised on its `sext` arm. The plan's audit notes that `puts`
// yields the corpus's only negative `i32` and that no negative `i32`
// literal exists to compare against, so the *value* is asserted by string
// comparison on the caller side rather than by sign.
func.func @answer() -> i32 {
    %c = arith.constant 42 : i32
    return %c : i32
}
