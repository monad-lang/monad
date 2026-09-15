// ffi_example / ffi_link_test — the mote's own C bindings called from plain
// `#[test]` defs, through the ordinary `monad test` link step.
//
// This is the other end of the feature from `ffi_codegen_e2e_test.mo` in
// this directory: that file drives the LLVM pipeline itself, with its
// externs declared inside a raw-string fixture, while nothing here links
// anything by hand. The only reason these tests can run at all is that
// `monad test` threads the mote's own `[link] libs` (this mote's
// `mote.toml` declares `[link] libs = ["m"]`) out of the loaded-module
// closure and into `link_ir` -- the same list the `run`/`compile` path has
// always passed.
//
// `sin` is the load-bearing one. The emitted IR goes through `llc`, so no
// frontend gets to fold the call away the way a C compiler folds
// `sin(constant)`; without `-lm` the driver's link fails with
// `undefined reference to 'sin'` and every test in this file is reported
// as a file-level FAIL.

use lib::libc {atoi, abs, sin, strlen}

/// `strlen` — a libc symbol reached through a `link_name` override. Both
/// directions cross the boundary as the uniform boxed `i64`, so the value
/// has to come back as the length itself.
#[test]
def test_extern_strlen_value : Bool :=
    I64.beq (strlen "hello") 5

/// `sin` — the symbol that lives in a library this mote has to declare.
/// The literal is the `F64` nearest pi/2, where libm returns exactly 1.0,
/// and getting it proves the boxed-double boundary (`bitcast i64` in,
/// `bitcast double` out) carried a real number across.
#[test]
def test_extern_sin_needs_libm : Bool :=
    F64.beq (sin 1.5707963267948966) 1.0

/// Signed `I32` on the way back: a NEGATIVE value from C must arrive as
/// the number it is, not as the unsigned reading of the same bits.
/// Asserted through `I32.to_string` because `I32.beq`'s `i32_eq` native is
/// not wired on the self-hosted side and this corpus cannot spell an `I32`
/// literal. Which ABI cast produces it (`sext`, not `zext`) is asserted
/// against the emitted IR in `lang/src/codegen/test/extern_codegen_tests.mo`
/// -- Monad's own `I32` operations all re-narrow to 32 bits, so no run-time
/// value here could tell the two apart.
#[test]
def test_extern_i32_return_is_signed : Bool :=
    String.beq (I32.to_string (atoi "-3")) "-3"

/// Signed `I32` on the way in: `abs` receives that same -3 narrowed back to
/// `i32` and returns +3, so the narrow-param path runs for real rather than
/// only appearing in emitted IR.
#[test]
def test_extern_i32_param_truncates : Bool :=
    String.beq (I32.to_string (abs (atoi "-3"))) "3"
