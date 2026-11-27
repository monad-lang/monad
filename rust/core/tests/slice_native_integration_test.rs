//! End-to-end test for `init/src/view.mo`'s indexed `Slice` in the Rust
//! bootstrap host.
//!
//! The compiled backend is pinned by `init/src/view_tests.mo` and
//! `codegen/src/test/view_ir_tests.mo`; this is the interpreter half of the
//! same six natives. It runs real Monad source through
//! `eval_core_program`, so the `Slice.of_list`/`length`/`get`/`set`/
//! `split_at`/`free` wrappers (including `Nat.to_i64` and the index
//! arithmetic they hand the natives) execute as written.

use monad_core::eval_core_program;
use monad_core::term::ModulePath;

fn run(source: &str) -> monad_core::core_value::Value {
  let path = ModulePath::top("'slice_e2e_test");
  eval_core_program(&path, source).unwrap_or_else(|e| panic!("eval_core_program failed: {e}"))
}

fn as_i64(v: &monad_core::core_value::Value) -> i64 {
  match v {
    monad_core::core_value::Value::Lit(monad_core::core_ir::IrLit::Num(n, _)) => *n,
    other => panic!("expected an int literal, got {other:?}"),
  }
}

/// Read, write, split, and free: `of_list` builds a `Slice 3`, `set`
/// overwrites index 1, `split_at 2` gives halves of 2 and 1, and the
/// answers are summed so one exit value covers every operation.
const SLICE_ROUNDTRIP: &str = r#"
use init::view {Slice}

def read_mid (s : Slice 3 I64) : I64 :=
    match Slice.get s 1 {
        Result.ok p => match p {
            Pair.pair v s1 => let _ := Slice.free s1 in v,
        },
        Result.err s1 => let _ := Slice.free s1 in 0 - 2,
    }

def run (xs : List I64) : I64 :=
    match Slice.of_list xs 3 {
        Result.ok s => match Slice.set s 1 99 {
            Result.ok s1 => read_mid s1,
            Result.err s1 => let _ := Slice.free s1 in 0 - 3,
        },
        Result.err _e => 0 - 4,
    }

def main : I64 := run [1, 2, 3]
"#;

#[test]
fn slice_read_write_roundtrip() {
  // The set wrote 99 over index 1; `read_mid` reads index 1 back.
  assert_eq!(as_i64(&run(SLICE_ROUNDTRIP)), 99);
}

/// A length mismatch is `Result.err` carrying the actual length, and the
/// out-of-range read is `Result.err` carrying the handle (never a lost
/// slice). Both errors are turned into distinct negative answers so a
/// wrong arm cannot pass as the right one.
const SLICE_ERRORS: &str = r#"
use init::view {Slice}

def run (xs : List I64) : I64 :=
    match Slice.of_list xs 2 {
        Result.ok s => let _ := Slice.free s in 0 - 1,
        Result.err e => match Slice.of_list [7, 8] 2 {
            Result.ok s => match Slice.get s 5 {
                Result.ok p => match p {
                    Pair.pair _v s1 => let _ := Slice.free s1 in 0 - 2,
                },
                Result.err s1 => let _ := Slice.free s1 in e.actual,
            },
            Result.err _e2 => 0 - 3,
        },
    }

def main : I64 := run [1, 2, 3]
"#;

#[test]
fn slice_reports_a_length_mismatch_and_keeps_the_handle() {
  // `[1, 2, 3]` against index 2 is a mismatch with actual = 3.
  assert_eq!(as_i64(&run(SLICE_ERRORS)), 3);
}
