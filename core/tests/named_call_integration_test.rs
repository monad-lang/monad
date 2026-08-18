//! End-to-end runtime tests for Phase 1 of
//! `plans/implementations/named-field-construction.md` (constructor-target
//! named calls, `NAME { field := value, ... }`) — unlike
//! `core_check_module.rs`'s own unit tests (which only exercise
//! type-checking via `check_module_source`), these run the FULL pipeline
//! (check -> lower -> evaluate) via `eval_core_program`, the same entry
//! point `core_eval_native_integration_test.rs` uses.
//!
//! This distinction matters: a real bug was found here that ONLY
//! manifested at the lowering/evaluation stage, not type-checking --
//! `check`/`infer`'s own success from a named-call desugaring is purely
//! local (per `desugar_struct_literals`'s own doc comment, `check` never
//! mutates the term it validates), so `desugar_struct_literals` — the
//! SEPARATE pass that actually rewrites the checked tree for lowering —
//! needed its OWN, independent named-call recognition; without it, a
//! type-checked-fine program could still fail at runtime with
//! `UnknownConstructor`/`expected N constructor fields, got 0` (the
//! ordinary struct-literal desugar path treating a named call's spread
//! block as if it were a malformed literal of the callee's OWN Pi
//! argument type). These tests pin real evaluated VALUES, not just
//! "did it compile," specifically to catch a regression of that class.

use monad_core::eval_core_program;
use monad_core::term::ModulePath;

fn run(source: &str) -> monad_core::core_value::Value {
  let path = ModulePath::top("'named_call_e2e_test");
  eval_core_program(&path, source).unwrap_or_else(|e| panic!("eval_core_program failed: {e}"))
}

fn as_i64(v: &monad_core::core_value::Value) -> i64 {
  match v {
    monad_core::core_value::Value::Lit(monad_core::core_ir::IrLit::Num(n, _)) => *n,
    other => panic!("expected an int literal, got {other:?}"),
  }
}

/// Multi-field constructor target, fields given in the OPPOSITE order
/// from `rectangle`'s own declaration (`width` then `height`) -- the
/// reordering is the whole point of this feature, and only a real
/// evaluated result (not just a type-check pass) proves the VALUES
/// landed in the right slots, not just that *some* well-typed term was
/// built.
const REORDERED_FIELDS: &str = r#"
type Shape {
    circle (radius : I64),
    rectangle (width : I64) (height : I64)
}

def area (s : Shape) : I64 :=
    match s {
        circle r => r * r,
        rectangle w h => w * h
    }

def r : Shape := Shape.rectangle { height := 3, width := 4 }

def main : I64 := area r
"#;

#[test]
fn phase1_named_call_reorders_constructor_fields_correctly() {
  assert_eq!(as_i64(&run(REORDERED_FIELDS)), 12);
}

/// Regression pin for the exact runtime bug this phase's own commit
/// history found: a single-param constructor (`Outer.mk`, sole param
/// `inner : Inner`) called with `{ inner := { n := 42 } }` -- the OUTER
/// struct literal's one field name ("inner") does NOT match `Inner`'s own
/// declared field ("n"), so the pre-existing, lax `check_struct_fields`
/// (present fields checked, missing/extra fields never validated) would
/// otherwise let the ORDINARY single-struct-argument interpretation
/// vacuously "succeed" against `Inner` with every field left `None` --
/// silently stealing this call away from named-call resolution and
/// producing a zero-field constructor at runtime instead of the real
/// nested value.
const NESTED_STRUCT_LITERAL_FIELD_VALUE: &str = r#"
struct Inner { n : I64 }
struct Outer { inner : Inner }

def o : Outer := Outer.mk { inner := { n := 42 } }

def inner_n (o : Outer) : I64 :=
    match o {
        mk i => match i { mk n => n }
    }

def main : I64 := inner_n o
"#;

#[test]
fn phase1_named_call_desugars_nested_unannotated_struct_literal_field() {
  assert_eq!(
    as_i64(&run(NESTED_STRUCT_LITERAL_FIELD_VALUE)),
    42,
    "the nested {{ n := 42 }} must reach evaluation as a real Inner.mk value, \
     not be swallowed by the ordinary struct-literal desugar path"
  );
}

/// A missing field with a real struct default (`Inductive.defaults`,
/// only ever populated for a single-constructor `struct`) must be filled
/// in with the DEFAULT's actual value at runtime, not left as an
/// incomplete/`None` constructor slot.
const MISSING_FIELD_STRUCT_DEFAULT: &str = r#"
struct Point { x : I64, y : I64 := 100 }

def p : Point := Point.mk { x := 1 }

def point_y (p : Point) : I64 :=
    match p {
        mk x y => y
    }

def main : I64 := point_y p
"#;

#[test]
fn phase1_named_call_fills_missing_field_from_struct_default() {
  assert_eq!(as_i64(&run(MISSING_FIELD_STRUCT_DEFAULT)), 100);
}

/// Zero-behavior-change regression pin (Rules step 1): an ordinary
/// function taking exactly one struct-typed argument, called with a
/// plain (non-annotated) struct literal whose fields DO genuinely belong
/// to that struct, must still evaluate via the pre-existing single-
/// argument interpretation -- confirms the new
/// `struct_literal_arg_matches_expected` guard doesn't misfire on
/// programs that already worked before this plan.
const ORDINARY_SINGLE_STRUCT_ARGUMENT_UNCHANGED: &str = r#"
struct Point { x : I64, y : I64 }

def sum_point (p : Point) : I64 :=
    match p {
        mk x y => x + y
    }

def main : I64 := sum_point { x := 3, y := 4 }
"#;

#[test]
fn phase1_does_not_change_existing_single_struct_argument_calls() {
  assert_eq!(as_i64(&run(ORDINARY_SINGLE_STRUCT_ARGUMENT_UNCHANGED)), 7);
}
