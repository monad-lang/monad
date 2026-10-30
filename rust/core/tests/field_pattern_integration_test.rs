//! End-to-end runtime tests for Phases 1-4 of
//! `plans/implementations/struct-field-destructuring.md` (field-pattern
//! match-case destructuring, `{ x, y } => ...` / `ConsName { x, y } =>
//! ...`, and Phases 3/4's `def`/lambda parameter destructuring, `def f
//! ({ x, y } : T) := ...` / `\({ x, y } : T) => ...`, both desugaring to
//! a gensym'd param + a wrapping bare-form match, reusing Phase 1/2's own
//! machinery) — unlike `core_check_module.rs`'s own unit tests (which only
//! exercise type-checking via `check_module_source`), these run the FULL
//! pipeline (check -> lower -> evaluate) via `eval_core_program`, the same
//! entry point `named_call_integration_test.rs` uses.
//!
//! This distinction matters here even more than for that plan's own
//! integration tests: Finding 2 of this plan's own evaluation (see its
//! Changelog) predicted that `check`/`infer` succeeding is not enough
//! proof the FIELD ORDER a field-pattern case's binders actually get is
//! correct at runtime — `lower_core.rs` lowers a case's body against its
//! WRITTEN field order (the only order available pre-type-checking), and
//! `desugar_struct_literals` must retarget it onto the constructor's real
//! DECLARED order (`core_term::permute_binders`) before evaluation, or a
//! type-checked-fine program could silently bind the WRONG values to the
//! WRONG names. Every test below writes fields in an order that would
//! produce a visibly wrong (but still well-typed) answer if that
//! retargeting were missing or buggy, rather than just checking "did it
//! run without error."

use monad_core::eval_core_program;
use monad_core::term::ModulePath;

fn run(source: &str) -> monad_core::core_value::Value {
  let path = ModulePath::top("'field_pattern_e2e_test");
  eval_core_program(&path, source).unwrap_or_else(|e| panic!("eval_core_program failed: {e}"))
}

fn as_i64(v: &monad_core::core_value::Value) -> i64 {
  match v {
    monad_core::core_value::Value::Lit(monad_core::core_ir::IrLit::Num(n, _)) => *n,
    other => panic!("expected an int literal, got {other:?}"),
  }
}

/// Bare `{ ... }` destructure of a struct, fields written in the OPPOSITE
/// order from the struct's own declaration (`y` before `x`) -- if
/// `permute_binders` weren't retargeting the case onto declared order,
/// `x`/`y` inside the body would silently read each other's values.
const BARE_STRUCT_REORDERED: &str = r#"
struct Point { x : I64, y : I64 }

def sub (p : Point) : I64 :=
    match p {
        { y, x } => x - y
    }

def main : I64 := sub { x := 10, y := 3 }
"#;

#[test]
fn phase2_bare_struct_destructure_reordered_fields_binds_correctly() {
  assert_eq!(as_i64(&run(BARE_STRUCT_REORDERED)), 7);
}

/// Bare `{ ... }` with field RENAME (`x := px`) and a partial destructure
/// via `..` -- `w` must resolve to `Rect`'s `width` field specifically
/// (declared FIRST), discarding `height` (declared second) without it
/// ever reaching the body.
const BARE_RENAME_AND_REST: &str = r#"
struct Rect { width : I64, height : I64 }

def left_edge (r : Rect) : I64 :=
    match r {
        { width := w, .. } => w
    }

def main : I64 := left_edge { width := 9, height := 100 }
"#;

#[test]
fn phase2_bare_rename_and_rest_binds_only_named_field() {
  assert_eq!(as_i64(&run(BARE_RENAME_AND_REST)), 9);
}

/// Named-constructor form against a MULTI-constructor `type` (the
/// Rust-enum-struct-variant case) -- `rectangle`'s two fields written in
/// the OPPOSITE order from its declaration, same reordering-correctness
/// proof as the struct case above, but through the named-form resolution
/// path instead of the bare-form one.
const NAMED_MULTI_CONSTRUCTOR_REORDERED: &str = r#"
type Shape {
    circle (radius : I64),
    rectangle { width : I64, height : I64 }
}

def area (s : Shape) : I64 :=
    match s {
        circle { radius } => radius * radius,
        rectangle { height, width } => width * height
    }

def main : I64 := area (Shape.rectangle 3 4)
"#;

#[test]
fn phase2_named_multi_constructor_reordered_fields_binds_correctly() {
  assert_eq!(as_i64(&run(NAMED_MULTI_CONSTRUCTOR_REORDERED)), 12);
}

/// Function-parameter destructuring is out of this plan's already-landed
/// scope (Phase 3/4, not yet implemented) -- this test instead exercises
/// a field-pattern case NESTED inside another field-pattern case's own
/// body, proving the retargeting composes (each case's own `permute_binders`
/// call is scoped correctly relative to the OTHER case's binders already
/// in scope, per `permute_binders`' own `cutoff` threading).
const NESTED_FIELD_PATTERN_CASES: &str = r#"
struct Point { x : I64, y : I64 }
struct Line { from : Point, to : Point }

def dx (l : Line) : I64 :=
    match l {
        { to, from } =>
            match to {
                { y := ty, x := tx } =>
                    match from {
                        { x := fx, y := fy } => (tx - fx) + (ty - fy)
                    }
            }
    }

def main : I64 := dx { from := { x := 1, y := 2 }, to := { x := 10, y := 20 } }
"#;

#[test]
fn phase2_nested_field_pattern_cases_compose_correctly() {
  // (10 - 1) + (20 - 2) = 9 + 18 = 27
  assert_eq!(as_i64(&run(NESTED_FIELD_PATTERN_CASES)), 27);
}

// -------------------------------------------------------------------
// Phase 3: `def` parameter destructuring.
// -------------------------------------------------------------------

/// A destructured param's gensym'd binder desugars to a wrapping `match`
/// -- same reordering-correctness proof as the match-case tests above,
/// applied through the PARAMETER-position path instead.
const DESTRUCTURED_PARAM_REORDERED: &str = r#"
struct Point { x : I64, y : I64 }

def sub ({ y, x } : Point) : I64 := x - y

def main : I64 := sub { x := 10, y := 3 }
"#;

#[test]
fn phase3_destructured_param_reordered_fields_binds_correctly() {
  assert_eq!(as_i64(&run(DESTRUCTURED_PARAM_REORDERED)), 7);
}

/// Two destructured params in one signature -- proves each gets its own
/// independent wrapping match, correctly scoped (per
/// `permute_binders`'s own `cutoff` threading composing across separate
/// match nodes, not just nested ones as the Phase 2 test above covers).
const TWO_DESTRUCTURED_PARAMS: &str = r#"
struct Point { x : I64, y : I64 }

def dist ({ x := x1, y := y1 } : Point) ({ x := x2, y := y2 } : Point) : I64 :=
    (x2 - x1) + (y2 - y1)

def main : I64 := dist { x := 1, y := 2 } { x := 10, y := 20 }
"#;

#[test]
fn phase3_two_destructured_params_bind_independently() {
  // (10 - 1) + (20 - 2) = 27
  assert_eq!(as_i64(&run(TWO_DESTRUCTURED_PARAMS)), 27);
}

/// A destructured param mixed with an ordinary plain one, and a partial
/// (`..`) destructure -- both need to still see each other correctly
/// (the plain param referenced from inside the destructured param's own
/// wrapping match).
const MIXED_PARAMS_WITH_REST: &str = r#"
struct Rect { width : I64, height : I64 }

def scaled_width ({ width, .. } : Rect) (factor : I64) : I64 := width * factor

def main : I64 := scaled_width { width := 4, height := 100 } 3
"#;

#[test]
fn phase3_mixed_destructured_and_plain_param_with_rest() {
  assert_eq!(as_i64(&run(MIXED_PARAMS_WITH_REST)), 12);
}

// -------------------------------------------------------------------
// Phase 4: lambda-literal parameter destructuring.
// -------------------------------------------------------------------

/// Same reordering-correctness proof as Phase 3's own `def`-param test,
/// through a `\({ ... } : T) => ...` lambda literal instead -- applied
/// via a higher-order `List.map`-style call so it's a genuine lambda
/// value, not just sugar for a `def`.
const LAMBDA_DESTRUCTURED_PARAM: &str = r#"
struct Point { x : I64, y : I64 }

def sub (f : Point -> I64) (p : Point) : I64 := f p

def main : I64 := sub (\({ y, x } : Point) => x - y) { x := 10, y := 3 }
"#;

#[test]
fn phase4_lambda_destructured_param_reordered_fields_binds_correctly() {
  assert_eq!(as_i64(&run(LAMBDA_DESTRUCTURED_PARAM)), 7);
}
