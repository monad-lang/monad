//! End-to-end runtime tests for dot field access (`a.fi`, `a.fi.fi2`, ...)
//! against single-constructor types -- sugar for `match a { {fi} => fi }`
//! (chained: one nested `match` per segment). See
//! `lower_core.rs::lower_field_access_chain` for the desugaring and
//! `field_pattern_integration_test.rs` (Phases 1-4 of `plans/
//! implementations/struct-field-destructuring.md`) for the bare `{ fi }`
//! match-pattern machinery this reuses unchanged.
//!
//! As with that file, tests write struct fields in an order that would
//! produce a visibly wrong (but still well-typed) answer if
//! `desugar_struct_literals`/`permute_binders` weren't retargeting the
//! synthesized pattern's binder onto the constructor's real declared
//! field order.

use monad_core::eval_core_program;
use monad_core::term::ModulePath;

fn run(source: &str) -> monad_core::core_value::Value {
  let path = ModulePath::top("'field_access_e2e_test");
  eval_core_program(&path, source).unwrap_or_else(|e| panic!("eval_core_program failed: {e}"))
}

fn run_err(source: &str) -> String {
  let path = ModulePath::top("'field_access_e2e_test");
  match eval_core_program(&path, source) {
    Ok(v) => panic!("expected an error, got {v:?}"),
    Err(e) => e,
  }
}

fn as_i64(v: &monad_core::core_value::Value) -> i64 {
  match v {
    monad_core::core_value::Value::Lit(monad_core::core_ir::IrLit::Num(n, _)) => *n,
    other => panic!("expected an int literal, got {other:?}"),
  }
}

/// `p.y`/`p.x` on a struct whose fields are declared in the OPPOSITE order
/// from how the caller happens to think about them -- if the synthesized
/// `{ fi }` pattern weren't retargeted onto Point's DECLARED order, `x`/`y`
/// would silently read each other's values.
const DOT_ACCESS_ON_PARAM: &str = r#"
struct Point { x : I64, y : I64 }

def sub (p : Point) : I64 := p.x - p.y

def main : I64 := sub { x := 10, y := 3 }
"#;

#[test]
fn dot_access_on_param_reads_the_declared_field() {
  assert_eq!(as_i64(&run(DOT_ACCESS_ON_PARAM)), 7);
}

/// Same reordering-correctness proof through a chain of TWO dots
/// (`l.to.x`) -- `to`'s own field access must be resolved against `Point`
/// (not `Line`), and `Point`'s fields are declared in the order that would
/// give a visibly wrong answer if either level's retargeting were missing.
const CHAINED_DOT_ACCESS: &str = r#"
struct Point { x : I64, y : I64 }
struct Line { from : Point, to : Point }

def dx (l : Line) : I64 := l.to.x - l.from.x

def main : I64 := dx { from := { x := 1, y := 2 }, to := { x := 10, y := 20 } }
"#;

#[test]
fn chained_dot_access_reads_nested_field() {
  assert_eq!(as_i64(&run(CHAINED_DOT_ACCESS)), 9);
}

/// Dot access on a plain single-constructor `type` (not `struct` sugar) --
/// proves this isn't gated on `struct`-declared types specifically, only
/// on the underlying inductive having exactly one constructor.
const DOT_ACCESS_ON_SINGLE_CONSTRUCTOR_TYPE: &str = r#"
type Box {
    mk { value : I64, tag : I64 }
}

def unwrap (b : Box) : I64 := b.value

def main : I64 := unwrap (Box.mk 5 1)
"#;

#[test]
fn dot_access_on_single_constructor_type_works() {
  assert_eq!(as_i64(&run(DOT_ACCESS_ON_SINGLE_CONSTRUCTOR_TYPE)), 5);
}

/// A local binding shadowing an existing type name still resolves as a
/// local: the parameter `Point` (deliberately named the same as the
/// `Point` struct) must be treated as a bound variable, not a module path
/// into `Point`'s own namespace -- and chains through it correctly.
const SHADOWING_LOCAL_BINDING: &str = r#"
struct Point { x : I64, y : I64 }
struct Wrapper { inner : Point }

def unwrap (Point : Wrapper) : I64 := Point.inner.x

def main : I64 := unwrap { inner := { x := 7, y := 2 } }
"#;

#[test]
fn dot_access_prefers_a_local_binding_over_a_same_named_module() {
  assert_eq!(as_i64(&run(SHADOWING_LOCAL_BINDING)), 7);
}

/// A dotted path whose first segment is NOT a local binding still
/// resolves as an ordinary qualified global reference (unaffected by the
/// new local-binding check).
const MODULE_PATH_STILL_RESOLVES_AS_GLOBAL: &str = r#"
type Shape {
    circle (radius : I64),
    rectangle { width : I64, height : I64 }
}

def main : I64 :=
    match Shape.rectangle 3 4 {
        rectangle { width, height } => width * height,
        circle { radius } => radius
    }
"#;

#[test]
fn dotted_module_path_still_resolves_as_a_global() {
  assert_eq!(as_i64(&run(MODULE_PATH_STILL_RESOLVES_AS_GLOBAL)), 12);
}

/// Dot access against a multi-constructor type has no single constructor
/// to resolve `{ fi }` against -- same `FieldPatternAmbiguousConstructor`
/// error a bare `{ .. }` match pattern would raise.
const DOT_ACCESS_ON_MULTI_CONSTRUCTOR_TYPE: &str = r#"
type Shape {
    circle (radius : I64),
    rectangle { width : I64, height : I64 }
}

def width_of (s : Shape) : I64 := s.width

def main : I64 := width_of (Shape.rectangle 3 4)
"#;

#[test]
fn dot_access_on_multi_constructor_type_is_ambiguous() {
  let err = run_err(DOT_ACCESS_ON_MULTI_CONSTRUCTOR_TYPE);
  assert!(
    err.contains("requires exactly one constructor"),
    "unexpected error: {err}"
  );
}

/// Dot access naming a field the constructor doesn't have -- same
/// `FieldPatternUnknownField` error a bare `{ nope }` match pattern would
/// raise.
const DOT_ACCESS_ON_UNKNOWN_FIELD: &str = r#"
struct Point { x : I64, y : I64 }

def z_of (p : Point) : I64 := p.z

def main : I64 := z_of { x := 1, y := 2 }
"#;

#[test]
fn dot_access_on_unknown_field_is_reported() {
  let err = run_err(DOT_ACCESS_ON_UNKNOWN_FIELD);
  assert!(err.contains("no field named"), "unexpected error: {err}");
}
