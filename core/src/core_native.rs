//! Native/builtin execution — Phase 5 of
//! `plans/implementations/core-term-closure-evaluator.md`.
//!
//! Ports `eval_term.rs::exec_prim`'s dispatch table (and its own helper
//! functions) near-verbatim, per the plan's own recommendation: these are
//! pure value-in/value-out operations with no dependency on `EvalTerm`'s
//! substitution-based representation, so reusing the *logic* while
//! retargeting the *types* (`EvalTerm` -> `core_value::Value`) is both
//! safe and the least-risk way to get real arithmetic/string ops working.
//!
//! One genuine representational difference from `eval_term.rs`: `CoreIr`
//! has no `IrLit::Bool` (see `core_ir.rs`'s doc comment — `Bool` is an
//! ordinary two-constructor inductive, same as any other, and `if`/`match`
//! already compile against its real declared constructor order rather
//! than assuming a literal boolean). So every comparison native here
//! builds its result as a `Value::Con` via `NativeTable::well_known`,
//! not a literal — `make_bool` below is the one new piece of plumbing
//! `exec_prim` didn't need.

use crate::core_eval::CoreEvalError;
use crate::core_ir::IrLit;
use crate::core_value::{NativeTable, Value};
use crate::lower_core_ir::CtorTag;
use crate::term::NumSuffix;

/// Execute a fully-saturated native call. Callers (`core_eval.rs`) are
/// responsible for only invoking this once `args.len()` has reached the
/// native's declared arity (`NativeTable::arity`) — this function doesn't
/// re-check that itself, only each op's own expected arg *count*, as a
/// defensive internal-consistency check.
pub fn exec_native(
  name: &str,
  args: &[Value],
  natives: &NativeTable,
) -> Result<Value, CoreEvalError> {
  match name {
    "i8_add" | "i16_add" | "i32_add" | "i64_add" | "u8_add" | "u16_add" | "u32_add" | "u64_add" => {
      int_binop(args, |a, b| a.wrapping_add(b))
    }
    "i8_sub" | "i16_sub" | "i32_sub" | "i64_sub" | "u8_sub" | "u16_sub" | "u32_sub" | "u64_sub" => {
      int_binop(args, |a, b| a.wrapping_sub(b))
    }
    "i8_mul" | "i16_mul" | "i32_mul" | "i64_mul" | "u8_mul" | "u16_mul" | "u32_mul" | "u64_mul" => {
      int_binop(args, |a, b| a.wrapping_mul(b))
    }
    "i8_div" | "i16_div" | "i32_div" | "i64_div" | "u8_div" | "u16_div" | "u32_div" | "u64_div" => {
      int_binop(args, |a, b| if b == 0 { 0 } else { a.wrapping_div(b) })
    }
    "u64_mod" => int_binop(args, |a, b| if b == 0 { 0 } else { a.wrapping_rem(b) }),
    "u64_xor" => int_binop(args, |a, b| a ^ b),
    "i8_eq" | "i16_eq" | "i32_eq" | "i64_eq" | "u8_eq" | "u16_eq" | "u32_eq" | "u64_eq" => {
      int_cmp(args, natives, |a, b| a == b)
    }
    "i8_lt" | "i16_lt" | "i32_lt" | "i64_lt" | "u8_lt" | "u16_lt" | "u32_lt" | "u64_lt" => {
      int_cmp(args, natives, |a, b| a < b)
    }
    "i8_gt" | "i16_gt" | "i32_gt" | "i64_gt" | "u8_gt" | "u16_gt" | "u32_gt" | "u64_gt" => {
      int_cmp(args, natives, |a, b| a > b)
    }
    "f32_add" | "f64_add" => float_binop(args, |a, b| a + b),
    "f32_sub" | "f64_sub" => float_binop(args, |a, b| a - b),
    "f32_mul" | "f64_mul" => float_binop(args, |a, b| a * b),
    "f32_div" | "f64_div" => float_binop(args, |a, b| a / b),
    "f32_eq" | "f64_eq" => float_cmp(args, natives, |a, b| a == b),
    "f32_lt" | "f64_lt" => float_cmp(args, natives, |a, b| a < b),
    "f32_gt" | "f64_gt" => float_cmp(args, natives, |a, b| a > b),
    "i8_to_string" => int_to_string(args, |v| (v as i8).to_string()),
    "i16_to_string" => int_to_string(args, |v| (v as i16).to_string()),
    "i32_to_string" => int_to_string(args, |v| (v as i32).to_string()),
    "i64_to_string" => int_to_string(args, |v| v.to_string()),
    "u8_to_string" => int_to_string(args, |v| (v as u8).to_string()),
    "u16_to_string" => int_to_string(args, |v| (v as u16).to_string()),
    "u32_to_string" => int_to_string(args, |v| (v as u32).to_string()),
    "u64_to_string" => int_to_string(args, |v| (v as u64).to_string()),
    "i64_to_u64" | "u8_to_u64" => int_to_int(args, NumSuffix::U64),
    "f32_to_string" | "f64_to_string" => float_to_string(args),
    "string_eq" => string_eq(args, natives),
    "string_concat" => string_concat(args),
    "string_length" => string_length(args),
    "string_starts_with" => string_starts_with(args, natives),
    "string_slice" => string_slice(args),
    "string_drop" => string_drop(args),
    "print_str" => print_str(args),
    "string_get" => string_get(args, natives),
    "string_to_list" => string_to_list(args, natives),
    "string_from_list" => string_from_list(args, natives),
    "bench_now" => bench_now(),
    "bench_report" => bench_report(args),
    // `CoreEvalError::UnknownNative` is keyed by id everywhere else (the
    // evaluator, which has the id on hand when the id itself is out of
    // `NativeTable`'s range); this is the one call site that only has the
    // *name* (already resolved via `NativeTable::name` before calling
    // `exec_native`) — a name-shaped native the checker/lowering pass
    // interned but this table simply has no logic for, not a lowering
    // bug, so it gets `NativeArgError` rather than a second, name-keyed
    // variant of `UnknownNative`.
    other => Err(CoreEvalError::NativeArgError(format!(
      "unknown native: {other}"
    ))),
  }
}

fn extract_int(v: &Value) -> Result<i64, CoreEvalError> {
  match v {
    Value::Lit(IrLit::Num(n, _)) => Ok(*n),
    other => Err(CoreEvalError::NativeArgError(format!(
      "expected an int literal, got {other:?}"
    ))),
  }
}

fn extract_float(v: &Value) -> Result<f64, CoreEvalError> {
  match v {
    Value::Lit(IrLit::Float(f, _)) => Ok(f.0),
    other => Err(CoreEvalError::NativeArgError(format!(
      "expected a float literal, got {other:?}"
    ))),
  }
}

fn extract_string(v: &Value) -> Result<&str, CoreEvalError> {
  match v {
    Value::Lit(IrLit::Str(s)) => Ok(s.as_str()),
    other => Err(CoreEvalError::NativeArgError(format!(
      "expected a string literal, got {other:?}"
    ))),
  }
}

fn require_ctor(ctor: Option<CtorTag>, name: &'static str) -> Result<CtorTag, CoreEvalError> {
  ctor.ok_or(CoreEvalError::MissingWellKnownCtor(name))
}

fn make_bool(natives: &NativeTable, v: bool) -> Result<Value, CoreEvalError> {
  let ctor = if v {
    require_ctor(natives.well_known.bool_true, "Bool.true")?
  } else {
    require_ctor(natives.well_known.bool_false, "Bool.false")?
  };
  Ok(Value::Con {
    tag: ctor.tag,
    args: Vec::new(),
  })
}

fn int_binop(args: &[Value], op: fn(i64, i64) -> i64) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "int binop needs 2 args".into(),
    ));
  }
  let a = extract_int(&args[0])?;
  let b = extract_int(&args[1])?;
  Ok(Value::Lit(IrLit::Num(op(a, b), NumSuffix::I64)))
}

fn int_cmp(
  args: &[Value],
  natives: &NativeTable,
  op: fn(i64, i64) -> bool,
) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError("int cmp needs 2 args".into()));
  }
  let a = extract_int(&args[0])?;
  let b = extract_int(&args[1])?;
  make_bool(natives, op(a, b))
}

fn float_binop(args: &[Value], op: fn(f64, f64) -> f64) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "float binop needs 2 args".into(),
    ));
  }
  let a = extract_float(&args[0])?;
  let b = extract_float(&args[1])?;
  Ok(Value::Lit(IrLit::Float(
    crate::term::F64Wrap(op(a, b)),
    NumSuffix::F64,
  )))
}

fn float_cmp(
  args: &[Value],
  natives: &NativeTable,
  op: fn(f64, f64) -> bool,
) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "float cmp needs 2 args".into(),
    ));
  }
  let a = extract_float(&args[0])?;
  let b = extract_float(&args[1])?;
  make_bool(natives, op(a, b))
}

fn int_to_string(args: &[Value], fmt: fn(i64) -> String) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "int_to_string needs 1 arg".into(),
    ));
  }
  let v = extract_int(&args[0])?;
  Ok(Value::Lit(IrLit::Str(fmt(v))))
}

fn int_to_int(args: &[Value], suffix: NumSuffix) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError("int cast needs 1 arg".into()));
  }
  let v = extract_int(&args[0])?;
  Ok(Value::Lit(IrLit::Num(v, suffix)))
}

fn float_to_string(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "float_to_string needs 1 arg".into(),
    ));
  }
  let v = extract_float(&args[0])?;
  Ok(Value::Lit(IrLit::Str(v.to_string())))
}

fn string_eq(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "string_eq needs 2 args".into(),
    ));
  }
  let a = extract_string(&args[0])?;
  let b = extract_string(&args[1])?;
  make_bool(natives, a == b)
}

fn string_concat(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "string_concat needs 2 args".into(),
    ));
  }
  let a = extract_string(&args[0])?;
  let b = extract_string(&args[1])?;
  Ok(Value::Lit(IrLit::Str(a.to_string() + b)))
}

fn string_length(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "string_length needs 1 arg".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  Ok(Value::Lit(IrLit::Num(s.len() as i64, NumSuffix::I64)))
}

fn string_starts_with(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "string_starts_with needs 2 args".into(),
    ));
  }
  let prefix = extract_string(&args[0])?;
  let s = extract_string(&args[1])?;
  make_bool(natives, s.starts_with(prefix))
}

fn string_slice(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.len() < 3 {
    return Err(CoreEvalError::NativeArgError(
      "string_slice needs 3 args".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  let start = (extract_int(&args[1])?.max(0) as usize).min(s.len());
  let len = extract_int(&args[2])?.max(0) as usize;
  let end = start.saturating_add(len).min(s.len());
  // Byte-oriented, matching `string_length`/`string_get`'s own byte
  // semantics -- but unlike those, `&str`'s own `[start..end]` indexing
  // PANICS if either bound doesn't land on a UTF-8 character boundary
  // (confirmed reachable: any string containing a multi-byte character,
  // sliced at an odd byte offset -- not just a theoretical edge case,
  // since string-processing code walks byte-by-byte, e.g.
  // `PARSER_COMBINATOR_SHAPED`'s own `String.drop 1 s` pattern). `get`
  // returns `None` instead of panicking for a bad boundary; falling back
  // to empty matches this function's own existing out-of-range
  // tolerance (an out-of-range `start` already produced `""`, not an
  // error) rather than crashing the whole evaluator over an in-language
  // slice call.
  let result = s.get(start..end).unwrap_or("").to_string();
  Ok(Value::Lit(IrLit::Str(result)))
}

fn string_drop(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "string_drop needs 2 args".into(),
    ));
  }
  let n = extract_int(&args[0])?.max(0) as usize;
  let s = extract_string(&args[1])?;
  // See `string_slice`'s own comment: `get` avoids panicking on a
  // non-boundary byte offset (a multi-byte character straddling it),
  // falling back to empty the same way an out-of-range `n` already did.
  let result = s.get(n..).unwrap_or("").to_string();
  Ok(Value::Lit(IrLit::Str(result)))
}

fn print_str(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "print_str needs 1 arg".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  println!("{s}");
  Ok(Value::Lit(IrLit::Str(s.to_string())))
}

fn string_get(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "string_get needs 2 args".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  let idx = extract_int(&args[1])?;
  let bytes = s.as_bytes();
  if idx < 0 || idx as usize >= bytes.len() {
    let none = require_ctor(natives.well_known.option_none, "Option.none")?;
    return Ok(Value::Con {
      tag: none.tag,
      args: Vec::new(),
    });
  }
  let some = require_ctor(natives.well_known.option_some, "Option.some")?;
  let byte = bytes[idx as usize] as i64;
  Ok(Value::Con {
    tag: some.tag,
    args: vec![Value::Lit(IrLit::Num(byte, NumSuffix::U8))],
  })
}

fn string_to_list(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "string_to_list needs 1 arg".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  let cons = require_ctor(natives.well_known.list_cons, "List.cons")?;
  let empty = require_ctor(natives.well_known.list_empty, "List.empty")?;
  let mut result = Value::Con {
    tag: empty.tag,
    args: Vec::new(),
  };
  for &byte in s.as_bytes().iter().rev() {
    result = Value::Con {
      tag: cons.tag,
      args: vec![Value::Lit(IrLit::Num(byte as i64, NumSuffix::U8)), result],
    };
  }
  Ok(result)
}

fn string_from_list(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "string_from_list needs 1 arg".into(),
    ));
  }
  let cons = require_ctor(natives.well_known.list_cons, "List.cons")?;
  let empty = require_ctor(natives.well_known.list_empty, "List.empty")?;
  let mut bytes = Vec::new();
  let mut cur = &args[0];
  loop {
    match cur {
      Value::Con { tag, args } if *tag == empty.tag && args.is_empty() => break,
      Value::Con { tag, args: cargs } if *tag == cons.tag && cargs.len() == cons.arity as usize => {
        bytes.push(extract_int(&cargs[0])? as u8);
        cur = &cargs[1];
      }
      other => {
        return Err(CoreEvalError::NativeArgError(format!(
          "expected a List U8 value, got {other:?}"
        )));
      }
    }
  }
  let s = String::from_utf8(bytes).map_err(|e| {
    CoreEvalError::NativeArgError(format!("invalid UTF-8 in string_from_list: {e}"))
  })?;
  Ok(Value::Lit(IrLit::Str(s)))
}

fn bench_now() -> Result<Value, CoreEvalError> {
  let now = std::time::SystemTime::now()
    .duration_since(std::time::UNIX_EPOCH)
    .unwrap_or_default()
    .as_millis() as i64;
  Ok(Value::Lit(IrLit::Num(now, NumSuffix::I64)))
}

fn bench_report(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "bench_report needs 2 args".into(),
    ));
  }
  let label = extract_string(&args[0])?;
  let elapsed = extract_int(&args[1])?;
  println!("  BENCH {label}: {elapsed}ms");
  Ok(Value::Lit(IrLit::Num(elapsed, NumSuffix::I64)))
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::lower_core_ir::WellKnownCtors;

  // Tag numbers here are deliberately NOT the real prelude's declared
  // order (see `lower_core_ir.rs`'s `List`/`Option`/`Bool` doc comments
  // for what that real order actually is) -- every native op here reads
  // tags exclusively through `NativeTable::well_known`, never a hardcoded
  // number, so these tests would still pass under any tag assignment;
  // using different-looking numbers than the real ones is deliberate, to
  // prove that (a hardcoded "0"/"1" match happening to agree with the
  // real order wouldn't catch a bug where `exec_native` used a literal
  // instead of `well_known`).
  fn test_natives() -> NativeTable {
    NativeTable::new(
      vec![],
      vec![],
      WellKnownCtors {
        bool_true: Some(CtorTag { tag: 7, arity: 0 }),
        bool_false: Some(CtorTag { tag: 8, arity: 0 }),
        option_some: Some(CtorTag { tag: 5, arity: 1 }),
        option_none: Some(CtorTag { tag: 6, arity: 0 }),
        list_cons: Some(CtorTag { tag: 3, arity: 2 }),
        list_empty: Some(CtorTag { tag: 4, arity: 0 }),
        io_io: None,
        result_ok: None,
        result_err: None,
      },
    )
  }

  fn int(v: i64) -> Value {
    Value::Lit(IrLit::Num(v, NumSuffix::I64))
  }

  fn string(s: &str) -> Value {
    Value::Lit(IrLit::Str(s.to_string()))
  }

  #[test]
  fn test_int_add() {
    let natives = test_natives();
    let v = exec_native("i64_add", &[int(2), int(3)], &natives).unwrap();
    assert!(matches!(v, Value::Lit(IrLit::Num(5, _))));
  }

  #[test]
  fn test_int_sub_wraps_not_panics() {
    let natives = test_natives();
    let v = exec_native("i8_sub", &[int(i64::MIN), int(1)], &natives).unwrap();
    assert!(matches!(v, Value::Lit(IrLit::Num(_, _))));
  }

  #[test]
  fn test_int_div_by_zero_is_zero_not_a_panic() {
    let natives = test_natives();
    let v = exec_native("i64_div", &[int(10), int(0)], &natives).unwrap();
    assert!(matches!(v, Value::Lit(IrLit::Num(0, _))));
  }

  #[test]
  fn test_int_eq_uses_well_known_bool_tags_not_hardcoded_ones() {
    let natives = test_natives();
    let t = exec_native("i64_eq", &[int(1), int(1)], &natives).unwrap();
    assert!(matches!(t, Value::Con { tag: 7, ref args } if args.is_empty()));
    let f = exec_native("i64_eq", &[int(1), int(2)], &natives).unwrap();
    assert!(matches!(f, Value::Con { tag: 8, ref args } if args.is_empty()));
  }

  #[test]
  fn test_int_lt_gt() {
    let natives = test_natives();
    assert!(matches!(
      exec_native("i64_lt", &[int(1), int(2)], &natives).unwrap(),
      Value::Con { tag: 7, .. }
    ));
    assert!(matches!(
      exec_native("i64_gt", &[int(1), int(2)], &natives).unwrap(),
      Value::Con { tag: 8, .. }
    ));
  }

  #[test]
  fn test_float_arithmetic_and_cmp() {
    let natives = test_natives();
    let f = |v: f64| Value::Lit(IrLit::Float(crate::term::F64Wrap(v), NumSuffix::F64));
    let sum = exec_native("f64_add", &[f(1.5), f(2.5)], &natives).unwrap();
    assert!(matches!(sum, Value::Lit(IrLit::Float(v, _)) if v.0 == 4.0));
    let eq = exec_native("f64_eq", &[f(1.0), f(1.0)], &natives).unwrap();
    assert!(matches!(eq, Value::Con { tag: 7, .. }));
  }

  #[test]
  fn test_string_eq_concat_length() {
    let natives = test_natives();
    assert!(matches!(
      exec_native("string_eq", &[string("hi"), string("hi")], &natives).unwrap(),
      Value::Con { tag: 7, .. }
    ));
    let cat = exec_native("string_concat", &[string("foo"), string("bar")], &natives).unwrap();
    assert!(matches!(cat, Value::Lit(IrLit::Str(ref s)) if s == "foobar"));
    let len = exec_native("string_length", &[string("hello")], &natives).unwrap();
    assert!(matches!(len, Value::Lit(IrLit::Num(5, _))));
  }

  #[test]
  fn test_string_slice_and_drop() {
    let natives = test_natives();
    let sliced = exec_native("string_slice", &[string("hello"), int(1), int(3)], &natives).unwrap();
    assert!(matches!(sliced, Value::Lit(IrLit::Str(ref s)) if s == "ell"));
    let dropped = exec_native("string_drop", &[int(2), string("hello")], &natives).unwrap();
    assert!(matches!(dropped, Value::Lit(IrLit::Str(ref s)) if s == "llo"));
  }

  #[test]
  fn test_string_slice_and_drop_on_non_char_boundary_does_not_panic() {
    // "héllo": h(byte 0), é(bytes 1-2), l(3), l(4), o(5) -- byte offset 2
    // sits mid-'é'. `&str`'s own `[..]` indexing panics on this; both
    // ops must instead fall back to their existing out-of-range
    // tolerance (empty string) rather than crash the evaluator.
    let natives = test_natives();
    let sliced = exec_native("string_slice", &[string("héllo"), int(2), int(2)], &natives).unwrap();
    assert!(matches!(sliced, Value::Lit(IrLit::Str(ref s)) if s.is_empty()));
    let dropped = exec_native("string_drop", &[int(2), string("héllo")], &natives).unwrap();
    assert!(matches!(dropped, Value::Lit(IrLit::Str(ref s)) if s.is_empty()));
  }

  #[test]
  fn test_int_to_string() {
    let natives = test_natives();
    let v = exec_native("i64_to_string", &[int(42)], &natives).unwrap();
    assert!(matches!(v, Value::Lit(IrLit::Str(ref s)) if s == "42"));
  }

  #[test]
  fn test_string_get_in_range_and_out_of_range() {
    let natives = test_natives();
    let some = exec_native("string_get", &[string("ab"), int(0)], &natives).unwrap();
    assert!(matches!(some, Value::Con { tag: 5, ref args } if args.len() == 1));
    let none = exec_native("string_get", &[string("ab"), int(5)], &natives).unwrap();
    assert!(matches!(none, Value::Con { tag: 6, ref args } if args.is_empty()));
  }

  #[test]
  fn test_string_to_list_and_from_list_roundtrip() {
    let natives = test_natives();
    let list = exec_native("string_to_list", &[string("hi")], &natives).unwrap();
    // "hi" -> cons(h, cons(i, empty)) -- two cons cells (tag 3) wrapping
    // one empty (tag 4).
    let Value::Con {
      tag: 3,
      args: ref outer,
    } = list
    else {
      panic!("expected an outer List.cons cell, got {list:?}")
    };
    assert_eq!(outer.len(), 2);
    let back = exec_native("string_from_list", std::slice::from_ref(&list), &natives).unwrap();
    assert!(matches!(back, Value::Lit(IrLit::Str(ref s)) if s == "hi"));
  }

  #[test]
  fn test_unknown_native_errors() {
    let natives = test_natives();
    let err = exec_native("totally_made_up_native", &[], &natives).unwrap_err();
    assert!(matches!(err, CoreEvalError::NativeArgError(_)));
  }

  #[test]
  fn test_missing_well_known_ctor_errors_instead_of_panicking() {
    let natives = NativeTable::new(vec![], vec![], WellKnownCtors::default());
    let err = exec_native("i64_eq", &[int(1), int(1)], &natives).unwrap_err();
    assert!(matches!(
      err,
      CoreEvalError::MissingWellKnownCtor("Bool.true")
    ));
  }
}
