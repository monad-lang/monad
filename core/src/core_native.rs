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
    "print_str" => print_str(args, natives),
    "string_get" => string_get(args, natives),
    "string_get_char" => string_get_char(args, natives),
    "string_to_list" => string_to_list(args, natives),
    "string_from_list" => string_from_list(args, natives),
    "bench_now" => bench_now(),
    "bench_report" => bench_report(args, natives),
    "read_file" => read_file(args, natives),
    "write_file" => write_file(args, natives),
    "file_exists" => file_exists(args, natives),
    "get_env" => get_env(args, natives),
    "exec_cmd" => exec_cmd(args, natives),
    "fork_io" => fork_io(args, natives),
    // `await_fiber` is NOT dispatched here — it needs `globals`/`cache`
    // (not just `natives`) to actually run the fiber's deferred action;
    // `core_eval::fire_or_accumulate` intercepts it before ever calling
    // this function. See `await_fiber`'s own doc comment.
    "cancel_fiber" => cancel_fiber(args, natives),
    "sleep_io" => sleep_io(args, natives),
    "scope_new" => scope_new(natives),
    "scope_fork" => scope_fork(args, natives),
    "scope_drop" => scope_drop(args, natives),
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

// TODO: `IO` is slated to be replaced with an opaque indexed monad whose
// internal value isn't reachable via an ordinary constructor match --
// this `io_io`-wrapping helper will need to change to whatever that
// type's own (non-structural) construction mechanism ends up being once
// that lands.
fn io_wrap(natives: &NativeTable, inner: Value) -> Result<Value, CoreEvalError> {
  let io = require_ctor(natives.well_known.io_io, "IO.io")?;
  Ok(Value::Con {
    tag: io.tag,
    args: vec![inner],
  })
}

fn print_str(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "print_str needs 1 arg".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  println!("{s}");
  // `IO.println`'s declared type is `IO Unit`, and `Monad.bind`'s own
  // `IO` instance (init/io.mo) pattern-matches its argument via `match a
  // { io a => f a }` -- an unwrapped return value here was a real,
  // pre-existing bug (this native predates this session's own changes),
  // just never hit by anything that BINDS a `println` call via `<-`/
  // `Monad.bind` rather than discarding its result outright. `Unit`'s
  // own runtime shape still doesn't matter (never pattern-matched), so
  // any inner value works -- kept as the string for minimal disruption.
  io_wrap(natives, Value::Lit(IrLit::Str(s.to_string())))
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

/// `String.get_char (s : String) (i : I64) : Option Char` — indexes by
/// CHARACTER (not byte, unlike `string_get`'s `Option U8`), mirroring
/// the tree-walker's own `eval::native::string_get_char` exactly.
fn string_get_char(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "string_get_char needs 2 args".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  let idx = extract_int(&args[1])?;
  let chars: Vec<char> = s.chars().collect();
  if idx < 0 || idx as usize >= chars.len() {
    let none = require_ctor(natives.well_known.option_none, "Option.none")?;
    return Ok(Value::Con {
      tag: none.tag,
      args: Vec::new(),
    });
  }
  let some = require_ctor(natives.well_known.option_some, "Option.some")?;
  Ok(Value::Con {
    tag: some.tag,
    args: vec![Value::Lit(IrLit::Char(chars[idx as usize]))],
  })
}

/// `IO.read_file (path : String) : IO String` — `Monad.bind`'s own `IO`
/// instance (init/io.mo) pattern-matches its argument via `match a { io
/// a => f a }`, so a real `IO.io`-wrapped `Con` is required, not a bare
/// `String` (see `io_wrap`'s own doc comment); a read failure is a
/// genuine evaluation error, same as the tree-walker's own
/// `eval::native::read_file`.
fn read_file(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "read_file needs 1 arg".into(),
    ));
  }
  let path = extract_string(&args[0])?;
  let content = std::fs::read_to_string(path)
    .map_err(|e| CoreEvalError::NativeArgError(format!("read_file {path} failed: {e}")))?;
  io_wrap(natives, Value::Lit(IrLit::Str(content)))
}

/// `IO.write_file (path : String) (content : String) : IO Unit` — see
/// `read_file`'s own doc comment on why the `IO.io` wrapping is
/// required; `Unit`'s own runtime shape still doesn't matter (never
/// pattern-matched), so any inner value works.
fn write_file(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "write_file needs 2 args".into(),
    ));
  }
  let path = extract_string(&args[0])?;
  let content = extract_string(&args[1])?;
  std::fs::write(path, content)
    .map_err(|e| CoreEvalError::NativeArgError(format!("write_file {path} failed: {e}")))?;
  io_wrap(natives, Value::Lit(IrLit::Str(String::new())))
}

/// `IO.file_exists (path : String) : IO Bool` — see `read_file`'s own
/// doc comment on why the `IO.io` wrapping is required.
fn file_exists(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "file_exists needs 1 arg".into(),
    ));
  }
  let path = extract_string(&args[0])?;
  let exists = make_bool(natives, std::fs::metadata(path).is_ok())?;
  io_wrap(natives, exists)
}

/// `IO.get_env (s : String) : IO (Option String)` — see `read_file`'s
/// own doc comment on why the `IO.io` wrapping is required; the INNER
/// `Option` needs the same real-`Con` treatment as `string_get`'s own
/// `Option U8`, for the same reason.
fn get_env(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError("get_env needs 1 arg".into()));
  }
  let name = extract_string(&args[0])?;
  let opt = match std::env::var(name) {
    Ok(value) => {
      let some = require_ctor(natives.well_known.option_some, "Option.some")?;
      Value::Con {
        tag: some.tag,
        args: vec![Value::Lit(IrLit::Str(value))],
      }
    }
    Err(_) => {
      let none = require_ctor(natives.well_known.option_none, "Option.none")?;
      Value::Con {
        tag: none.tag,
        args: Vec::new(),
      }
    }
  };
  io_wrap(natives, opt)
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

/// Reads a `List String` value into an owned `Vec<String>` — the
/// argument-decoding counterpart to `string_from_list`'s `List U8`
/// walk just above, same cons/empty tag-matching idiom, just decoding
/// each element via `extract_string` instead of `extract_int`. Used by
/// `exec_cmd` to decode its `args : List String` parameter.
fn extract_string_list(v: &Value, natives: &NativeTable) -> Result<Vec<String>, CoreEvalError> {
  let cons = require_ctor(natives.well_known.list_cons, "List.cons")?;
  let empty = require_ctor(natives.well_known.list_empty, "List.empty")?;
  let mut result = Vec::new();
  let mut cur = v;
  loop {
    match cur {
      Value::Con { tag, args } if *tag == empty.tag && args.is_empty() => break,
      Value::Con { tag, args: cargs } if *tag == cons.tag && cargs.len() == cons.arity as usize => {
        result.push(extract_string(&cargs[0])?.to_string());
        cur = &cargs[1];
      }
      other => {
        return Err(CoreEvalError::NativeArgError(format!(
          "expected a List String value, got {other:?}"
        )));
      }
    }
  }
  Ok(result)
}

/// `Process.exec_cmd (cmd : String) (args : List String) : IO I64` —
/// ports `eval::native::exec_cmd`'s logic (`core/src/eval/native.rs`,
/// the tree-walker's own native table) near-verbatim, retargeted from
/// `Term` to `Value`/`IrLit`; see `read_file`'s own doc comment on why
/// the `IO.io` wrapping is required.
fn exec_cmd(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "exec_cmd needs 2 args".into(),
    ));
  }
  let cmd = extract_string(&args[0])?;
  let cmd_args = extract_string_list(&args[1], natives)?;
  let status = std::process::Command::new(cmd)
    .args(&cmd_args)
    .status()
    .map_err(|e| CoreEvalError::NativeArgError(format!("exec_cmd \"{cmd}\" failed: {e}")))?;
  let exit_code = status.code().unwrap_or(-1) as i64;
  io_wrap(natives, Value::Lit(IrLit::Num(exit_code, NumSuffix::I64)))
}

fn bench_now() -> Result<Value, CoreEvalError> {
  let now = std::time::SystemTime::now()
    .duration_since(std::time::UNIX_EPOCH)
    .unwrap_or_default()
    .as_millis() as i64;
  Ok(Value::Lit(IrLit::Num(now, NumSuffix::I64)))
}

fn bench_report(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "bench_report needs 2 args".into(),
    ));
  }
  let label = extract_string(&args[0])?;
  let elapsed = extract_int(&args[1])?;
  println!("  BENCH {label}: {elapsed}ms");
  // Declared `Bool` (`std/bench.mo`), same as the tree-walker's own
  // `eval::native::bench_report` (`Ok(b_true())`) -- returning a bare
  // `I64` here (the previous behavior) type-checked fine at compile time
  // (natives aren't checked against their declared signature the way
  // ordinary defs are) but broke every `#[test] def profile_* : Bool`
  // caller at runtime, since `detect_test_result_value` only knows how
  // to classify `Bool`/`IO`/`Result` constructors.
  make_bool(natives, true)
}

/// A forked-but-not-yet-awaited (or already-completed) fiber. Mirrors
/// `eval::native::FiberHandle` exactly, just holding a `Value` (the
/// closure to run) instead of a `Term` — see `fork_io`'s own doc comment
/// for why forking defers rather than actually running anything.
struct FiberHandle {
  fiber: crate::runtime::fiber::Fiber<Value>,
  action: Option<Value>,
}

/// A `scope_new`-allocated scope: just the set of fiber ids forked under
/// it, so `scope_drop` can cancel every one still outstanding. Mirrors
/// `eval::native::ScopeHandle`.
struct ScopeHandle {
  fiber_ids: std::sync::Mutex<Vec<u64>>,
}

/// Fiber/scope handles are opaque to surface code (`std/concurrent/
/// fiber.mo`'s own doc comment: "do not pattern match on them") — a bare
/// `Num` carrying `runtime::global`'s registry id is enough, the same way
/// the tree-walker's own `Literal::Foreign(id)` served this purpose.
/// `U64` since `runtime::global::register` itself returns `u64`.
fn handle_value(id: u64) -> Value {
  Value::Lit(IrLit::Num(id as i64, NumSuffix::U64))
}

fn extract_handle_id(v: &Value) -> Result<u64, CoreEvalError> {
  match v {
    Value::Lit(IrLit::Num(n, _)) => Ok(*n as u64),
    other => Err(CoreEvalError::NativeArgError(format!(
      "expected an opaque fiber/scope handle, got {other:?}"
    ))),
  }
}

/// `Unit`'s own runtime shape never matters (never pattern-matched, same
/// as `io_wrap`'s callers elsewhere in this file) — an empty string is as
/// good a placeholder as any.
fn unit_value() -> Value {
  Value::Lit(IrLit::Str(String::new()))
}

/// `forkIO (action : Unit -> IO A) : IO (Fiber A)` (`std/concurrent/
/// fiber.mo`) — defers `action` rather than running it: registers a
/// handle holding the still-unapplied closure. This "fiber" system is
/// cooperative/lazy, not real OS-thread concurrency — `await_fiber` is
/// what actually runs the action (applying it to `unit`), the first time
/// it's awaited. Mirrors `eval::native::fork_io` exactly.
fn fork_io(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  let action = args
    .first()
    .cloned()
    .ok_or_else(|| CoreEvalError::NativeArgError("fork_io needs 1 arg".into()))?;
  if !matches!(action, Value::Closure { .. }) {
    return Err(CoreEvalError::NativeArgError(format!(
      "forkIO expected a function (Unit -> IO A), got {action:?}"
    )));
  }
  let handle = FiberHandle {
    fiber: crate::runtime::fiber::Fiber::new(),
    action: Some(action),
  };
  let id = crate::runtime::global::register(handle);
  io_wrap(natives, handle_value(id))
}

/// `await_fiber (f : Fiber A) : IO A` — the one fiber/scope native that
/// needs the full evaluator (`globals`/`cache`), not just `exec_native`'s
/// ordinary `(name, args, natives)` shape: running the fiber's deferred
/// action means applying its stored closure to `unit` via
/// `core_eval::apply`. Dispatched directly from `core_eval::fire_or_
/// accumulate`, bypassing `exec_native`'s generic table entirely — see
/// that function's own doc comment. Mirrors `eval::native::await_fiber`.
pub fn await_fiber(
  args: &[Value],
  globals: &crate::core_value::GlobalTable,
  natives: &NativeTable,
  cache: &mut crate::core_value::GlobalCache,
) -> Result<Value, CoreEvalError> {
  let f = args
    .first()
    .ok_or_else(|| CoreEvalError::NativeArgError("await_fiber needs 1 arg".into()))?;
  let id = extract_handle_id(f)?;
  let handle = crate::runtime::global::take::<FiberHandle>(id)
    .ok_or_else(|| CoreEvalError::NativeArgError(format!("fiber handle {id} not found")))?;
  if handle.fiber.is_done() && handle.fiber.state() == crate::runtime::fiber::FiberState::Cancelled
  {
    return Err(CoreEvalError::NativeArgError(format!(
      "fiber {id} was cancelled"
    )));
  }
  let action = handle
    .action
    .ok_or_else(|| CoreEvalError::NativeArgError(format!("fiber {id} already awaited")))?;
  let result = crate::core_eval::apply(action, unit_value(), globals, natives, cache)?;
  handle.fiber.set_result(result.clone());
  handle
    .fiber
    .set_state(crate::runtime::fiber::FiberState::Completed);
  Ok(result)
}

/// `cancel_fiber (f : Fiber A) : IO Unit` — marks the fiber cancelled
/// without running it (a no-op if it's already running/done, same as
/// `Fiber::cancel`'s own guard). Mirrors `eval::native::cancel_fiber`.
fn cancel_fiber(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  let f = args
    .first()
    .ok_or_else(|| CoreEvalError::NativeArgError("cancel_fiber needs 1 arg".into()))?;
  let id = extract_handle_id(f)?;
  crate::runtime::global::with::<FiberHandle, _>(id, |h| h.fiber.cancel())
    .ok_or_else(|| CoreEvalError::NativeArgError(format!("fiber handle {id} not found")))?;
  io_wrap(natives, unit_value())
}

/// `sleepIO (ms : I64) : IO Unit` (`std/concurrent/combine.mo`). Mirrors
/// `eval::native::sleep_io`.
fn sleep_io(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  let ms = extract_int(
    args
      .first()
      .ok_or_else(|| CoreEvalError::NativeArgError("sleep_io needs 1 arg".into()))?,
  )?;
  std::thread::sleep(std::time::Duration::from_millis(ms.max(0) as u64));
  io_wrap(natives, unit_value())
}

/// `scope_new : IO Scope` — a zero-arg (point-free) native. Mirrors
/// `eval::native::scope_new`.
fn scope_new(natives: &NativeTable) -> Result<Value, CoreEvalError> {
  let handle = ScopeHandle {
    fiber_ids: std::sync::Mutex::new(Vec::new()),
  };
  let id = crate::runtime::global::register(handle);
  io_wrap(natives, handle_value(id))
}

/// `scope_fork (s : Scope) (action : Unit -> IO A) : IO (Fiber A)` — like
/// `fork_io`, defers `action` rather than running it, but also records
/// the new fiber's id under `s`'s own `ScopeHandle` so `scope_drop` can
/// cancel it later. Mirrors `eval::native::scope_fork`.
fn scope_fork(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "scope_fork needs 2 args".into(),
    ));
  }
  let scope_id = extract_handle_id(&args[0])?;
  let action = args[1].clone();
  if !matches!(action, Value::Closure { .. }) {
    return Err(CoreEvalError::NativeArgError(format!(
      "scope_fork expected a function (Unit -> IO A), got {action:?}"
    )));
  }
  let handle = FiberHandle {
    fiber: crate::runtime::fiber::Fiber::new(),
    action: Some(action),
  };
  let fiber_id = crate::runtime::global::register(handle);
  crate::runtime::global::with::<ScopeHandle, _>(scope_id, |scope| {
    scope.fiber_ids.lock().unwrap().push(fiber_id);
  })
  .ok_or_else(|| CoreEvalError::NativeArgError(format!("scope {scope_id} not found")))?;
  io_wrap(natives, handle_value(fiber_id))
}

/// `scope_drop (s : Scope) : IO Unit` — cancels every fiber forked under
/// `s` that hasn't been awaited/cancelled yet. Mirrors
/// `eval::native::scope_drop`.
fn scope_drop(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  let s = args
    .first()
    .ok_or_else(|| CoreEvalError::NativeArgError("scope_drop needs 1 arg".into()))?;
  let scope_id = extract_handle_id(s)?;
  let handle = crate::runtime::global::take::<ScopeHandle>(scope_id)
    .ok_or_else(|| CoreEvalError::NativeArgError(format!("scope {scope_id} not found")))?;
  let fiber_ids = handle.fiber_ids.into_inner().unwrap();
  for fid in &fiber_ids {
    crate::runtime::global::with::<FiberHandle, _>(*fid, |h| h.fiber.cancel());
  }
  io_wrap(natives, unit_value())
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
