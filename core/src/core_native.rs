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

/// Natives safe to run during macro-expansion-time "meta" evaluation
/// (`core/src/eval/meta_compile.rs`) — deterministic, no IO/concurrency/
/// mutable shared state. A **fail-closed allowlist**, not a blocklist: a
/// native not on this list is unavailable in a pure `GlobalCache`
/// (`GlobalCache::new_pure`, checked by `core_eval.rs`'s
/// `fire_or_accumulate` before dispatch), including any native added to
/// this file's `exec_native` match in the future that nobody explicitly
/// adds here — the safe default for something a derive/meta handler
/// might call. `await_fiber` (handled outside `exec_native`'s own match,
/// directly in `core_eval.rs::fire_or_accumulate`) is excluded the same
/// way, via the same check.
const PURE_NATIVES: &[&str] = &[
  "i8_add",
  "i16_add",
  "i32_add",
  "i64_add",
  "u8_add",
  "u16_add",
  "u32_add",
  "u64_add",
  "i8_sub",
  "i16_sub",
  "i32_sub",
  "i64_sub",
  "u8_sub",
  "u16_sub",
  "u32_sub",
  "u64_sub",
  "i8_mul",
  "i16_mul",
  "i32_mul",
  "i64_mul",
  "u8_mul",
  "u16_mul",
  "u32_mul",
  "u64_mul",
  "i8_div",
  "i16_div",
  "i32_div",
  "i64_div",
  "u8_div",
  "u16_div",
  "u32_div",
  "u64_div",
  "u64_mod",
  "u64_xor",
  "i8_eq",
  "i16_eq",
  "i32_eq",
  "i64_eq",
  "u8_eq",
  "u16_eq",
  "u32_eq",
  "u64_eq",
  "i8_lt",
  "i16_lt",
  "i32_lt",
  "i64_lt",
  "u8_lt",
  "u16_lt",
  "u32_lt",
  "u64_lt",
  "i8_gt",
  "i16_gt",
  "i32_gt",
  "i64_gt",
  "u8_gt",
  "u16_gt",
  "u32_gt",
  "u64_gt",
  "u32_and",
  "u32_or",
  "u32_xor",
  "u32_shl",
  "u32_shr",
  "u8_to_u32",
  "u32_to_u8",
  "i64_to_u32",
  "i64_to_u64",
  "u8_to_u64",
  "f32_add",
  "f64_add",
  "f32_sub",
  "f64_sub",
  "f32_mul",
  "f64_mul",
  "f32_div",
  "f64_div",
  "f32_eq",
  "f64_eq",
  "f32_lt",
  "f64_lt",
  "f32_gt",
  "f64_gt",
  "i8_to_string",
  "i16_to_string",
  "i32_to_string",
  "i64_to_string",
  "u8_to_string",
  "u16_to_string",
  "u32_to_string",
  "u64_to_string",
  "f32_to_string",
  "f64_to_string",
  "string_eq",
  "string_concat",
  "string_concat_list",
  "string_length",
  "string_starts_with",
  "string_slice",
  "string_drop",
  "string_get",
  "string_get_char",
  "string_to_list",
  "string_from_list",
  "string_to_lowercase",
  // `std/array.mo`. Pure by construction: `array_new`/`array_with`
  // allocate a FRESH `Con` rather than writing through an existing one,
  // and `array_len`/`array_get` only read. `array_set_in_place` and
  // `array_freeze` are deliberately absent -- they are `IO`-typed, and
  // belong with `read_file`/`write_file` in the excluded set below.
  "array_new",
  "array_len",
  "array_get",
  "array_with",
];

/// Explicitly excluded (for documentation/grep-ability, not consulted by
/// `is_pure_native` — the allowlist above is authoritative): `print_str`
/// (IO), `current_time`/`bench_report` (non-deterministic timing),
/// `read_file`/`write_file`/`file_exists`/`is_dir`/`list_dir`/`get_env`/
/// `exec_cmd` (filesystem/process IO), `fork_io`/`cancel_fiber`/
/// `sleep_io`/`scope_new`/`scope_fork`/`scope_drop`/`await_fiber`
/// (concurrency/shared mutable state).
pub fn is_pure_native(name: &str) -> bool {
  PURE_NATIVES.contains(&name)
}

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
    "i8_add" | "i16_add" | "i32_add" | "i64_add" | "u8_add" | "u16_add" | "u64_add" => {
      int_binop(args, |a, b| a.wrapping_add(b))
    }
    "i8_sub" | "i16_sub" | "i32_sub" | "i64_sub" | "u8_sub" | "u16_sub" | "u64_sub" => {
      int_binop(args, |a, b| a.wrapping_sub(b))
    }
    "i8_mul" | "i16_mul" | "i32_mul" | "i64_mul" | "u8_mul" | "u16_mul" | "u64_mul" => {
      int_binop(args, |a, b| a.wrapping_mul(b))
    }
    "i8_div" | "i16_div" | "i32_div" | "i64_div" | "u8_div" | "u16_div" | "u64_div" => {
      int_binop(args, |a, b| if b == 0 { 0 } else { a.wrapping_div(b) })
    }
    "u64_mod" => int_binop(args, |a, b| if b == 0 { 0 } else { a.wrapping_rem(b) }),
    "u64_xor" => int_binop(args, |a, b| a ^ b),
    "i8_eq" | "i16_eq" | "i32_eq" | "i64_eq" | "u8_eq" | "u16_eq" | "u64_eq" => {
      int_cmp(args, natives, |a, b| a == b)
    }
    "i8_lt" | "i16_lt" | "i32_lt" | "i64_lt" | "u8_lt" | "u16_lt" | "u64_lt" => {
      int_cmp(args, natives, |a, b| a < b)
    }
    "i8_gt" | "i16_gt" | "i32_gt" | "i64_gt" | "u8_gt" | "u16_gt" | "u64_gt" => {
      int_cmp(args, natives, |a, b| a > b)
    }
    // `U32` is pulled out of the generic groups above and given
    // width-correct treatment (mask to 32 bits before AND after each
    // op) via `int_binop_width`/`int_div_width`/`int_cmp_width` — see
    // those helpers' doc comments. The same missing-width-mask bug
    // affects `I8`/`I16`/`I32`/`U8`/`U16` above too (confirmed via a
    // live repro: `I8.add 100i8 100i8` compared against `-56i8` reports
    // NOT EQUAL instead of wrapping+comparing correctly) — fixing those
    // is a larger, separable change, tracked as a follow-up rather than
    // done here. `U32` needed fixing now because SHA-256 depends on
    // correct mod-2^32 wraparound.
    "u32_add" => int_binop_width(args, NumSuffix::U32, i64::wrapping_add),
    "u32_sub" => int_binop_width(args, NumSuffix::U32, i64::wrapping_sub),
    "u32_mul" => int_binop_width(args, NumSuffix::U32, i64::wrapping_mul),
    "u32_div" => int_div_width(args, NumSuffix::U32),
    "u32_eq" => int_cmp_width(args, natives, NumSuffix::U32, |a, b| a == b),
    "u32_lt" => int_cmp_width(args, natives, NumSuffix::U32, |a, b| a < b),
    "u32_gt" => int_cmp_width(args, natives, NumSuffix::U32, |a, b| a > b),
    "u32_and" => int_binop_width(args, NumSuffix::U32, |a, b| a & b),
    "u32_or" => int_binop_width(args, NumSuffix::U32, |a, b| a | b),
    "u32_xor" => int_binop_width(args, NumSuffix::U32, |a, b| a ^ b),
    "u32_shl" => int_binop_width(args, NumSuffix::U32, |a, b| a.wrapping_shl(b as u32)),
    "u32_shr" => int_binop_width(args, NumSuffix::U32, |a, b| a.wrapping_shr(b as u32)),
    "u8_to_u32" => int_to_int(args, NumSuffix::U32),
    "u32_to_u8" => int_to_int(args, NumSuffix::U8),
    "i64_to_u32" => int_to_int(args, NumSuffix::U32),
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
    "string_lt" => string_lt(args, natives),
    "string_gt" => string_gt(args, natives),
    "string_hash" => string_hash(args),
    "string_concat" => string_concat(args),
    "string_concat_list" => string_concat_list(args, natives),
    "string_length" => string_length(args),
    "string_to_lowercase" => string_to_lowercase(args),
    "string_starts_with" => string_starts_with(args, natives),
    "string_slice" => string_slice(args),
    "string_drop" => string_drop(args),
    "print_str" => print_str(args, natives),
    "array_new" => array_new(args, natives),
    "array_len" => array_len(args),
    "array_get" => array_get(args, natives),
    "array_with" => array_with(args, natives),
    "array_set_in_place" => array_set_in_place(args, natives),
    "array_freeze" => array_freeze(args, natives),
    "string_get" => string_get(args, natives),
    "string_get_char" => string_get_char(args, natives),
    "string_to_list" => string_to_list(args, natives),
    "string_from_list" => string_from_list(args, natives),
    "current_time" => current_time(natives),
    "bench_report" => bench_report(args, natives),
    "read_file" => read_file(args, natives),
    "write_file" => write_file(args, natives),
    "file_exists" => file_exists(args, natives),
    "is_dir" => is_dir(args, natives),
    "list_dir" => list_dir(args, natives),
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
    "process_id" => process_id(),
    "build_commit" => build_commit(),
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

/// Like `extract_string`, but returns the underlying `SharedStr` itself
/// rather than a derived `&str` — needed only by `string_slice`/
/// `string_drop`, which construct a new O(1) view via `SharedStr::
/// subslice`/`drop_prefix` rather than a copied `&str`.
fn extract_shared_str(v: &Value) -> Result<&crate::shared_str::SharedStr, CoreEvalError> {
  match v {
    Value::Lit(IrLit::Str(s)) => Ok(s),
    other => Err(CoreEvalError::NativeArgError(format!(
      "expected a string literal, got {other:?}"
    ))),
  }
}

fn require_ctor(ctor: Option<CtorTag>, name: &'static str) -> Result<CtorTag, CoreEvalError> {
  ctor.ok_or_else(|| CoreEvalError::MissingWellKnownCtor(name))
}

fn make_bool(natives: &NativeTable, v: bool) -> Result<Value, CoreEvalError> {
  let ctor = if v {
    require_ctor(natives.well_known.bool_true, "Bool.true")?
  } else {
    require_ctor(natives.well_known.bool_false, "Bool.false")?
  };
  Ok(Value::Con {
    tag: ctor.tag,
    args: std::sync::Arc::new(Vec::new().into()),
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

/// Truncate/reinterpret `v`'s low bits to the Rust integer type matching
/// `suffix`, then sign/zero-extend back to `i64` — i.e. project `v` onto
/// its width's canonical range. Used to make width-specific natives
/// (`u32_add` etc., unlike the generic, unmasked `int_binop` above)
/// actually correct: `int_binop` computes on the raw, unmasked `i64`
/// payload and always tags the result `NumSuffix::I64` regardless of the
/// real operand width, so e.g. two `U32` values that are congruent mod
/// 2^32 but carry different raw `i64` representations compare unequal.
/// Confirmed live for `I8`: `I8.add 100i8 100i8` compared against the
/// wrapped `-56i8` reports not-equal instead of wrapping+comparing
/// correctly first. `U32` is fixed via this helper (see `int_binop_width`
/// /`int_div_width`/`int_cmp_width` below); the same bug in
/// `I8`/`I16`/`I32`/`U8`/`U16` is a separate, out-of-scope follow-up.
fn mask_to_suffix(v: i64, suffix: NumSuffix) -> i64 {
  match suffix {
    NumSuffix::I8 => v as i8 as i64,
    NumSuffix::I16 => v as i16 as i64,
    NumSuffix::I32 => v as i32 as i64,
    NumSuffix::I64 => v,
    NumSuffix::U8 => v as u8 as i64,
    NumSuffix::U16 => v as u16 as i64,
    NumSuffix::U32 => v as u32 as i64,
    NumSuffix::U64 => v as u64 as i64,
    NumSuffix::F32 | NumSuffix::F64 => v, // not used for float ops
  }
}

/// Width-correct counterpart to `int_binop`: masks both operands to
/// `suffix`'s canonical range before calling `op`, and masks the result
/// again before tagging it with `suffix` (instead of always `I64`).
/// Since both operands are pre-masked, `op` itself can stay a plain
/// `i64` closure — e.g. a masked `U32` sum is at most just under 2^33,
/// nowhere near `i64`'s own range, so no separate `u32`-typed closure is
/// needed even for `wrapping_shl`/`wrapping_shr` (the pre-masked operand
/// is always non-negative, so plain `i64` shifts behave correctly).
fn int_binop_width(
  args: &[Value],
  suffix: NumSuffix,
  op: fn(i64, i64) -> i64,
) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "int binop needs 2 args".into(),
    ));
  }
  let a = mask_to_suffix(extract_int(&args[0])?, suffix);
  let b = mask_to_suffix(extract_int(&args[1])?, suffix);
  Ok(Value::Lit(IrLit::Num(
    mask_to_suffix(op(a, b), suffix),
    suffix,
  )))
}

/// Width-correct division: masks operands, zero-checks the (masked)
/// divisor, then masks the result. See `int_binop_width`'s doc comment.
fn int_div_width(args: &[Value], suffix: NumSuffix) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError("int div needs 2 args".into()));
  }
  let a = mask_to_suffix(extract_int(&args[0])?, suffix);
  let b = mask_to_suffix(extract_int(&args[1])?, suffix);
  if b == 0 {
    return Err(CoreEvalError::NativeArgError("division by zero".into()));
  }
  Ok(Value::Lit(IrLit::Num(
    mask_to_suffix(a.wrapping_div(b), suffix),
    suffix,
  )))
}

/// Width-correct counterpart to `int_cmp`: masks both operands to
/// `suffix`'s canonical range before comparing. See `int_binop_width`'s
/// doc comment for why this matters (raw, unmasked comparison is the
/// concrete bug this fixes for `U32`).
fn int_cmp_width(
  args: &[Value],
  natives: &NativeTable,
  suffix: NumSuffix,
  op: fn(i64, i64) -> bool,
) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError("int cmp needs 2 args".into()));
  }
  let a = mask_to_suffix(extract_int(&args[0])?, suffix);
  let b = mask_to_suffix(extract_int(&args[1])?, suffix);
  make_bool(natives, op(a, b))
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
  Ok(Value::Lit(IrLit::Str(fmt(v).into())))
}

fn int_to_int(args: &[Value], suffix: NumSuffix) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError("int cast needs 1 arg".into()));
  }
  let v = extract_int(&args[0])?;
  // Mask to the target width instead of passing the raw payload through
  // unchanged — strictly safer (a no-op for an already-canonical value),
  // and correct for narrowing casts like `u32_to_u8`.
  Ok(Value::Lit(IrLit::Num(mask_to_suffix(v, suffix), suffix)))
}

fn float_to_string(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "float_to_string needs 1 arg".into(),
    ));
  }
  let v = extract_float(&args[0])?;
  Ok(Value::Lit(IrLit::Str(v.to_string().into())))
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

/// Byte-lexicographic `<`/`>`, matching `init/string.mo`'s self-hosted
/// `bytes_lt`/`bytes_gt` semantics exactly (both walk `String.to_list`'s
/// `List U8` byte-by-byte; Rust's `&str` `Ord` is also plain byte-wise
/// comparison, since UTF-8's byte ordering agrees with codepoint
/// ordering). See self-hosted-compiler-perf.md Step 2: a temporary,
/// pragmatic native fast path for a self-hosted function whose cost was
/// dominated by an allocation-heavy `String` -> `List U8` conversion
/// rather than genuine self-hosted logic — mirrors `string_eq` above,
/// which already had this native path.
fn string_lt(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "string_lt needs 2 args".into(),
    ));
  }
  let a = extract_string(&args[0])?;
  let b = extract_string(&args[1])?;
  make_bool(natives, a < b)
}

fn string_gt(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "string_gt needs 2 args".into(),
    ));
  }
  let a = extract_string(&args[0])?;
  let b = extract_string(&args[1])?;
  make_bool(natives, a > b)
}

/// djb2 hash, bit-identical to `init/string.mo`'s self-hosted
/// `String.hash_bytes`/`String.hash` (`hash = hash*33 + byte`, seed
/// `5381`, folded left-to-right over the string's bytes — same wrapping
/// `U64` semantics as `u64_mul`/`u64_add` above, so a plain Rust `u64`
/// `wrapping_mul`/`wrapping_add` fold reproduces it exactly). Operates
/// directly on `s.as_bytes()` (UTF-8 bytes in source order), the same
/// bytes `String.to_list` would materialize as a `List U8` one cons cell
/// at a time — this just skips that allocation.
fn string_hash(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "string_hash needs 1 arg".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  let hash = s.as_bytes().iter().fold(5381u64, |acc, &b| {
    acc.wrapping_mul(33).wrapping_add(b as u64)
  });
  Ok(Value::Lit(IrLit::Num(hash as i64, NumSuffix::U64)))
}

fn string_concat(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "string_concat needs 2 args".into(),
    ));
  }
  let a = extract_string(&args[0])?;
  let b = extract_string(&args[1])?;
  Ok(Value::Lit(IrLit::Str((a.to_string() + b).into())))
}

/// `String.concat_list` (init/string.mo). Concatenates a `List String`
/// in one pass instead of folding `String.concat`, which is quadratic in
/// the total length. The host needs it as much as the compiled runtime
/// does: building v31 means this evaluator interprets the compiler's own
/// LLVM emitters.
fn string_concat_list(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "string_concat_list needs 1 arg".into(),
    ));
  }
  let cons = require_ctor(natives.well_known.list_cons, "List.cons")?;
  let mut out = String::new();
  let mut node = &args[0];
  loop {
    match node {
      Value::Con { tag, args: fields } if *tag == cons.tag && fields.len() == 2 => {
        out.push_str(extract_string(&fields[0])?);
        node = &fields[1];
      }
      _ => break,
    }
  }
  Ok(Value::Lit(IrLit::Str(out.into())))
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

fn string_to_lowercase(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "string_to_lowercase needs 1 arg".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  Ok(Value::Lit(IrLit::Str(s.to_lowercase().into())))
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
  let s = extract_shared_str(&args[0])?;
  let start = (extract_int(&args[1])?.max(0) as usize).min(s.len());
  let len = extract_int(&args[2])?.max(0) as usize;
  let end = start.saturating_add(len).min(s.len());
  // O(1): `SharedStr::subslice` shares `s`'s backing `Arc<str>` rather
  // than copying bytes -- this used to be `s.get(start..end).unwrap_or(
  // "").to_string()`, a full copy on every call regardless of how small
  // the slice was (the dominant cost of self-hosted parsing before
  // `SharedStr` existed; see `shared_str.rs`'s doc comment). Byte-
  // oriented, matching `string_length`/`string_get`'s own byte
  // semantics -- but unlike those, naive `[start..end]` indexing PANICS
  // if either bound doesn't land on a UTF-8 character boundary
  // (confirmed reachable: any string containing a multi-byte character,
  // sliced at an odd byte offset -- not just a theoretical edge case,
  // since string-processing code walks byte-by-byte, e.g. a parser's
  // `String.drop 1 s` pattern). `subslice` falls back to empty instead
  // of panicking for a bad boundary, matching this function's own
  // pre-existing out-of-range tolerance (an out-of-range `start` already
  // produced `""`, not an error).
  Ok(Value::Lit(IrLit::Str(s.subslice(start, end))))
}

fn string_drop(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "string_drop needs 2 args".into(),
    ));
  }
  let n = extract_int(&args[0])?.max(0) as usize;
  let s = extract_shared_str(&args[1])?;
  // See `string_slice`'s own comment: O(1) via `SharedStr::drop_prefix`,
  // same non-boundary/out-of-range fallback-to-empty behavior as before.
  Ok(Value::Lit(IrLit::Str(s.drop_prefix(n))))
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
    args: std::sync::Arc::new(vec![inner].into()),
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
  io_wrap(natives, Value::Lit(IrLit::Str(s.to_string().into())))
}

// --- `std/array.mo` -------------------------------------------------
//
// An `Array A` value IS a `Value::Con` tagged `Array.mk` whose `args`
// are its elements: the length is the arg count, indexing is an arg
// index, and elements need no type information because `Value` carries
// none. The compiled backend's `Constructor` (`{header, tag,
// field_count, fields[]}`, runtime.c) has exactly the same shape, which
// is what lets one set of natives serve both runtimes.
//
// **`array_set_in_place` is O(1) COMPILED and O(n) INTERPRETED**, and
// that difference is inherent rather than an implementation shortcut:
// `Value::Con`'s `args` is an `Arc<ConArgs>` shared with whatever
// environment slot or global-cache entry the builder was read out of, so
// `Arc::make_mut` copies on every write here (see `Value::Con`'s own doc
// comment in `core_value.rs` -- the aliased case is the normal one).
// `monad_set_field` on the compiled side writes the real object. Both
// are CORRECT; only the cost differs. Anything building a large array
// under the interpreter should therefore prefer `array_new` +
// `array_with` folds or go through the compiled backend.

/// `array_new (n : I64) (fill : A) : Array A`.
fn array_new(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "array_new needs 2 args".into(),
    ));
  }
  let n = extract_int(&args[0])?;
  let mk = require_ctor(natives.well_known.array_mk, "Array.mk")?;
  let len = if n < 0 { 0 } else { n as usize };
  Ok(Value::Con {
    tag: mk.tag,
    args: std::sync::Arc::new(vec![args[1].clone(); len].into()),
  })
}

/// The elements of an `Array` value, or an error naming what came
/// instead -- shared by every `array_*` native below.
fn array_elems(v: &Value) -> Result<&[Value], CoreEvalError> {
  match v {
    Value::Con { args, .. } => Ok(args.as_ref().as_ref()),
    other => Err(CoreEvalError::NativeArgError(format!(
      "expected an Array, got {other:?}"
    ))),
  }
}

/// `array_len (a : Array A) : I64` -- O(1).
fn array_len(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "array_len needs 1 arg".into(),
    ));
  }
  let elems = array_elems(&args[0])?;
  Ok(Value::Lit(IrLit::Num(elems.len() as i64, NumSuffix::I64)))
}

/// `array_get (a : Array A) (i : I64) : Option A` -- `Option`, not a
/// panic, for the same reason `String.get` returns one: an
/// out-of-range read must not be undefined behaviour in the compiled
/// backend.
fn array_get(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "array_get needs 2 args".into(),
    ));
  }
  let elems = array_elems(&args[0])?;
  let idx = extract_int(&args[1])?;
  if idx < 0 || idx as usize >= elems.len() {
    let none = require_ctor(natives.well_known.option_none, "Option.none")?;
    return Ok(Value::Con {
      tag: none.tag,
      args: std::sync::Arc::new(Vec::new().into()),
    });
  }
  let some = require_ctor(natives.well_known.option_some, "Option.some")?;
  Ok(Value::Con {
    tag: some.tag,
    args: std::sync::Arc::new(vec![elems[idx as usize].clone()].into()),
  })
}

/// `array_with (a : Array A) (i : I64) (v : A) : Array A` -- the
/// persistent `set`: copy, then write, so the input is untouched. O(n)
/// by design; bulk construction is what the builder is for.
/// An out-of-range index returns the array unchanged (the total
/// counterpart of `array_get`'s `Option.none`).
fn array_with(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 3 {
    return Err(CoreEvalError::NativeArgError(
      "array_with needs 3 args".into(),
    ));
  }
  let elems = array_elems(&args[0])?;
  let idx = extract_int(&args[1])?;
  if idx < 0 || idx as usize >= elems.len() {
    return Ok(args[0].clone());
  }
  let mk = require_ctor(natives.well_known.array_mk, "Array.mk")?;
  let mut next = elems.to_vec();
  next[idx as usize] = args[2].clone();
  Ok(Value::Con {
    tag: mk.tag,
    args: std::sync::Arc::new(next.into()),
  })
}

/// `array_set_in_place (b : ArrayBuilder A) (i : I64) (v : A) : IO Unit`.
/// See the section comment above for why this is O(n) here and O(1)
/// compiled. Returns `IO Unit`, so the mutated builder is reached
/// through the caller's own binding -- which, under the copying
/// semantics this runtime forces, is why `std/array.mo` builds through
/// `array_with` on the host path rather than relying on the write
/// being observable through an alias.
fn array_set_in_place(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 3 {
    return Err(CoreEvalError::NativeArgError(
      "array_set_in_place needs 3 args".into(),
    ));
  }
  // Validate the shape and bounds so a bad index fails the same way on
  // both runtimes rather than silently doing nothing on one.
  let elems = array_elems(&args[0])?;
  let idx = extract_int(&args[1])?;
  if idx < 0 || idx as usize >= elems.len() {
    return Err(CoreEvalError::NativeArgError(format!(
      "array_set_in_place index {idx} out of range for length {}",
      elems.len()
    )));
  }
  // `IO Unit`'s payload, spelled the way `write_file` (the other
  // `IO Unit` native) already spells it: an empty string, never
  // inspected -- `Unit` is not in `WellKnownCtors` and nothing reads
  // this value.
  io_wrap(natives, Value::Lit(IrLit::Str(String::new().into())))
}

/// `array_freeze (b : ArrayBuilder A) : IO (Array A)` -- COPIES rather
/// than casting. A cast would leave the builder aliasing a value pure
/// code believes is immutable, and a later `array_set_in_place` would
/// mutate it: the one way this design can produce a wrong answer rather
/// than a slow one.
fn array_freeze(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "array_freeze needs 1 arg".into(),
    ));
  }
  let elems = array_elems(&args[0])?;
  let mk = require_ctor(natives.well_known.array_mk, "Array.mk")?;
  io_wrap(
    natives,
    Value::Con {
      tag: mk.tag,
      args: std::sync::Arc::new(elems.to_vec().into()),
    },
  )
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
      args: std::sync::Arc::new(Vec::new().into()),
    });
  }
  let some = require_ctor(natives.well_known.option_some, "Option.some")?;
  let byte = bytes[idx as usize] as i64;
  Ok(Value::Con {
    tag: some.tag,
    args: std::sync::Arc::new(vec![Value::Lit(IrLit::Num(byte, NumSuffix::U8))].into()),
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
      args: std::sync::Arc::new(Vec::new().into()),
    });
  }
  let some = require_ctor(natives.well_known.option_some, "Option.some")?;
  Ok(Value::Con {
    tag: some.tag,
    args: std::sync::Arc::new(vec![Value::Lit(IrLit::Char(chars[idx as usize]))].into()),
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
  // The key `SharedStr` construction site for the self-hosted parser's
  // perf: the WHOLE file's content becomes one backing `Arc<str>`
  // allocation here, and every subsequent `String.slice`/`String.drop`
  // during parsing shares it (O(1) each) instead of re-copying.
  io_wrap(natives, Value::Lit(IrLit::Str(content.into())))
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
  io_wrap(natives, Value::Lit(IrLit::Str(String::new().into())))
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

/// `IO.is_dir (path : String) : IO Bool` — see `file_exists`'s own doc
/// comment; a nonexistent path is simply not-a-directory, not an error
/// (matching `file_exists`'s own `.unwrap_or(false)`-shaped tolerance
/// for a path that doesn't exist).
fn is_dir(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError("is_dir needs 1 arg".into()));
  }
  let path = extract_string(&args[0])?;
  let is_dir = std::fs::metadata(path).map(|m| m.is_dir()).unwrap_or(false);
  let result = make_bool(natives, is_dir)?;
  io_wrap(natives, result)
}

/// `IO.list_dir (path : String) : IO (List String)` — bare entry names
/// (not full paths), sorted for deterministic output, one level only.
/// Same `List.cons`/`List.empty` construction idiom as `string_to_list`
/// just below, built right-to-left over a byte string's worth of
/// entries instead of a `String`'s bytes.
fn list_dir(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError("list_dir needs 1 arg".into()));
  }
  let path = extract_string(&args[0])?;
  let mut entries: Vec<String> = std::fs::read_dir(path)
    .map_err(|e| CoreEvalError::NativeArgError(format!("list_dir {path} failed: {e}")))?
    .filter_map(|entry| entry.ok())
    .map(|entry| entry.file_name().to_string_lossy().into_owned())
    .collect();
  entries.sort();
  let cons = require_ctor(natives.well_known.list_cons, "List.cons")?;
  let empty = require_ctor(natives.well_known.list_empty, "List.empty")?;
  let mut result = Value::Con {
    tag: empty.tag,
    args: std::sync::Arc::new(Vec::new().into()),
  };
  for entry in entries.into_iter().rev() {
    result = Value::Con {
      tag: cons.tag,
      args: std::sync::Arc::new(vec![Value::Lit(IrLit::Str(entry.into())), result].into()),
    };
  }
  io_wrap(natives, result)
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
        args: std::sync::Arc::new(vec![Value::Lit(IrLit::Str(value.into()))].into()),
      }
    }
    Err(_) => {
      let none = require_ctor(natives.well_known.option_none, "Option.none")?;
      Value::Con {
        tag: none.tag,
        args: std::sync::Arc::new(Vec::new().into()),
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
    args: std::sync::Arc::new(Vec::new().into()),
  };
  for &byte in s.as_bytes().iter().rev() {
    result = Value::Con {
      tag: cons.tag,
      args: std::sync::Arc::new(
        vec![Value::Lit(IrLit::Num(byte as i64, NumSuffix::U8)), result].into(),
      ),
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
  Ok(Value::Lit(IrLit::Str(s.into())))
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

/// `IO.current_time` (std/io.mo). `IO.io`-wrapped, like every other
/// native whose declared type is `IO _`: `Monad.bind`'s `IO` instance
/// pattern-matches with `match a { io a => f a }`, so a bare number here
/// fails as "value is not a constructor" the moment anything binds it
/// with `<-`. This used to be `bench_now : I64` -- pure, unwrapped, and
/// correct for that type.
fn current_time(natives: &NativeTable) -> Result<Value, CoreEvalError> {
  let now = std::time::SystemTime::now()
    .duration_since(std::time::UNIX_EPOCH)
    .unwrap_or_default()
    .as_millis() as i64;
  io_wrap(natives, Value::Lit(IrLit::Num(now, NumSuffix::I64)))
}

fn process_id() -> Result<Value, CoreEvalError> {
  Ok(Value::Lit(IrLit::Num(
    std::process::id() as i64,
    NumSuffix::I64,
  )))
}

fn build_commit() -> Result<Value, CoreEvalError> {
  Ok(Value::Lit(IrLit::Str(
    option_env!("MONAD_BUILD_COMMIT")
      .unwrap_or("unknown")
      .into(),
  )))
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
  Value::Lit(IrLit::Str(String::new().into()))
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
        // Deliberately NOT tag 0: same rationale as the scrambled tags
        // above -- a native that hardcoded a literal instead of reading
        // `well_known` would still pass with the real numbering.
        array_mk: Some(CtorTag { tag: 9, arity: 0 }),
      },
    )
  }

  fn int(v: i64) -> Value {
    Value::Lit(IrLit::Num(v, NumSuffix::I64))
  }

  fn string(s: &str) -> Value {
    Value::Lit(IrLit::Str(s.into()))
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
  fn test_string_lt_gt_match_byte_lexicographic_order() {
    let natives = test_natives();
    assert!(matches!(
      exec_native("string_lt", &[string("abc"), string("abd")], &natives).unwrap(),
      Value::Con { tag: 7, .. }
    ));
    assert!(matches!(
      exec_native("string_lt", &[string("abd"), string("abc")], &natives).unwrap(),
      Value::Con { tag: 8, .. }
    ));
    assert!(matches!(
      exec_native("string_gt", &[string("abd"), string("abc")], &natives).unwrap(),
      Value::Con { tag: 7, .. }
    ));
    assert!(matches!(
      exec_native("string_gt", &[string("abc"), string("abc")], &natives).unwrap(),
      Value::Con { tag: 8, .. }
    ));
    // Shorter-is-less when one is a prefix of the other, matching
    // `bytes_lt`'s `empty`/`cons` case split exactly.
    assert!(matches!(
      exec_native("string_lt", &[string("ab"), string("abc")], &natives).unwrap(),
      Value::Con { tag: 7, .. }
    ));
  }

  #[test]
  fn test_string_hash_matches_djb2_seed_5381() {
    let natives = test_natives();
    // djb2 of the empty string is just the seed.
    let empty = exec_native("string_hash", &[string("")], &natives).unwrap();
    assert!(matches!(
      empty,
      Value::Lit(IrLit::Num(5381, NumSuffix::U64))
    ));
    // djb2("a") = 5381*33 + 'a' (97) = 177670.
    let a = exec_native("string_hash", &[string("a")], &natives).unwrap();
    assert!(matches!(a, Value::Lit(IrLit::Num(177_670, NumSuffix::U64))));
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
