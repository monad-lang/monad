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
  "i32_to_i64",
  "i64_to_i32",
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
  // The decimal -> bit-pattern conversion the compiler uses to lower a
  // float literal (`lang/codegen/emit.mo`). Pure: a function of its own
  // argument text, no IO and no clock, so it is foldable like the rest.
  "f64_of_string",
  "string_eq",
  "string_concat",
  "string_concat_list",
  "string_length",
  "string_count_newlines",
  "string_trailing_chars",
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
  // `Ptr.null` (init/prelude.mo): the NULL word, a constant.
  "ptr_null",
  // `ByteBuf.length` (std/bytebuf.mo): a registry lookup, no effect.
  "bytebuf_len",
];

/// Explicitly excluded (for documentation/grep-ability, not consulted by
/// `is_pure_native` — the allowlist above is authoritative): `print_str`
/// (IO), `current_time`/`current_time_nano`/`bench_report`
/// (non-deterministic timing),
/// `read_file`/`write_file`/`file_exists`/`is_dir`/`list_dir`/`get_env`/
/// `exec_cmd` (filesystem/process IO), `fork_io`/`cancel_fiber`/
/// `sleep_io`/`scope_new`/`scope_fork`/`scope_drop`/`await_fiber`
/// (concurrency/shared mutable state). Nothing here is a `tcp_*` native:
/// this evaluator deliberately implements no TCP at all, so `std/io.mo`'s
/// eight `tcp_*` defs are dispatched by the self-hosted backend alone
/// (`runtime/src/runtime.c`) and reach this table never.
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
    "i8_div" | "i16_div" | "i32_div" | "i64_div" | "u8_div" | "u16_div" => {
      int_binop(args, |a, b| if b == 0 { 0 } else { a.wrapping_div(b) })
    }
    // `U64.div`/`U64.mod` are UNSIGNED, as their names say. They used to
    // share the signed `int_binop` path, and the consequence was not a
    // rounding subtlety -- it broke every `HashMap` in the self-hosted
    // compiler.
    //
    // `String.hash` is djb2, which wraps, so ~half of all hashes have bit
    // 63 set and read back as a negative `i64`. `HashMap.bucket_of`
    // (`std/map.mo`) is `U64.mod hash 256u64`, and a signed remainder
    // takes the sign of its dividend, so those keys got a NEGATIVE bucket
    // index. `Bucket16.get`'s dispatch is `if U64.beq 0u64 idx then b0 else
    // ... else b15`, which a negative index falls straight through -- so
    // every one of them landed in the same fall-through slot.
    //
    // Measured on the compiler's own emitted module: of 3068 symbol names,
    // 1618 hash negative and 1612 collapsed into ONE bucket, against a
    // worst bucket of 23 with unsigned mod. `missing_call_targets` was
    // 45443ms of a 266178ms self-compile purely from scanning that chain.
    "u64_div" => uint_binop(args, |a, b| if b == 0 { 0 } else { a.wrapping_div(b) }),
    "u64_mod" => uint_binop(args, |a, b| if b == 0 { 0 } else { a.wrapping_rem(b) }),
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
    // `i32_to_i64` is payload identity (`mask_to_suffix(v, I64) = v`);
    // `i64_to_i32` re-interprets the low 32 bits (`v as i32 as i64`),
    // which the compiled backend emits as trunc+sext.
    "i32_to_i64" => int_to_int(args, NumSuffix::I64),
    "i64_to_i32" => int_to_int(args, NumSuffix::I32),
    "f32_to_string" | "f64_to_string" => float_to_string(args),
    // `f64_of_string` is the one F64 native with no F32 twin and no
    // `F64`-typed result: it is the decimal -> bit-pattern conversion the
    // COMPILER calls to lower a float literal (`lang/codegen/emit.mo`'s
    // `compile_lit_ir`), so its result is the i64 the emitted constant
    // has to be. See `float_of_string`'s own note on the parse.
    "f64_of_string" => float_of_string(args),
    "string_eq" => string_eq(args, natives),
    "string_lt" => string_lt(args, natives),
    "string_gt" => string_gt(args, natives),
    "string_hash" => string_hash(args),
    "string_concat" => string_concat(args),
    "string_concat_list" => string_concat_list(args, natives),
    "string_length" => string_length(args),
    "string_count_newlines" => string_count_newlines(args),
    "string_trailing_chars" => string_trailing_chars(args),
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
    "io_pure" => io_pure(args, natives),
    "current_time" => current_time(natives),
    "current_time_nano" => current_time_nano(natives),
    "bench_report" => bench_report(args, natives),
    "read_file" => read_file(args, natives),
    "write_file" => write_file(args, natives),
    "file_exists" => file_exists(args, natives),
    "is_dir" => is_dir(args, natives),
    "list_dir" => list_dir(args, natives),
    "get_env" => get_env(args, natives),
    // The raw-stdio family (`std/io.mo`). Like `current_time` above
    // (and unlike the file natives just above it), `read_line` and
    // `flush_stdout` are nullary natives -- there is no argument to
    // check, so no `NativeArgError` for one.
    "read_line" => read_line(natives),
    "read_stdin_exact" => read_stdin_exact(args, natives),
    "write_stdout" => write_stdout(args, natives),
    "flush_stdout" => flush_stdout(natives),
    "write_stderr" => write_stderr(args, natives),
    "exec_cmd" => exec_cmd(args, natives),
    // The piped-subprocess family (`std/src/process.mo`, agent-skills.md
    // Phase 4) -- IO-returning, so none of them belongs in PURE_NATIVES.
    "proc_spawn" => proc_spawn(args, natives),
    "proc_write" => proc_write(args, natives),
    "proc_read" => proc_read(args, natives),
    "proc_wait" => proc_wait(args, natives),
    // The tui mote's ONE terminal-control native (motes/tui/src/
    // terminal.mo) -- raw-mode enter/leave and TIOCGWINSZ merged behind
    // an I64 op flag, the same one-entry-point-one-flag shape
    // `proc_read`/`proc_wait` set. IO-returning, so not in
    // PURE_NATIVES.
    "term_ctl" => term_ctl(args, natives),
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
    // `Ptr.null : Ptr` (init/prelude.mo) — the NULL pointer, for C
    // functions whose callback argument is NULL (`SSL_set_verify` in
    // motes/tls is the first caller). A `Ptr` value is its raw machine
    // word under every backend, so 0 is the whole implementation.
    "ptr_null" => Ok(Value::Lit(IrLit::Num(0, NumSuffix::I64))),
    // `std/bytebuf.mo`. Registry-id handles — see `bytebuf_alloc`'s own
    // doc comment. No `bytebuf_ptr` arm (this evaluator has no raw
    // address to hand out); the four `IO`-typed ones are not in
    // `PURE_NATIVES` (like `read_file`), while `bytebuf_len` is.
    "bytebuf_alloc" => bytebuf_alloc(args, natives),
    "bytebuf_of_list" => bytebuf_of_list(args, natives),
    "bytebuf_to_list" => bytebuf_to_list(args, natives),
    "bytebuf_free" => bytebuf_free(args, natives),
    "bytebuf_to_string" => bytebuf_to_string(args, natives),
    "bytebuf_of_string" => bytebuf_of_string(args, natives),
    "bytebuf_len" => bytebuf_len(args),
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

/// `Result.ok <payload>` as a `Value`, via the well-known ctor tags.
fn make_result_ok(natives: &NativeTable, payload: Value) -> Result<Value, CoreEvalError> {
  let ok = require_ctor(natives.well_known.result_ok, "Result.ok")?;
  Ok(Value::Con {
    tag: ok.tag,
    args: std::sync::Arc::new(vec![payload].into()),
  })
}

/// `Result.err <message>` as a `Value`.
fn make_result_err(natives: &NativeTable, msg: String) -> Result<Value, CoreEvalError> {
  let err = require_ctor(natives.well_known.result_err, "Result.err")?;
  Ok(Value::Con {
    tag: err.tag,
    args: std::sync::Arc::new(vec![Value::Lit(IrLit::Str(msg.into()))].into()),
  })
}

/// `Option.some`/`Option.none` as a `Value` (`Option.some`'s fixed runtime
/// tag matches `runtime.c`'s, but the interpreter resolves it from the
/// program like every native-built ctor here).
fn make_option(natives: &NativeTable, v: Option<Value>) -> Result<Value, CoreEvalError> {
  match v {
    Some(inner) => {
      let some = require_ctor(natives.well_known.option_some, "Option.some")?;
      Ok(Value::Con {
        tag: some.tag,
        args: std::sync::Arc::new(vec![inner].into()),
      })
    }
    None => {
      let none = require_ctor(natives.well_known.option_none, "Option.none")?;
      Ok(Value::Con {
        tag: none.tag,
        args: std::sync::Arc::new(Vec::new().into()),
      })
    }
  }
}

/// `int_binop` for operations whose operands are genuinely unsigned: the
/// raw `i64` payload is reinterpreted as `u64`, the operation runs there,
/// and the result is reinterpreted back. Only the operations where signedness
/// changes the ANSWER need this -- `add`/`sub`/`mul`/`xor` are bit-identical
/// either way, and `beq` compares bit patterns, which is why the `U64`
/// variants of those can keep sharing `int_binop`.
fn uint_binop(args: &[Value], op: fn(u64, u64) -> u64) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "uint binop needs 2 args".into(),
    ));
  }
  let a = extract_int(&args[0])? as u64;
  let b = extract_int(&args[1])? as u64;
  Ok(Value::Lit(IrLit::Num(op(a, b) as i64, NumSuffix::U64)))
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

/// The decimal -> double conversion behind `F64.bits_of_string`
/// (`init/number.mo`), returned as the `I64` bit pattern the compiled
/// backend stores in an `F64` slot. `f64::from_str` is what the parser
/// already uses for a float LITERAL (`core/src/term.rs`), so a literal
/// compiled by this host and one converted by the self-hosted compiler's
/// `strtod` (`runtime/src/runtime.c`) produce the same double.
///
/// Unparsable text yields 0.0 rather than an error, matching the C side:
/// this exists so a float literal can be lowered at all, and a wrong
/// constant is a test failure while a hard error here would be a
/// compiler that cannot compile its own corpus.
fn float_of_string(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "float_of_string needs 1 arg".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  let v: f64 = s.trim().parse().unwrap_or(0.0);
  Ok(Value::Lit(IrLit::Num(v.to_bits() as i64, NumSuffix::I64)))
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

/// The byte range `string_count_newlines`/`string_trailing_chars` look
/// at: the first `len` bytes of `s`, clamped. Both take a LENGTH rather
/// than a pre-sliced string so that `resolve_ascending`
/// (`lang/parser/position.mo`) can ask about one segment per source span
/// without materialising it -- see those natives' doc comments in
/// `init/string.mo` for why a slice per span would be quadratic on the
/// compiled runtime.
fn prefix_bytes<'a>(s: &'a str, len: &Value) -> Result<&'a [u8], CoreEvalError> {
  let n = extract_int(len)?;
  let n = if n < 0 { 0 } else { n as usize };
  let bytes = s.as_bytes();
  Ok(&bytes[..n.min(bytes.len())])
}

fn string_count_newlines(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "string_count_newlines needs 2 args".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  let n = prefix_bytes(s, &args[1])?
    .iter()
    .filter(|b| **b == b'\n')
    .count();
  Ok(Value::Lit(IrLit::Num(n as i64, NumSuffix::I64)))
}

/// Characters (not bytes) after the last newline in the range, or across
/// the whole range when it has none. A character is a byte that is not a
/// UTF-8 continuation byte -- `(b & 0xC0) != 0x80`, the same 0x80-0xBF
/// range `is_utf8_continuation_byte` (`lang/parser/position.mo`) tests
/// for. `runtime/src/runtime.c`'s `monad_string_trailing_chars` must
/// agree with this byte for byte: a disagreement surfaces as the host and
/// a self-compiled binary reporting different columns.
fn string_trailing_chars(args: &[Value]) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "string_trailing_chars needs 2 args".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  let mut n: i64 = 0;
  for b in prefix_bytes(s, &args[1])? {
    if *b == b'\n' {
      n = 0;
    } else if (*b & 0xC0) != 0x80 {
      n += 1;
    }
  }
  Ok(Value::Lit(IrLit::Num(n, NumSuffix::I64)))
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
// this `io_mk`/`raw_io_io`-wrapping helper will need to change to whatever that
// type's own (non-structural) construction mechanism ends up being once
// that lands.
/// Wrap a raw value into an `IO` value: `IO.mk (RawIO.io inner)`.
/// The outer `IO.mk` is the user-facing wrapper; the inner `RawIO.io`
/// is the opaque native constructor. Both tags are resolved from
/// `NativeTable::well_known`.
fn io_wrap(natives: &NativeTable, inner: Value) -> Result<Value, CoreEvalError> {
  let raw_val = raw_io_wrap(natives, inner)?;
  let io_mk = require_ctor(natives.well_known.io_mk, "IO.mk")?;
  Ok(Value::Con {
    tag: io_mk.tag,
    args: std::sync::Arc::new(vec![raw_val].into()),
  })
}

/// Wrap a raw value into a `RawIO` value: `RawIO.io inner` -- ONE layer,
/// not the two-layer `IO.mk (RawIO.io ...)` that `io_wrap` produces. The
/// `IO.mk` wrapping is done by the `.mo` wrappers in `std/src/process.mo`
/// (`IO.mk (proc_read c 0)`), exactly the way `IO.pure` does it for
/// `RawIO.pure` -- the interpreter-side counterpart of codegen's
/// `NativeWrapKind.raw_io_passthrough`.
fn raw_io_wrap(natives: &NativeTable, inner: Value) -> Result<Value, CoreEvalError> {
  let raw_io = require_ctor(natives.well_known.raw_io_io, "RawIO.io")?;
  Ok(Value::Con {
    tag: raw_io.tag,
    args: std::sync::Arc::new(vec![inner].into()),
  })
}

/// `io_pure (a : A) : RawIO A` — the native constructor for `RawIO`
/// values. Creates a single `RawIO.io` wrapper (ONE layer), NOT the
/// two-layer `IO.mk (RawIO.io ...)` that `io_wrap` produces — the
/// `IO.mk` wrapping is done by `IO.pure` in the `.mo` source
/// (`IO.pure a := IO.mk (RawIO.pure a)`).
fn io_pure(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  let inner = args
    .first()
    .cloned()
    .ok_or_else(|| CoreEvalError::NativeArgError("io_pure needs 1 arg".into()))?;
  raw_io_wrap(natives, inner)
}

/// `io_bind (a : RawIO A) (f : A -> RawIO B) : RawIO B` — unwraps a
/// `RawIO A` value and applies `f` to the inner value. Needs the full
/// evaluator (like `await_fiber`) because applying `f` means calling
/// `core_eval::apply`. Dispatched from `fire_or_accumulate`, not
/// `exec_native`.
pub fn io_bind(
  args: &[Value],
  globals: &crate::core_value::GlobalTable,
  natives: &NativeTable,
  cache: &mut crate::core_value::GlobalCache,
) -> Result<Value, CoreEvalError> {
  let io_val = args
    .first()
    .ok_or_else(|| CoreEvalError::NativeArgError("io_bind needs 2 args".into()))?;
  let f = args
    .get(1)
    .ok_or_else(|| CoreEvalError::NativeArgError("io_bind needs 2 args".into()))?
    .clone();
  let raw_io = require_ctor(natives.well_known.raw_io_io, "RawIO.io")?;
  let inner = match io_val {
    Value::Con { tag, args } if *tag == raw_io.tag => args
      .first()
      .cloned()
      .ok_or_else(|| CoreEvalError::NativeArgError("RawIO.io constructor has no fields".into()))?,
    _ => {
      return Err(CoreEvalError::NativeArgError(format!(
        "io_bind expected a RawIO value, got {io_val:?}"
      )));
    }
  };
  crate::core_eval::apply(f, inner, globals, natives, cache)
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
    return make_option(natives, None);
  }
  make_option(natives, Some(elems[idx as usize].clone()))
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
    return make_option(natives, None);
  }
  let byte = bytes[idx as usize] as i64;
  make_option(natives, Some(Value::Lit(IrLit::Num(byte, NumSuffix::U8))))
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
    return make_option(natives, None);
  }
  make_option(natives, Some(Value::Lit(IrLit::Char(chars[idx as usize]))))
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
    Ok(value) => make_option(natives, Some(Value::Lit(IrLit::Str(value.into()))))?,
    Err(_) => make_option(natives, None)?,
  };
  io_wrap(natives, opt)
}

// --- `std/io.mo`'s raw stdio family --------------------------------
//
// The byte-level half of stdio, added for the language server (`lsp`):
// a framed protocol written to stdout, logging on stderr, and a stdin
// byte stream whose frames can be split across reads. See that group's
// own comment in `std/io.mo` for the contract each of these implements;
// `runtime/src/runtime.c` holds the compiled backend's matching half.

/// Bytes a previous `read_stdin_exact` call read but could not hand
/// over, because they are the start of a multi-byte UTF-8 character
/// whose remaining bytes had not arrived yet.
///
/// This exists because Monad's `String` here is an `Arc<str>` and MUST
/// be valid UTF-8, while `read_stdin_exact`'s caller treats the result
/// as an UNINTERPRETED BYTE STREAM and slices it at byte offsets it
/// takes from an LSP `Content-Length` header. Converting a chunk that
/// ends mid-character lossily (`from_utf8_lossy`) would replace that
/// character with U+FFFD, which is a DIFFERENT LENGTH in bytes -- and
/// every offset the caller computes afterwards would be shifted by the
/// difference. So the incomplete tail is held here and prepended to the
/// next read instead; the caller never sees it until it is a whole
/// character.
///
/// A process-wide `Mutex`, not a thread-local: stdin is process-wide
/// state, and two threads each holding a *half* of a character would
/// both hand over a corrupt stream.
static STDIN_CARRY: std::sync::Mutex<Vec<u8>> = std::sync::Mutex::new(Vec::new());

/// One UNBUFFERED `read(2)` from `fd`, retrying `EINTR`; `0` means EOF.
///
/// Every stdin reader here goes through this rather than
/// `std::io::stdin()`, matching `runtime.c`, whose readers all use
/// `read(0, ...)`. Rust's `Stdin` is an 8 KiB `BufReader`: a 1-byte
/// read through it pulls in everything the OS has ready, and those
/// bytes are then invisible to anything that looks at fd 0 itself.
/// `motes/tui/src/input.mo` reads one byte and then `poll(2)`s fd 0
/// (`term_ctl` op 3) to ask whether more of an escape sequence is
/// pending -- through the buffer, `poll` said "nothing" and the rest of
/// the keystroke waited for the NEXT keypress.
fn read_fd_raw(fd: libc::c_int, buf: &mut [u8]) -> std::io::Result<usize> {
  loop {
    let n = unsafe { libc::read(fd, buf.as_mut_ptr().cast(), buf.len()) };
    if n >= 0 {
      return Ok(n as usize);
    }
    let e = std::io::Error::last_os_error();
    if e.kind() != std::io::ErrorKind::Interrupted {
      return Err(e);
    }
  }
}

/// One line off `fd`, byte at a time, WITHOUT its trailing newline;
/// `None` when nothing at all was read (EOF). Byte-at-a-time for the
/// reason `runtime.c`'s `monad_read_line` gives: anything that reads
/// ahead consumes bytes belonging to the caller's NEXT read
/// (`read_stdin_exact`, or tui's poll-then-read).
fn read_line_fd(fd: libc::c_int) -> std::io::Result<Option<Vec<u8>>> {
  let mut line = Vec::new();
  let mut saw_byte = false;
  let mut byte = [0u8; 1];
  while read_fd_raw(fd, &mut byte)? == 1 {
    saw_byte = true;
    if byte[0] == b'\n' {
      break;
    }
    line.push(byte[0]);
  }
  Ok(saw_byte.then_some(line))
}

/// One `read` from stdin; `0` means EOF. Split out so both of
/// `read_stdin_exact`'s read sites (the fill loop and the
/// complete-the-character loop) share one error shape.
fn read_stdin_chunk(buf: &mut [u8]) -> Result<usize, CoreEvalError> {
  read_fd_raw(libc::STDIN_FILENO, buf)
    .map_err(|e| CoreEvalError::NativeArgError(format!("read_stdin_exact failed: {e}")))
}

/// `IO.read_line : IO (Option String)` — one line from stdin WITHOUT
/// its trailing newline, or `Option.none` at EOF (nothing read at all).
///
/// Reads raw bytes (`read_line_fd`) rather than `BufRead::read_line`:
/// the latter REJECTS invalid UTF-8, and this is a protocol reader
/// whose only job is to hand back what the peer sent. A final line with
/// no trailing newline is `Option.some line`, and `\r` is deliberately
/// NOT stripped.
///
/// No `STDIN_CARRY` handling is needed here, unlike `read_stdin_exact`
/// just below: `\n` is ASCII, so it is always a character boundary, and
/// the line ends either at that boundary or at EOF -- never on a lone
/// prefix of a multi-byte character with more of it still to come.
fn read_line(natives: &NativeTable) -> Result<Value, CoreEvalError> {
  let line = read_line_fd(libc::STDIN_FILENO)
    .map_err(|e| CoreEvalError::NativeArgError(format!("read_line failed: {e}")))?;
  let opt = match line {
    None => make_option(natives, None)?,
    Some(buf) => {
      let line = String::from_utf8_lossy(&buf).into_owned();
      make_option(natives, Some(Value::Lit(IrLit::Str(line.into()))))?
    }
  };
  io_wrap(natives, opt)
}

/// `IO.read_stdin_exact (n : I64) : IO String` — blocking read of UP TO
/// `n` bytes from stdin; the result being SHORTER than `n` (including
/// `""`) means EOF, and `n <= 0` returns `""`.
///
/// Two rules here are load-bearing and a future reader will otherwise
/// "simplify" this into a lossy conversion -- see `STDIN_CARRY`'s own
/// doc comment for why they exist:
///
///   1. Never return `""` while not at EOF. An empty result means
///      end-of-stream to the caller's framing reader, which would then
///      abandon the rest of the message. This matters most for `n = 1`
///      (a byte-at-a-time reader), where the first byte of a multi-byte
///      character would otherwise be all we have to show.
///   2. Return the largest VALID UTF-8 PREFIX of what we hold, carrying
///      any incomplete trailing bytes over to the next call rather than
///      converting them. Only at EOF may a trailing incomplete sequence
///      be flushed with `from_utf8_lossy` (there is no next call to
///      complete it, and the caller's byte offsets are already past it).
///
/// Filling to `n` bytes before looking at UTF-8 is what makes "shorter
/// than `n`" a reliable EOF signal rather than "the OS happened to
/// return less than a pipe buffer this time".
fn read_stdin_exact(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "read_stdin_exact needs 1 arg".into(),
    ));
  }
  let n = extract_int(&args[0])?;
  if n <= 0 {
    return io_wrap(natives, Value::Lit(IrLit::Str(String::new().into())));
  }
  let n = n as usize;
  let mut carry = match STDIN_CARRY.lock() {
    Ok(guard) => guard,
    // A panic in an unrelated native would otherwise turn every later
    // read into a hard error; the carried bytes are still the right
    // ones, so take them.
    Err(poisoned) => poisoned.into_inner(),
  };
  let mut buf: Vec<u8> = std::mem::take(&mut *carry);
  let mut chunk = vec![0u8; n];
  let mut eof = false;
  // Fill to `n` (or EOF) first.
  while buf.len() < n && !eof {
    let got = read_stdin_chunk(&mut chunk[..n - buf.len()])?;
    if got == 0 {
      eof = true;
    } else {
      buf.extend_from_slice(&chunk[..got]);
    }
  }
  let result = loop {
    match std::str::from_utf8(&buf) {
      Ok(s) => {
        let out = s.to_string();
        buf.clear();
        break out;
      }
      Err(e) => {
        let valid = e.valid_up_to();
        if valid > 0 {
          // A valid prefix plus a trailing (possibly incomplete)
          // character: hand over the prefix, carry the rest.
          let out = std::str::from_utf8(&buf[..valid])
            .expect("valid_up_to is a UTF-8 boundary")
            .to_string();
          buf.drain(..valid);
          break out;
        }
        if e.error_len().is_some() || eof {
          // Either the bytes are genuinely invalid (reading more can
          // never make them valid) or we are at EOF with a half
          // character. Nothing is left to wait for, so flush lossily --
          // still non-empty, so rule 1 above holds.
          let out = String::from_utf8_lossy(&buf).into_owned();
          buf.clear();
          break out;
        }
        // Entirely an incomplete character, and not at EOF: read on
        // rather than returning "" (rule 1).
        let got = read_stdin_chunk(&mut chunk)?;
        if got == 0 {
          eof = true;
        } else {
          buf.extend_from_slice(&chunk[..got]);
        }
      }
    }
  };
  *carry = buf;
  drop(carry);
  io_wrap(natives, Value::Lit(IrLit::Str(result.into())))
}

/// `IO.write_stdout (s : String) : IO Unit` — write `s` to stdout
/// VERBATIM: no trailing newline (the whole difference from
/// `IO.println`) and no flush (a frame's pieces are written first, then
/// `flush_stdout` once). See `write_file`'s own doc comment on why the
/// `IO.io` wrapping is required; `Unit`'s own runtime shape still
/// doesn't matter (never pattern-matched), so the empty string is the
/// inner value.
fn write_stdout(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "write_stdout needs 1 arg".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  use std::io::Write;
  let stdout = std::io::stdout();
  let mut lock = stdout.lock();
  lock
    .write_all(s.as_bytes())
    .map_err(|e| CoreEvalError::NativeArgError(format!("write_stdout failed: {e}")))?;
  io_wrap(natives, Value::Lit(IrLit::Str(String::new().into())))
}

/// `IO.flush_stdout : IO Unit` — flush stdout. Nullary (like
/// `current_time`), so no argument check.
fn flush_stdout(natives: &NativeTable) -> Result<Value, CoreEvalError> {
  use std::io::Write;
  let stdout = std::io::stdout();
  let mut lock = stdout.lock();
  lock
    .flush()
    .map_err(|e| CoreEvalError::NativeArgError(format!("flush_stdout failed: {e}")))?;
  io_wrap(natives, Value::Lit(IrLit::Str(String::new().into())))
}

/// `IO.write_stderr (s : String) : IO Unit` — write `s` to stderr
/// verbatim, no trailing newline, and FLUSH it: a log line that sits in
/// a buffer until process exit is no log line at all for a server that
/// never exits. A native of its own rather than `IO.write_stdout` plus
/// a stream argument, so a log line can never interleave into the
/// protocol stream on fd 1.
fn write_stderr(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "write_stderr needs 1 arg".into(),
    ));
  }
  let s = extract_string(&args[0])?;
  use std::io::Write;
  let stderr = std::io::stderr();
  let mut lock = stderr.lock();
  lock
    .write_all(s.as_bytes())
    .map_err(|e| CoreEvalError::NativeArgError(format!("write_stderr failed: {e}")))?;
  lock
    .flush()
    .map_err(|e| CoreEvalError::NativeArgError(format!("write_stderr failed: {e}")))?;
  io_wrap(natives, Value::Lit(IrLit::Str(String::new().into())))
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

/// `std/bytebuf.mo`'s five interpreter-backed natives. A `ByteBuf` under
/// this evaluator is a REGISTRY id (`runtime::global::register`), the
/// same opaque-handle convention `fork_io`/`scope_new` use; the compiled
/// backend instead carries a pointer to a `BufObj` (bytebuf.mo's module
/// doc is the cross-backend contract, and values never cross backends).
/// `bytebuf_ptr` deliberately has no arm — this evaluator has no raw
/// address to hand out, so forcing it reports
/// `unknown native: bytebuf_ptr`.
///
/// The recorded length is this side's `Vec` length (`bytebuf_len`),
/// which is also what `bytebuf_to_list` clamps `len` to — matching the
/// compiled `BufObj.len` clamp exactly, so the two backends read back
/// the same bytes for every argument, in-contract or not.
fn bytebuf_alloc(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  let n = match args.first() {
    Some(v) => extract_int(v)?,
    None => {
      return Err(CoreEvalError::NativeArgError(
        "bytebuf_alloc needs 1 arg".into(),
      ));
    }
  };
  let len = if n < 0 { 0 } else { n as usize };
  let id = crate::runtime::global::register(vec![0u8; len]);
  io_wrap(natives, handle_value(id))
}

fn bytebuf_of_list(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.is_empty() {
    return Err(CoreEvalError::NativeArgError(
      "bytebuf_of_list needs 1 arg".into(),
    ));
  }
  let bytes = byte_list_bytes(&args[0], natives)?;
  let id = crate::runtime::global::register(bytes);
  io_wrap(natives, handle_value(id))
}

/// Walk a `List U8` value into owned bytes — `string_from_list`'s own
/// cons/empty walk, minus the UTF-8 check a byte buffer must not have
/// (a buffer may legitimately hold any bytes; a String may not).
fn byte_list_bytes(v: &Value, natives: &NativeTable) -> Result<Vec<u8>, CoreEvalError> {
  let cons = require_ctor(natives.well_known.list_cons, "List.cons")?;
  let empty = require_ctor(natives.well_known.list_empty, "List.empty")?;
  let mut bytes = Vec::new();
  let mut cur = v;
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
  Ok(bytes)
}

fn bytebuf_to_list(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "bytebuf_to_list needs 2 args".into(),
    ));
  }
  let id = extract_handle_id(&args[0])?;
  let len = extract_int(&args[1])?;
  let bytes = crate::runtime::global::with::<Vec<u8>, _>(id, |v| v.clone()).ok_or_else(|| {
    CoreEvalError::NativeArgError(format!("bytebuf_to_list: no buffer for handle {id}"))
  })?;
  // Same clamping `string_to_list` does for its byte source: a
  // non-positive length is an empty list, never an error. The `min` is
  // the recorded-length clamp the compiled `BufObj` also applies.
  let take = if len <= 0 {
    0
  } else {
    (len as usize).min(bytes.len())
  };
  let cons = require_ctor(natives.well_known.list_cons, "List.cons")?;
  let empty = require_ctor(natives.well_known.list_empty, "List.empty")?;
  let mut result = Value::Con {
    tag: empty.tag,
    args: std::sync::Arc::new(Vec::new().into()),
  };
  for &byte in bytes[..take].iter().rev() {
    result = Value::Con {
      tag: cons.tag,
      args: std::sync::Arc::new(
        vec![Value::Lit(IrLit::Num(byte as i64, NumSuffix::U8)), result].into(),
      ),
    };
  }
  io_wrap(natives, result)
}

/// `ByteBuf.length (b : ByteBuf) : I64` — the recorded element count.
/// Pure (no `IO`) and so in `PURE_NATIVES`; the registry entry holds the
/// bytes, so their count IS the recorded length, exactly as the compiled
/// `BufObj`'s `len` field is.
fn bytebuf_len(args: &[Value]) -> Result<Value, CoreEvalError> {
  let id = match args.first() {
    Some(v) => extract_handle_id(v)?,
    None => {
      return Err(CoreEvalError::NativeArgError(
        "bytebuf_len needs 1 arg".into(),
      ));
    }
  };
  let len = crate::runtime::global::with::<Vec<u8>, _>(id, |v| v.len()).ok_or_else(|| {
    CoreEvalError::NativeArgError(format!("bytebuf_len: no buffer for handle {id}"))
  })?;
  Ok(Value::Lit(IrLit::Num(len as i64, NumSuffix::I64)))
}

/// `bytebuf_to_string : ByteBuf -> I64 -> RawIO String` -- the first
/// `len` bytes as a `String`, clamped exactly as `bytebuf_to_list`
/// clamps. A `String` here must be UTF-8, so bytes that are not come
/// back lossily (U+FFFD); the compiled backend copies them verbatim.
/// `RawIO` (one `raw_io_wrap` layer): `ByteBuf.to_string` adds `IO.mk`.
fn bytebuf_to_string(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "bytebuf_to_string needs 2 args".into(),
    ));
  }
  let id = extract_handle_id(&args[0])?;
  let len = extract_int(&args[1])?;
  let text = crate::runtime::global::with::<Vec<u8>, _>(id, |v| {
    let take = if len <= 0 {
      0
    } else {
      (len as usize).min(v.len())
    };
    String::from_utf8_lossy(&v[..take]).into_owned()
  })
  .ok_or_else(|| {
    CoreEvalError::NativeArgError(format!("bytebuf_to_string: no buffer for handle {id}"))
  })?;
  raw_io_wrap(natives, Value::Lit(IrLit::Str(text.into())))
}

/// `bytebuf_of_string : String -> RawIO ByteBuf` -- a fresh registry
/// buffer holding the string's bytes.
fn bytebuf_of_string(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  let s = match args.first() {
    Some(v) => extract_string(v)?,
    None => {
      return Err(CoreEvalError::NativeArgError(
        "bytebuf_of_string needs 1 arg".into(),
      ));
    }
  };
  let id = crate::runtime::global::register(s.as_bytes().to_vec());
  raw_io_wrap(natives, handle_value(id))
}

fn bytebuf_free(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  let id = match args.first() {
    Some(v) => extract_handle_id(v)?,
    None => {
      return Err(CoreEvalError::NativeArgError(
        "bytebuf_free needs 1 arg".into(),
      ));
    }
  };
  crate::runtime::global::drop_handle(id);
  io_wrap(natives, unit_value())
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
  // The child inherits our stdout; flush first so our own pending
  // output does not land after the child's. Same reason
  // `monad_exec_cmd` (runtime/src/runtime.c) calls `fflush(NULL)`.
  {
    use std::io::Write;
    let _ = std::io::stdout().flush();
  }
  let status = std::process::Command::new(cmd)
    .args(&cmd_args)
    .status()
    .map_err(|e| CoreEvalError::NativeArgError(format!("exec_cmd \"{cmd}\" failed: {e}")))?;
  let exit_code = status.code().unwrap_or(-1) as i64;
  io_wrap(natives, Value::Lit(IrLit::Num(exit_code, NumSuffix::I64)))
}

// ── Piped subprocesses (std/src/process.mo, agent-skills.md Phase 4) ──
//
// `exec_cmd` waits and returns only an exit status; a protocol peer
// (the MCP client's stdio transport) needs to WRITE the child's stdin,
// READ its stdout/stderr line by line while it runs, and kill it. That
// requires state that outlives a single native call, so each child
// lives in a registry and the `Child` value handed to Monad is the
// 1-based slot index -- the same opaque-word trick `Socket` uses in
// the compiled backend (`runtime.c`), never a constructor. The
// compiled backend keeps its OWN registry beside `monad_exec_cmd` in
// `runtime.c`; the two agree on the surface (`std/src/process.mo`) but
// not on the handle VALUES, which are opaque and never cross a
// process boundary.
//
// The four natives here return `RawIO <payload>` -- a SINGLE
// `RawIO.io` layer via `raw_io_wrap`, not the two-layer `io_wrap` --
// and the `Proc.*` wrappers in `std/src/process.mo` build the
// user-facing `IO` type with `IO.mk`, the same split `IO.pure`/
// `RawIO.pure` already use. That keeps the payload building here and
// the naming/defaults in `.mo` source, and it is what codegen's
// `NativeWrapKind.raw_io_passthrough` emits compiled.
//
// `Mutex` because `run_tests_parallel` runs `#[test]` defs on real
// threads that all reach this one table. The lock is per native call,
// never per byte, and `proc_read` does its blocking `read_line`
// OUTSIDE the lock (it takes the `BufReader` out, reads, puts it back)
// -- holding the lock across a blocking read would deadlock every
// other test thread's proc native against a child that never writes.

/// One live child with its three pipe ends. `stdin` is `Option`
/// because `Child::wait` wants it dropped before reaping (a child
/// blocked on stdin-EOF would otherwise hang `wait`); `out`/`err` are
/// `BufReader`s so a line costs one `read` per buffer, not per byte.
struct ProcChild {
  child: std::process::Child,
  stdin: Option<std::process::ChildStdin>,
  out: Option<std::io::BufReader<std::process::ChildStdout>>,
  err: Option<std::io::BufReader<std::process::ChildStderr>>,
}

static PROC_CHILDREN: std::sync::LazyLock<std::sync::Mutex<Vec<Option<ProcChild>>>> =
  std::sync::LazyLock::new(|| std::sync::Mutex::new(Vec::new()));

fn proc_registry() -> Result<std::sync::MutexGuard<'static, Vec<Option<ProcChild>>>, CoreEvalError>
{
  PROC_CHILDREN
    .lock()
    .map_err(|_| CoreEvalError::NativeArgError("proc registry poisoned".into()))
}

/// `Proc.spawn (cmd : String) (args : List String) : RawIO (Result String
/// Child)` -- fork+exec with all three standard streams piped. stdout
/// and stderr are SEPARATE pipes (unlike `Proc.capture`'s merged
/// redirect): a protocol stream must not have a server's log lines
/// spliced into its JSON frames. Errors before the child exists are
/// `Result.err` rather than a native failure, matching the surface
/// the compiled backend's `monad_proc_spawn` returns.
fn proc_spawn(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "proc_spawn needs 2 args".into(),
    ));
  }
  let cmd = extract_string(&args[0])?;
  let cmd_args = extract_string_list(&args[1], natives)?;
  // The child inherits nothing (all three streams are pipes), so the
  // stdout-flush `exec_cmd` needs does not apply -- but flushing keeps
  // our own pending output ahead of anything the child writes to a
  // shared terminal in a non-piped context, and costs nothing.
  {
    use std::io::Write;
    let _ = std::io::stdout().flush();
  }
  let spawned = std::process::Command::new(cmd)
    .args(&cmd_args)
    .stdin(std::process::Stdio::piped())
    .stdout(std::process::Stdio::piped())
    .stderr(std::process::Stdio::piped())
    .spawn();
  let mut child = match spawned {
    Ok(c) => c,
    Err(e) => {
      return raw_io_wrap(
        natives,
        make_result_err(natives, format!("proc_spawn \"{cmd}\" failed: {e}"))?,
      );
    }
  };
  let stdin = child.stdin.take();
  let out = child.stdout.take().map(std::io::BufReader::new);
  let err = child.stderr.take().map(std::io::BufReader::new);
  let handle = {
    let mut reg = proc_registry()?;
    reg.push(Some(ProcChild {
      child,
      stdin,
      out,
      err,
    }));
    reg.len() as i64
  };
  raw_io_wrap(
    natives,
    make_result_ok(natives, Value::Lit(IrLit::Num(handle, NumSuffix::I64)))?,
  )
}

/// The slot index for a `Child` handle, or a `Result.err` message --
/// shared by every handle-taking native below.
fn proc_handle(args: &[Value], name: &'static str) -> Result<usize, CoreEvalError> {
  let h = extract_int(
    args
      .first()
      .ok_or_else(|| CoreEvalError::NativeArgError(format!("{name} needs 1 arg")))?,
  )?;
  if h < 1 {
    return Err(CoreEvalError::NativeArgError(format!(
      "{name}: not a child handle: {h}"
    )));
  }
  Ok(h as usize)
}

/// `Proc.write (c : Child) (s : String) : RawIO (Result String U64)` --
/// bytes written, or `Result.err` (a dead child's EPIPE arrives here,
/// which is the caller's signal the peer is gone).
fn proc_write(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "proc_write needs 2 args".into(),
    ));
  }
  let slot = proc_handle(args, "proc_write")?;
  let s = extract_string(&args[1])?;
  let outcome = {
    let mut reg = proc_registry()?;
    match reg.get_mut(slot - 1) {
      Some(Some(pc)) => match pc.stdin.as_mut() {
        None => Err("proc_write: child's stdin is closed".to_string()),
        Some(w) => {
          use std::io::Write;
          w.write_all(s.as_bytes())
            .and_then(|()| w.flush())
            .map_err(|e| format!("proc_write: {e}"))
        }
      },
      _ => Err("proc_write: no such child".to_string()),
    }
  };
  let value = match outcome {
    Err(msg) => make_result_err(natives, msg)?,
    Ok(()) => make_result_ok(
      natives,
      Value::Lit(IrLit::Num(s.len() as i64, NumSuffix::U64)),
    )?,
  };
  raw_io_wrap(natives, value)
}

/// One complete, newline-terminated line off `r`, or `None` at end of
/// stream. A partial line at EOF (bytes with no trailing newline) is
/// DISCARDED: JSON-RPC-over-stdio frames are newline-terminated by
/// specification, so those bytes are a truncated message, not a
/// message -- surfacing them as one would fabricate a frame the peer
/// never finished writing. Both backends agree on the answer.
///
/// A line is BOUNDED (`PROC_MAX_LINE`): a peer that withholds its
/// newline would otherwise grow the buffer without limit, and one
/// caller of `Proc.read_line` is the shell tool, whose peer is an
/// arbitrary command, not a trusted protocol server. The bound is
/// checked against the line's CONTENT (the newline does not count), a
/// line of more than a mebibyte errors, and the check runs on each
/// chunk BEFORE it is accumulated -- so a flood fails the read at the
/// bound, it does not grow to the bound first. `runtime.c`'s
/// `proc_read_line_off` carries the same number and the same message.
const PROC_MAX_LINE: usize = 1024 * 1024;

fn proc_line<R: std::io::BufRead>(r: &mut R) -> std::io::Result<Option<String>> {
  let mut buf: Vec<u8> = Vec::new();
  // `fill_buf`/`consume` rather than `read_line`: `read_line` reads
  // the WHOLE line before any caller-side check could fire, which is
  // exactly the unbounded read the bound exists to stop.
  loop {
    let available = r.fill_buf()?;
    if available.is_empty() {
      // EOF: `buf` may hold a partial line, which is discarded per the
      // contract above.
      return Ok(None);
    }
    match available.iter().position(|&b| b == b'\n') {
      Some(i) => {
        buf.extend_from_slice(&available[..=i]);
        r.consume(i + 1);
        break;
      }
      None => {
        if buf.len() + available.len() > PROC_MAX_LINE {
          return Err(std::io::Error::other("line longer than 1048576 bytes"));
        }
        buf.extend_from_slice(available);
        let n = available.len();
        r.consume(n);
      }
    }
  }
  if buf.len() - 1 > PROC_MAX_LINE {
    return Err(std::io::Error::other("line longer than 1048576 bytes"));
  }
  buf.pop(); // the '\n'
  match String::from_utf8(buf) {
    Ok(s) => Ok(Some(s)),
    // The message `BufRead::read_line` itself used for the same case.
    Err(_) => Err(std::io::Error::other("stream did not contain valid UTF-8")),
  }
}

/// `Proc.read_line`/`Proc.read_stderr_line : Child -> IO (Result String
/// (Option String))` -- `Option.none` is end of stream (or a truncated
/// final line), `Option.some line` is one line WITHOUT its trailing
/// newline but WITH any `\r` (toolkit's framing trims that -- the same
/// split of responsibilities the compiled backend uses).
///
/// The take-out, blocking-read, put-back dance shared by the stdout
/// and stderr readers. `take` pulls the stream out of the slot (so the
/// registry lock is NOT held across a blocking read -- see the
/// registry's own comment), `put` returns it; the two closures exist
/// only because `BufReader<ChildStdout>` and `BufReader<ChildStderr>`
/// are different types that no single field access could name. A panic
/// between take and put-back loses the slot, which a test crash
/// already abandons.
fn proc_read_stream<T: std::io::Read>(
  slot: usize,
  take: impl Fn(&mut ProcChild) -> Option<std::io::BufReader<T>>,
  put: impl Fn(&mut ProcChild, Option<std::io::BufReader<T>>),
) -> std::io::Result<Option<String>> {
  let mut reg = proc_registry().map_err(|e| std::io::Error::other(e.to_string()))?;
  let mut taken = match reg.get_mut(slot - 1) {
    Some(Some(pc)) => take(pc),
    _ => return Err(std::io::Error::other("no such child")),
  };
  drop(reg);
  let r = match &mut taken {
    None => Err(std::io::Error::other("stream already closed")),
    Some(reader) => proc_line(reader),
  };
  // Put the reader back whether the read succeeded OR failed. The
  // lock must not be held across the blocking read (the registry's own
  // comment), but a FAILED read is not a dead stream: the underlying
  // fd is unchanged and a later read can still make progress, so
  // dropping the reader on one error would close the stream for good.
  // (When the slot itself is gone -- a concurrent `proc_wait` took the
  // child -- the put-back finds no home, and `taken` dropping closes
  // the fd, which is what `wait` wants anyway.)
  if taken.is_some() {
    let mut reg = proc_registry().map_err(|e| std::io::Error::other(e.to_string()))?;
    if let Some(pc) = reg.get_mut(slot - 1).and_then(|o| o.as_mut()) {
      put(pc, taken);
    }
  }
  r
}

/// `Proc.read (c : Child) (stream : I64) : RawIO (Result String (Option
/// String))` -- one line of the child's chosen stream (`stream` 0 =
/// stdout, 1 = stderr), the former `read_line`/`read_stderr_line` twins
/// merged behind one flag. `Option.none` is end of stream (or a
/// truncated final line), `Option.some line` is one line WITHOUT its
/// trailing newline but WITH any `\r` (toolkit's framing trims that --
/// the same split of responsibilities the compiled backend uses). See
/// `proc_read_stream`'s own doc for why the lock is not held across
/// the blocking read.
fn proc_read(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "proc_read needs 2 args".into(),
    ));
  }
  let slot = proc_handle(args, "proc_read")?;
  let stderr = extract_int(&args[1])? != 0;
  let outcome = if stderr {
    proc_read_stream(slot, |pc| pc.err.take(), |pc, r| pc.err = r)
  } else {
    proc_read_stream(slot, |pc| pc.out.take(), |pc, r| pc.out = r)
  };
  let value = match outcome {
    Err(e) => make_result_err(natives, format!("proc_read: {e}"))?,
    Ok(opt) => make_result_ok(
      natives,
      make_option(natives, opt.map(|s| Value::Lit(IrLit::Str(s.into()))))?,
    )?,
  };
  raw_io_wrap(natives, value)
}

/// `Proc.wait (c : Child) (kill : I64) : RawIO I64` -- close the pipes,
/// reap the child, FREE the slot (the handle dies with it; a stale
/// handle may alias a later child's, so nothing may use one after
/// `wait`), and return `WEXITSTATUS`, or -1 on a signal -- `exec_cmd`'s
/// own convention. With `kill` set, SIGKILL the child first, so one
/// call is the whole "kill, then reap" teardown (the former separate
/// `proc_kill` never reaped, which left every caller hand-rolling the
/// same kill-then-wait pair). Killing an already-exited child is not
/// an error either way -- a disposer must be idempotent.
fn proc_wait(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  if args.len() < 2 {
    return Err(CoreEvalError::NativeArgError(
      "proc_wait needs 2 args".into(),
    ));
  }
  let slot = proc_handle(args, "proc_wait")?;
  let kill_first = extract_int(&args[1])? != 0;
  let taken = {
    let mut reg = proc_registry()?;
    match reg.get_mut(slot - 1) {
      Some(Some(_)) => reg.get_mut(slot - 1).and_then(|o| o.take()),
      _ => None,
    }
  };
  let code = match taken {
    None => -1,
    Some(mut pc) => {
      // Drop stdin FIRST: a child blocked on stdin-EOF would hang here.
      pc.stdin.take();
      if kill_first {
        let _ = pc.child.kill();
      }
      pc.child.wait().ok().and_then(|s| s.code()).unwrap_or(-1) as i64
    }
  };
  raw_io_wrap(natives, Value::Lit(IrLit::Num(code, NumSuffix::I64)))
}

/// The mode `term_ctl` op 0 replaced, restored by op 1. `Mutex` (not
/// `AtomicBool`-style tricks) because `run_tests_parallel` reaches this
/// one table from real threads; the lock is held for a pair of
/// `tc*` calls, never across a read.
static TERM_CTL_SAVED: std::sync::LazyLock<std::sync::Mutex<Option<libc::termios>>> =
  std::sync::LazyLock::new(|| std::sync::Mutex::new(None));

/// `term_ctl` op 0 -- cbreak on stdin: ICANON and ECHO off (keypresses
/// arrive one at a time, unechoed), ISIG and OPOST deliberately left on
/// (Ctrl-C still works; a plain "\n" still prints). 1 on success, 0 when
/// stdin is not a tty -- degrading rather than failing so a test run
/// never needs a pty.
fn term_ctl_enter_raw() -> i64 {
  unsafe {
    let mut t: libc::termios = std::mem::zeroed();
    if libc::tcgetattr(libc::STDIN_FILENO, &mut t) != 0 {
      return 0;
    }
    {
      let mut saved = TERM_CTL_SAVED.lock().unwrap();
      // First entry wins: a nested enter-leave-enter sequence must still
      // restore the ORIGINAL mode, not the intermediate one.
      if saved.is_none() {
        *saved = Some(t);
      }
    }
    t.c_lflag &= !(libc::ICANON | libc::ECHO);
    t.c_cc[libc::VMIN] = 1;
    t.c_cc[libc::VTIME] = 0;
    if libc::tcsetattr(libc::STDIN_FILENO, libc::TCSAFLUSH, &t) != 0 {
      return 0;
    }
    1
  }
}

/// `term_ctl` op 1 -- restore the saved mode, 0 when there is none (a
/// leave without an enter, or stdin not a tty at enter time).
fn term_ctl_leave_raw() -> i64 {
  let saved = TERM_CTL_SAVED.lock().unwrap().take();
  match saved {
    Some(t) => unsafe {
      if libc::tcsetattr(libc::STDIN_FILENO, libc::TCSAFLUSH, &t) == 0 {
        1
      } else {
        0
      }
    },
    None => 0,
  }
}

/// `term_ctl` op 2 -- the size of the terminal on `fd`, as
/// `rows * 65536 + cols`, or None when it has none.
fn term_ctl_size_fd(fd: i32) -> Option<i64> {
  unsafe {
    let mut ws: libc::winsize = std::mem::zeroed();
    if libc::ioctl(fd, libc::TIOCGWINSZ, &mut ws) != 0 {
      return None;
    }
    if ws.ws_row == 0 || ws.ws_col == 0 {
      return None;
    }
    Some(ws.ws_row as i64 * 65536 + ws.ws_col as i64)
  }
}

/// `term_ctl` op 2 -- the terminal size packed as `rows * 65536 + cols`.
/// stdin first, then stdout (a piped-stdin program still owns a terminal
/// its output goes to), then `COLUMNS`/`LINES`, then 24x80. Never fails.
fn term_ctl_size() -> i64 {
  if let Some(p) = term_ctl_size_fd(libc::STDIN_FILENO) {
    return p;
  }
  if let Some(p) = term_ctl_size_fd(libc::STDOUT_FILENO) {
    return p;
  }
  let cols = std::env::var("COLUMNS")
    .ok()
    .and_then(|s| s.parse::<i64>().ok());
  let rows = std::env::var("LINES")
    .ok()
    .and_then(|s| s.parse::<i64>().ok());
  if let (Some(r), Some(c)) = (rows, cols) {
    if r > 0 && c > 0 {
      return r * 65536 + c;
    }
  }
  24 * 65536 + 80
}

/// `term_ctl : I64 -> RawIO I64` (motes/tui/src/terminal.mo) -- the tui
/// mote's one terminal-control native: op 0/1 enter/leave cbreak mode on
/// stdin (1/0), op 2 the size packed as `rows * 65536 + cols`, any other
/// op -1. `RawIO`-declared, so ONE `RawIO.io` wrap via `raw_io_wrap`;
/// the `Terminal.*` wrappers build the user-facing `IO` with `IO.mk`.
fn term_ctl(args: &[Value], natives: &NativeTable) -> Result<Value, CoreEvalError> {
  let op = extract_int(
    args
      .first()
      .ok_or_else(|| CoreEvalError::NativeArgError("term_ctl needs 2 args".into()))?,
  )?;
  let arg = extract_int(
    args
      .get(1)
      .ok_or_else(|| CoreEvalError::NativeArgError("term_ctl needs 2 args".into()))?,
  )?;
  let result = match op {
    0 => term_ctl_enter_raw(),
    1 => term_ctl_leave_raw(),
    2 => term_ctl_size(),
    3 => term_ctl_poll(arg),
    _ => -1,
  };
  raw_io_wrap(natives, Value::Lit(IrLit::Num(result, NumSuffix::I64)))
}

/// `term_ctl` op 3 -- poll(2) on stdin for up to `timeout_ms`:
/// 1 readable (EOF counts as readable; the READ is what reports
/// closure), 0 timed out, -1 poll itself failed. This is the tick
/// source a TUI frame loop rides on -- there is no sleep-with-wakeup
/// primitive, so "input timed out" IS the frame clock.
fn term_ctl_poll(timeout_ms: i64) -> i64 {
  // poll(2)'s own convention: a negative timeout blocks indefinitely --
  // that is how an app opts out of ticks. The mode/size ops never see
  // this argument.
  let timeout = if timeout_ms < 0 {
    -1
  } else {
    timeout_ms.min(i32::MAX as i64) as i32
  };
  let mut fds = [libc::pollfd {
    fd: libc::STDIN_FILENO,
    events: libc::POLLIN,
    revents: 0,
  }];
  let rc = unsafe { libc::poll(fds.as_mut_ptr(), 1, timeout) };
  if rc < 0 {
    -1
  } else if rc == 0 {
    0
  } else {
    1
  }
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

/// `IO.current_time_nano` (std/io.mo) -- raw nanoseconds, `IO.io`-wrapped
/// for the same reason `current_time` above is.
///
/// Deliberately no unit conversion: the only caller is the synthesized
/// test driver (`lang/codegen/test_driver.mo`), which does all of its
/// ns/us/ms/s arithmetic in Monad so both runtimes format identically.
fn current_time_nano(natives: &NativeTable) -> Result<Value, CoreEvalError> {
  let now = std::time::SystemTime::now()
    .duration_since(std::time::UNIX_EPOCH)
    .unwrap_or_default()
    .as_nanos() as i64;
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
        // Deliberately NOT tag 0: same rationale as the scrambled tags
        // above -- a native that hardcoded a literal instead of reading
        // `well_known` would still pass with the real numbering.
        array_mk: Some(CtorTag { tag: 9, arity: 0 }),
        raw_io_io: Some(CtorTag { tag: 11, arity: 1 }),
        io_mk: Some(CtorTag { tag: 12, arity: 1 }),
        result_ok: Some(CtorTag { tag: 9, arity: 1 }),
        result_err: Some(CtorTag { tag: 10, arity: 1 }),
      },
    )
  }

  fn int(v: i64) -> Value {
    Value::Lit(IrLit::Num(v, NumSuffix::I64))
  }

  fn string(s: &str) -> Value {
    Value::Lit(IrLit::Str(s.into()))
  }

  /// The stdin readers must not read ahead: after one line or one byte,
  /// the rest must still be in the KERNEL, where `poll(2)` (tui's
  /// `term_ctl` op 3) and the next raw read can see it. A pipe stands in
  /// for fd 0.
  #[test]
  fn test_raw_fd_readers_leave_unread_bytes_pollable() {
    let mut fds = [0 as libc::c_int; 2];
    assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
    let (rd, wr) = (fds[0], fds[1]);
    let input = b"ab\n\x1b[A";
    let wrote = unsafe { libc::write(wr, input.as_ptr().cast(), input.len()) };
    assert_eq!(wrote, input.len() as isize);

    let pending = |fd: libc::c_int| {
      let mut p = [libc::pollfd {
        fd,
        events: libc::POLLIN,
        revents: 0,
      }];
      unsafe { libc::poll(p.as_mut_ptr(), 1, 0) }
    };

    assert_eq!(read_line_fd(rd).unwrap(), Some(b"ab".to_vec()));
    let mut byte = [0u8; 1];
    assert_eq!(read_fd_raw(rd, &mut byte).unwrap(), 1);
    assert_eq!(byte[0], 0x1b);
    assert_eq!(
      pending(rd),
      1,
      "the rest of the escape sequence must stay pollable"
    );

    unsafe { libc::close(wr) };
    assert_eq!(read_line_fd(rd).unwrap(), Some(b"[A".to_vec()));
    assert_eq!(read_line_fd(rd).unwrap(), None);
    unsafe { libc::close(rd) };
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
