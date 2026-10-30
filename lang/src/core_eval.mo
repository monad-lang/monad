use lib::core_ir {CoreIr, IrLit, MatchArm}
use lib::core_value {
  CoreEvalCycle, Env, GlobalCache, GlobalDef, GlobalTable, NativeTable, Value,
  env_extend, env_get, global_cache_begin, global_cache_fail, global_cache_get,
  global_cache_depth, global_cache_depth_limit, global_cache_fuel,
  global_cache_new, global_cache_new_fueled, global_cache_store,
  global_cache_with_depth, global_cache_with_fuel, global_table_get,
  global_table_len, native_table_arity, native_table_name,
}
use lang::types {Identifier, ModulePath, NumSuffix, i64}
use std::list {List.length}

/// The evaluator core loop, mirroring `rust/core/src/core_eval.rs` (Rust).
///
/// The payoff of `lang/core_ir.mo` + `lang/core_value.mo`: reduces
/// `CoreIr` to `Value` via environment-extending closures, not
/// substitution. `app` evaluates its function to a `v_closure` and its
/// argument to a `Value` (strict call-by-value, matching
/// `rust/core/src/eval.rs::eval_app`'s real semantics), then *extends* the
/// closure's captured environment by one binding and evaluates the body
/// there. Each argument is evaluated exactly once; every subsequent
/// `local` reference to it is a shared `Value` off the environment, not a
/// re-evaluation -- the concrete fix for the former `EvalTerm`
/// evaluator's call-site-environment bug documented in this project's
/// evaluator plan.
///
/// **Cache threading, not mutation.** Rust threads `cache: &mut
/// GlobalCache` through `eval`/`apply`/`force_global`. Monad has no
/// interior mutability, so every function here instead returns `Pair
/// (Result CoreEvalError Value) GlobalCache` -- the *possibly-updated*
/// cache is always returned alongside the result, success or failure,
/// mirroring `&mut`'s "the cache reflects everything done so far,
/// regardless of outcome" behavior with an explicit return value instead.
/// `eval_then` is the bind/chain combinator that threads this through a
/// sequence of sub-evaluations.
///
/// **Natives are not a ported `core_native.rs`.** Since this evaluator
/// itself runs *inside* the real Monad interpreter, executing a native op
/// just calls straight through to Monad's own stdlib function of the same
/// meaning (`I64.add`, `I64.lt`, ...) -- see `exec_native` below. Only a
/// small, fixed set is implemented (enough to run real recursive
/// programs in tests), not full parity with `core_native.rs`'s ~60 ops.

pub type CoreEvalError {
  /// A `local i` with no matching environment frame -- an internal
  /// lowering bug, not a normal runtime condition.
  ce_unbound_local (idx: I64),
  /// A `global i` past the end of `GlobalTable` -- also an internal
  /// lowering bug.
  ce_unknown_global (idx: I64),
  /// A `global` slot recorded as `gd_unresolved` (a known,
  /// already-diagnosed gap) was actually forced at runtime.
  ce_unresolved_global (path: ModulePath),
  /// Applied a `Value` that isn't a function, constructor, or native --
  /// only `v_lit` can reach this.
  ce_not_a_function (v: Value) (arg: Value),
  /// A `match_` scrutinee reduced to something other than `v_con`.
  ce_not_a_constructor (v: Value),
  /// A `match_`'s scrutinee tag has no corresponding arm -- an internal
  /// lowering bug (`match_` should have one arm per constructor of the
  /// scrutinee's inductive).
  ce_case_index_out_of_bounds (tag: I64),
  /// A matched constructor's field count didn't match its arm's declared
  /// `bind_count` -- another internal-invariant violation.
  ce_arity_mismatch (expected: I64) (got: I64),
  /// Forcing a global re-entered its own still-in-progress slot -- a
  /// genuine reference cycle.
  ce_cycle (idx: I64),
  /// A `ntv`/`v_partial_ntv` referenced a `native_id` with no entry in
  /// `NativeTable` -- an internal lowering bug.
  ce_unknown_native (id: I64),
  /// The evaluator's step budget (`eval_fueled`) ran out. Not an internal
  /// bug: the browser REPL uses it to stop a runaway program without
  /// freezing the page.
  ce_out_of_fuel,
  /// More than `max_call_depth` nested user calls, on a cache that carries
  /// that limit (only `eval_fueled` does). The wasm stack would trap a few
  /// hundred frames later, so this reports cleanly first.
  ce_recursion_too_deep,
  /// A native fired with the wrong number or shape of arguments.
  ce_native_arg_error (msg: String),
  /// A `match` with no wildcard, and no case for `ctor` either, actually
  /// produced a value of `ctor` at runtime.
  ce_non_exhaustive_match (inductive: ModulePath) (ctor: Identifier),
}

// ─── The Result-plus-threaded-cache "monad" this module runs in ────────

def eval_ok (v : Value) (cache : GlobalCache) : Pair (Result CoreEvalError Value) GlobalCache :=
  Pair.pair (Result.ok v) cache

def eval_err (e : CoreEvalError) (cache : GlobalCache) : Pair (Result CoreEvalError Value) GlobalCache :=
  Pair.pair (Result.err e) cache

def lift_result (r : Result CoreEvalError Value) (cache : GlobalCache) : Pair (Result CoreEvalError Value) GlobalCache :=
  Pair.pair r cache

/// Chain a sub-evaluation into a continuation that receives its `Value`
/// and its (possibly-updated) `GlobalCache`. On error, the cache as of
/// the failure is still threaded through (never dropped) -- `f` is
/// simply not called.
def eval_then
    (outcome : Pair (Result CoreEvalError Value) GlobalCache)
    (f : Value -> GlobalCache -> Pair (Result CoreEvalError Value) GlobalCache)
    : Pair (Result CoreEvalError Value) GlobalCache :=
  match outcome {
    Pair.pair r cache =>
      match r {
        Result.ok v => f v cache,
        Result.err e => Pair.pair (Result.err e) cache,
      },
  }

/// Evaluate a list of `CoreIr` args left-to-right, threading the cache
/// through each, then hand the fully-evaluated `List Value` (in the same
/// order) plus the final cache to `k`.
#[partial]
def eval_args
    (args : List CoreIr) (env : Env) (globals : GlobalTable) (natives : NativeTable)
    (cache : GlobalCache)
    (k : List Value -> GlobalCache -> Pair (Result CoreEvalError Value) GlobalCache)
    : Pair (Result CoreEvalError Value) GlobalCache :=
  match args {
    List.empty => k List.empty cache,
    List.cons hd rest =>
      eval_then (eval hd env globals natives cache) (fn v => fn cache1 =>
        eval_args rest env globals natives cache1 (fn vs => fn cache2 =>
          k (List.cons v vs) cache2)),
  }

/// Evaluate `ir` to a `Value` in environment `env`, against whole-program
/// `globals`/`natives`, memoizing any global references forced along the
/// way into the returned cache.
#[partial]
pub def eval
    (ir : CoreIr) (env : Env) (globals : GlobalTable) (natives : NativeTable)
    (cache : GlobalCache)
    : Pair (Result CoreEvalError Value) GlobalCache :=
  match burn_fuel cache {
    Result.err e => Pair.pair (Result.err e) cache,
    Result.ok cache1 => eval_go ir env globals natives cache1,
  }

/// Evaluate with an explicit step budget. `fuel < 0` is unlimited; any
/// other value burns one step per IR node and fails with
/// `ce_out_of_fuel` when it reaches zero. The browser REPL's engine is the
/// only finite caller; `monad eval` and the meta-evaluator use `eval`.
///
/// The budget comes with a nesting cap: a finite caller has a fixed stack
/// (the web profile's 32 MiB) that `fuel` does not bound, so the cache
/// carries `max_call_depth` as well. Plain `eval` leaves that cap off --
/// the compiler's own meta-evaluator runs well past it.
pub def eval_fueled
    (fuel : I64) (ir : CoreIr) (globals : GlobalTable) (natives : NativeTable)
    : Pair (Result CoreEvalError Value) GlobalCache :=
  eval ir Env.env_nil globals natives
    (global_cache_new_fueled (global_table_len globals) fuel max_call_depth)

/// One node of the budget. `-1` (every ordinary caller) is one compare and
/// no write; a finite budget decrements in the returned cache, which the
/// recursion already threads everywhere.
def burn_fuel (cache : GlobalCache) : Result CoreEvalError GlobalCache :=
  let fuel : I64 := global_cache_fuel cache
  in
  if I64.lt fuel 0 then Result.ok cache
  else if I64.beq fuel 0 then Result.err CoreEvalError.ce_out_of_fuel
  else Result.ok (global_cache_with_fuel cache (fuel - 1))

#[partial]
def eval_go
    (ir : CoreIr) (env : Env) (globals : GlobalTable) (natives : NativeTable)
    (cache : GlobalCache)
    : Pair (Result CoreEvalError Value) GlobalCache :=
  match ir {
    CoreIr.local idx =>
      match env_get env idx {
        Option.some v => eval_ok v cache,
        Option.none => eval_err (CoreEvalError.ce_unbound_local idx) cache,
      },
    CoreIr.global idx => force_global idx globals natives cache,
    CoreIr.lam body => eval_ok (Value.v_closure body env) cache,
    CoreIr.app fun_ arg =>
      // Strict call-by-value: both sides are fully reduced to a Value
      // before `apply` ever runs -- no unevaluated thunk is ever carried
      // forward, unlike the old `EvalTerm` evaluator's naive threaded-env
      // scheme.
      eval_then (eval fun_ env globals natives cache) (fn f => fn cache1 =>
        eval_then (eval arg env globals natives cache1) (fn a => fn cache2 =>
          apply f a globals natives cache2)),
    CoreIr.lit l => eval_ok (Value.v_lit l) cache,
    CoreIr.match_ scrutinee arms =>
      eval_then (eval scrutinee env globals natives cache) (fn v => fn cache1 =>
        dispatch v arms env globals natives cache1),
    CoreIr.match_fail inductive ctor =>
      eval_err (CoreEvalError.ce_non_exhaustive_match inductive ctor) cache,
    CoreIr.con tag arity args =>
      eval_args args env globals natives cache (fn vs => fn cache_n =>
        eval_ok (Value.v_con tag vs) cache_n),
    CoreIr.ntv native_id args =>
      eval_args args env globals natives cache (fn vs => fn cache_n =>
        fire_or_accumulate native_id vs natives cache_n),
  }

/// Apply `f` to `a`. The `v_closure` case is the direct fix for the old
/// `EvalTerm` evaluator's substitution-shaped bug: extend the closure's
/// *captured* environment by one binding and evaluate its body there,
/// rather than extending whatever environment happened to be live at the
/// call site.
#[partial]
def apply
    (f : Value) (a : Value) (globals : GlobalTable) (natives : NativeTable)
    (cache : GlobalCache)
    : Pair (Result CoreEvalError Value) GlobalCache :=
  match f {
    Value.v_closure body closure_env =>
      match enter_depth cache {
        Result.err e => eval_err e cache,
        Result.ok cache1 =>
          match eval body (env_extend closure_env a) globals natives cache1 {
            Pair.pair r cache2 => Pair.pair r (leave_depth cache2),
          },
      },
    Value.v_con tag args =>
      eval_ok (Value.v_con tag (List.append args [a])) cache,
    Value.v_partial_ntv native_id args =>
      fire_or_accumulate native_id (List.append args [a]) natives cache,
    Value.v_lit l =>
      eval_err (CoreEvalError.ce_not_a_function (Value.v_lit l) a) cache,
  }

/// Constructor-tag dispatch: index straight into `arms` by the
/// scrutinee's tag (no scan), then extend the *enclosing* environment
/// (`env` -- the one active where this `match_` node itself sits, not a
/// fresh one) with the constructor's own fields, in declaration order
/// (so the last-declared field ends up innermost/`local 0`). This
/// matters: an arm's body is not closed over just its own fields -- a
/// `local` index inside it can still count past the newly-introduced
/// field bindings to reach an outer enclosing binder.
#[partial]
def dispatch
    (scrutinee : Value) (arms : List MatchArm) (env : Env) (globals : GlobalTable)
    (natives : NativeTable) (cache : GlobalCache)
    : Pair (Result CoreEvalError Value) GlobalCache :=
  match scrutinee {
    Value.v_con tag args => dispatch_con tag args arms env globals natives cache,
    Value.v_lit _ => eval_err (CoreEvalError.ce_not_a_constructor scrutinee) cache,
    Value.v_closure _ _ => eval_err (CoreEvalError.ce_not_a_constructor scrutinee) cache,
    Value.v_partial_ntv _ _ => eval_err (CoreEvalError.ce_not_a_constructor scrutinee) cache,
  }

#[partial]
def dispatch_con
    (tag : I64) (args : List Value) (arms : List MatchArm) (env : Env)
    (globals : GlobalTable) (natives : NativeTable) (cache : GlobalCache)
    : Pair (Result CoreEvalError Value) GlobalCache :=
  match List.get tag arms {
    Option.some matched_arm => dispatch_arm matched_arm args env globals natives cache,
    Option.none => eval_err (CoreEvalError.ce_case_index_out_of_bounds tag) cache,
  }

#[partial]
def dispatch_arm
    (matched_arm : MatchArm) (args : List Value) (env : Env) (globals : GlobalTable)
    (natives : NativeTable) (cache : GlobalCache)
    : Pair (Result CoreEvalError Value) GlobalCache :=
  match matched_arm {
    MatchArm.arm bind_count body =>
      if I64.beq (List.length args) bind_count
      then eval body (extend_env_with_fields env args) globals natives cache
      else eval_err (CoreEvalError.ce_arity_mismatch bind_count (List.length args)) cache,
  }

#[partial]
def extend_env_with_fields (env : Env) (args : List Value) : Env :=
  match args {
    List.empty => env,
    List.cons hd rest => extend_env_with_fields (env_extend env hd) rest,
  }

/// The most nested user calls `eval_fueled` allows. Measured on the web
/// profile: ~120 KiB of wasm stack per user call (the self-hosted codegen
/// gives `eval` a large frame), and 32 MiB holds about 250 `sum`-shaped
/// calls. The stack trap is not catchable, so this counter stops at 200 --
/// comfortably below the measured ceiling -- and reports cleanly instead of
/// trapping. Only the browser REPL's cache carries this limit; the plain
/// `eval` entry points do not (see `eval_fueled`).
pub def max_call_depth : I64 := 200

def enter_depth (cache : GlobalCache) : Result CoreEvalError GlobalCache :=
  let d : I64 := global_cache_depth cache
  in
  let limit : I64 := global_cache_depth_limit cache
  in
  if I64.lt limit 0 then Result.ok (global_cache_with_depth cache (I64.add d 1))
  else if I64.lt limit d
  then Result.err CoreEvalError.ce_recursion_too_deep
  else Result.ok (global_cache_with_depth cache (I64.add d 1))

def leave_depth (cache : GlobalCache) : GlobalCache :=
  global_cache_with_depth cache (I64.sub (global_cache_depth cache) 1)

/// Force global slot `idx` to a `Value`, memoizing the result into the
/// returned cache -- each global's body is walked to a `Value` at most
/// once per cache lineage, ever, regardless of how many call sites
/// reference it.
#[partial]
def force_global
    (idx : I64) (globals : GlobalTable) (natives : NativeTable) (cache : GlobalCache)
    : Pair (Result CoreEvalError Value) GlobalCache :=
  match global_cache_get cache idx {
    Option.some v => eval_ok v cache,
    Option.none =>
      match global_table_get globals idx {
        Option.some gd => force_global_def idx gd globals natives cache,
        Option.none => eval_err (CoreEvalError.ce_unknown_global idx) cache,
      },
  }

/// NOTE: every `gd_def` here is memoized unconditionally, with none of
/// the effect carve-out the Rust evaluator's own `force_global` has
/// (`rust/core/src/core_eval.rs`, `GlobalDef::Effect` /
/// `Native { arity: 0 }`). That is safe ONLY because this evaluator's
/// native table is `basic_native_table` -- five I64 ops and seven String
/// ops, all pure. Nothing it can evaluate has an effect to repeat.
///
/// Adding an effectful native here would need that carve-out first.
/// Without it a zero-arity `def x : IO A` performs its effect once per
/// process and every later reference replays the cached result --
/// exactly how every `--verbose` timing in the compiler came to print
/// one frozen constant.
#[partial]
def force_global_def
    (idx : I64) (gd : GlobalDef) (globals : GlobalTable) (natives : NativeTable)
    (cache : GlobalCache)
    : Pair (Result CoreEvalError Value) GlobalCache :=
  match gd {
    GlobalDef.gd_constructor tag arity => eval_ok (Value.v_con tag List.empty) cache,
    // A 0-arity native (Ptr.null, Ptr.minus_one) is a VALUE, not a partial
    // application: forcing it must fire it. Every table native is pure, so
    // firing on each force is safe (the memoized path only covers `gd_def`).
    GlobalDef.gd_native native_id _arity => fire_or_accumulate native_id List.empty natives cache,
    GlobalDef.gd_unresolved path => eval_err (CoreEvalError.ce_unresolved_global path) cache,
    GlobalDef.gd_def body =>
      match global_cache_begin cache idx {
        Result.err cycle => force_global_cycle_error cycle cache,
        Result.ok cache1 => force_global_body idx body globals natives cache1,
      },
  }

def force_global_cycle_error (cycle : CoreEvalCycle) (cache : GlobalCache) : Pair (Result CoreEvalError Value) GlobalCache :=
  match cycle {
    CoreEvalCycle.core_eval_cycle idx => eval_err (CoreEvalError.ce_cycle idx) cache,
  }

#[partial]
def force_global_body
    (idx : I64) (body : CoreIr) (globals : GlobalTable) (natives : NativeTable)
    (cache1 : GlobalCache)
    : Pair (Result CoreEvalError Value) GlobalCache :=
  match eval body Env.env_nil globals natives cache1 {
    Pair.pair r cache2 =>
      match r {
        Result.ok v => eval_ok v (global_cache_store cache2 idx v),
        // On failure, release the in-progress marker (rather than leave
        // it stuck forever) so a later, unrelated force of the same slot
        // doesn't see a spurious cycle -- see `global_cache_fail`'s doc
        // comment in `lang/core_value.mo`.
        Result.err e => eval_err e (global_cache_fail cache2 idx),
      },
  }

/// Fire a native call once `args`'s length reaches its declared arity;
/// below that, stay a `v_partial_ntv`, exactly like an under-saturated
/// `v_con`.
def fire_or_accumulate
    (native_id : I64) (args : List Value) (natives : NativeTable) (cache : GlobalCache)
    : Pair (Result CoreEvalError Value) GlobalCache :=
  let arity : I64 := native_table_arity natives native_id in
  if I64.lt (List.length args) arity
  then eval_ok (Value.v_partial_ntv native_id args) cache
  else
    match native_table_name natives native_id {
      Option.some name => lift_result (exec_native name args) cache,
      Option.none => eval_err (CoreEvalError.ce_unknown_native native_id) cache,
    }

// ─── A small native table ─────────────────────────────────────────────
// Executing a native op calls through to Monad's own stdlib function of
// the same meaning. The reference for every semantic detail is
// `rust/core/src/core_native.rs::exec_native` (the Rust host), and where the
// compiled backend intentionally diverges the divergence is named here:
//   * i8/i16/i32/u8/u16/u64 arithmetic and comparison are UNMASKED i64
//     operations tagged `I64` (`int_binop`), exactly like the reference
//     and the compiled backend -- the reference's own note records the
//     missing-width-mask bug as a separate, unfixed change.
//   * U32 is the one width-correct family (`int_binop_width`): mask both
//     operands to 32 bits, apply, mask the result.
//   * U64 division/remainder are UNSIGNED (`uint_binop`); everything else
//     about U64 is raw i64.
//   * division by zero returns 0 for the generic families; U32 division
//     is an error (`int_div_width`).
// Floats, IO/effects (`io_pure`/`io_bind`), `Eq.rec` and raw pointers are
// deliberately absent: the first two are rejected earlier (float
// literals by lowering, IO mains by the engine's own gate), and the rest
// need representations this evaluator does not have.

def value_as_i64 (v : Value) : Option I64 :=
  match v {
    Value.v_lit l => irlit_as_i64 l,
    Value.v_closure _ _ => Option.none,
    Value.v_con _ _ => Option.none,
    Value.v_partial_ntv _ _ => Option.none,
  }

def irlit_as_i64 (l : IrLit) : Option I64 :=
  match l {
    IrLit.ir_num n _ => Option.some n,
    IrLit.ir_str _ => Option.none,
    IrLit.ir_char _ => Option.none,
    IrLit.ir_float _ _ => Option.none,
    IrLit.ir_sort _ => Option.none,
  }

def value_as_str (v : Value) : Option String :=
  match v {
    Value.v_lit l => irlit_as_str l,
    Value.v_closure _ _ => Option.none,
    Value.v_con _ _ => Option.none,
    Value.v_partial_ntv _ _ => Option.none,
  }

def irlit_as_str (l : IrLit) : Option String :=
  match l {
    IrLit.ir_str s => Option.some s,
    IrLit.ir_num _ _ => Option.none,
    IrLit.ir_char _ => Option.none,
    IrLit.ir_float _ _ => Option.none,
    IrLit.ir_sort _ => Option.none,
  }

/// `Bool { true, false }` (`init/prelude.mo`) -- `true` is declared
/// first, so tag 0; `false` is tag 1.
def bool_value (b : Bool) : Value :=
  if b then Value.v_con 0 List.empty else Value.v_con 1 List.empty

def i64_value (n : I64) : Value := Value.v_lit (IrLit.ir_num n NumSuffix.i64)

def int_value (n : I64) (suffix : NumSuffix) : Value := Value.v_lit (IrLit.ir_num n suffix)

def str_value (s : String) : Value := Value.v_lit (IrLit.ir_str s)

/// Project `x` onto `0 .. width-1` without a bitwise AND (I64 has none):
/// truncated division, then a single add when the remainder is negative.
/// `x / INT64_MIN` cases cannot overflow the product because `q * width`
/// is exactly the multiple that was subtracted.
def wrap (width : I64) (x : I64) : I64 :=
  let q : I64 := I64.div x width
  in
  let r : I64 := I64.sub x (I64.mul q width)
  in
  if I64.lt r 0 then I64.add r width else r

/// Sign-extend the low `width` bits (`(x as i8/i16/i32) as i64`).
def sign_extend (width : I64) (half : I64) (x : I64) : I64 :=
  let m : I64 := wrap width x
  in
  if I64.gt m half then I64.sub m width else m

def mask_u8 (x : I64) : I64 := wrap 256 x

def mask_u32 (x : I64) : I64 := wrap 4294967296 x

def masked_u8_value (x : I64) : Value := int_value (mask_u8 x) NumSuffix.u8

def masked_u16_value (x : I64) : Value := int_value (wrap 65536 x) NumSuffix.u16

def masked_u32_value (x : I64) : Value := int_value (mask_u32 x) NumSuffix.u32

// ─── Generic (unmasked) integer families ──────────────────────────────

def native_i64_binop (f : I64 -> I64 -> I64) (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 0"),
    List.cons a rest1 => native_i64_binop_arg2 f a rest1,
  }

def native_i64_binop_arg2 (f : I64 -> I64 -> I64) (a : Value) (rest1 : List Value) : Result CoreEvalError Value :=
  match rest1 {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 1"),
    List.cons b _ => native_i64_binop_run f a b,
  }

def native_i64_binop_run (f : I64 -> I64 -> I64) (a : Value) (b : Value) : Result CoreEvalError Value :=
  match value_as_i64 a {
    Option.some x =>
      match value_as_i64 b {
        Option.some y => Result.ok (i64_value (f x y)),
        Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
      },
    Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
  }

/// `i64`'s minimum, without writing an unrepresentable literal:
/// `(0 - MAX) - 1`.
def i64_min : I64 := I64.sub (I64.sub 0 9223372036854775807) 1

/// `int_binop`'s guarded division: 0 when the divisor is 0. The MIN / -1
/// case is guarded too: `sdiv` traps on that overflow in wasm (and is UB in
/// LLVM), while the reference's `wrapping_div` returns MIN.
def native_i64_div_binop (args : List Value) : Result CoreEvalError Value :=
  native_i64_binop
    (fn (a : I64) => fn (b : I64) =>
        if I64.beq b 0 then 0
        else if I64.beq a i64_min && I64.beq b (-1) then a
        else I64.div a b)
    args

def native_i64_bool_binop (f : I64 -> I64 -> Bool) (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 0"),
    List.cons a rest1 => native_i64_bool_binop_arg2 f a rest1,
  }

def native_i64_bool_binop_arg2 (f : I64 -> I64 -> Bool) (a : Value) (rest1 : List Value) : Result CoreEvalError Value :=
  match rest1 {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 1"),
    List.cons b _ => native_i64_bool_binop_run f a b,
  }

def native_i64_bool_binop_run (f : I64 -> I64 -> Bool) (a : Value) (b : Value) : Result CoreEvalError Value :=
  match value_as_i64 a {
    Option.some x =>
      match value_as_i64 b {
        Option.some y => Result.ok (bool_value (f x y)),
        Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
      },
    Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
  }

def native_i64_to_string (f : I64 -> String) (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 1 arg, got 0"),
    List.cons a _ =>
      match value_as_i64 a {
        Option.some x => Result.ok (str_value (f x)),
        Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
      },
  }

def native_i64_to_i64_value (suffix : NumSuffix) (f : I64 -> I64) (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 1 arg, got 0"),
    List.cons a _ =>
      match value_as_i64 a {
        Option.some x => Result.ok (int_value (f x) suffix),
        Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
      },
  }

// ─── U32: the width-correct family ─────────────────────────────────────

def native_u32_binop (f : U32 -> U32 -> U32) (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 0"),
    List.cons a rest1 =>
      match rest1 {
        List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 1"),
        List.cons b _ => native_u32_binop_run f a b,
      },
  }

def native_u32_binop_run (f : U32 -> U32 -> U32) (a : Value) (b : Value) : Result CoreEvalError Value :=
  match value_as_i64 a {
    Option.some x =>
      match value_as_i64 b {
        Option.some y =>
          Result.ok (int_value (U32.to_i64 (f (I64.to_u32 x) (I64.to_u32 y))) NumSuffix.u32),
        Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
      },
    Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
  }

def native_u32_cmp (f : U32 -> U32 -> Bool) (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 0"),
    List.cons a rest1 =>
      match rest1 {
        List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 1"),
        List.cons b _ =>
          match value_as_i64 a {
            Option.some x =>
              match value_as_i64 b {
                Option.some y => Result.ok (bool_value (f (I64.to_u32 x) (I64.to_u32 y))),
                Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
              },
            Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
          },
      },
  }

/// `int_div_width`: mask, error on a zero divisor (the one family that
/// does), mask the quotient.
def native_u32_div (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 0"),
    List.cons a rest1 =>
      match rest1 {
        List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 1"),
        List.cons b _ =>
          match value_as_i64 a {
            Option.some x =>
              match value_as_i64 b {
                Option.some y =>
                  if I64.beq (mask_u32 y) 0
                  then Result.err (CoreEvalError.ce_native_arg_error "division by zero")
                  else Result.ok (int_value (U32.to_i64 (U32.div (I64.to_u32 x) (I64.to_u32 y))) NumSuffix.u32),
                Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
              },
            Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
          },
      },
  }

// ─── U64: unsigned division/modulo, raw i64 otherwise ──────────────────

def native_u64_div (args : List Value) : Result CoreEvalError Value :=
  native_u64_div_go (fn (a : U64) => fn (b : U64) => if U64.beq b 0u64 then 0u64 else U64.div a b) args

def native_u64_mod (args : List Value) : Result CoreEvalError Value :=
  native_u64_div_go (fn (a : U64) => fn (b : U64) => if U64.beq b 0u64 then 0u64 else U64.mod a b) args

def native_u64_div_go (f : U64 -> U64 -> U64) (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 0"),
    List.cons a rest1 =>
      match rest1 {
        List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 1"),
        List.cons b _ =>
          match value_as_i64 a {
            Option.some x =>
              match value_as_i64 b {
                Option.some y =>
                  Result.ok (int_value (U64.to_i64 (f (I64.to_u64 x) (I64.to_u64 y))) NumSuffix.u64),
                Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
              },
            Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
          },
      },
  }

def native_u64_xor (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 0"),
    List.cons a rest1 =>
      match rest1 {
        List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 1"),
        List.cons b _ =>
          match value_as_i64 a {
            Option.some x =>
              match value_as_i64 b {
                Option.some y =>
                  Result.ok (int_value (U64.to_i64 (U64.xor (I64.to_u64 x) (I64.to_u64 y))) NumSuffix.i64),
                Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
              },
            Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 arg"),
          },
      },
  }

// ─── String ───────────────────────────────────────────────────────────

def native_string_binop_str_result (f : String -> String -> String) (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 0"),
    List.cons a rest1 => native_string_binop_str_result_arg2 f a rest1,
  }

def native_string_binop_str_result_arg2 (f : String -> String -> String) (a : Value) (rest1 : List Value) : Result CoreEvalError Value :=
  match rest1 {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 1"),
    List.cons b _ => native_string_binop_str_result_run f a b,
  }

def native_string_binop_str_result_run (f : String -> String -> String) (a : Value) (b : Value) : Result CoreEvalError Value :=
  match value_as_str a {
    Option.some x =>
      match value_as_str b {
        Option.some y => Result.ok (str_value (f x y)),
        Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected String arg"),
      },
    Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected String arg"),
  }

def native_string_binop_bool_result (f : String -> String -> Bool) (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 0"),
    List.cons a rest1 => native_string_binop_bool_result_arg2 f a rest1,
  }

def native_string_binop_bool_result_arg2 (f : String -> String -> Bool) (a : Value) (rest1 : List Value) : Result CoreEvalError Value :=
  match rest1 {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 1"),
    List.cons b _ => native_string_binop_bool_result_run f a b,
  }

def native_string_binop_bool_result_run (f : String -> String -> Bool) (a : Value) (b : Value) : Result CoreEvalError Value :=
  match value_as_str a {
    Option.some x =>
      match value_as_str b {
        Option.some y => Result.ok (bool_value (f x y)),
        Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected String arg"),
      },
    Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected String arg"),
  }

def native_string_unop_str_result (f : String -> String) (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 1 arg, got 0"),
    List.cons a _ =>
      match value_as_str a {
        Option.some x => Result.ok (str_value (f x)),
        Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected String arg"),
      },
  }

def native_string_length_result (args : List Value) : Result CoreEvalError Value :=
  native_string_to_i64 (fn (s : String) => String.length s) args

/// A one-String-argument native whose result is an i64.
def native_string_to_i64 (f : String -> I64) (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 1 arg, got 0"),
    List.cons a _ =>
      match value_as_str a {
        Option.some x => Result.ok (i64_value (f x)),
        Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected String arg"),
      },
  }

/// A `(String, I64)` native whose result is an i64 -- the two primitives
/// that take an explicit byte length (`String.count_newlines`,
/// `String.trailing_chars`). The length is part of the call, not
/// recomputed: the reference counts only that prefix.
def native_string_len_i64 (f : String -> I64 -> I64) (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 0"),
    List.cons s rest =>
      match rest {
        List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 1"),
        List.cons n _ =>
          match value_as_str s {
            Option.some x =>
              match value_as_i64 n {
                Option.some len => Result.ok (i64_value (f x len)),
                Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 length"),
              },
            Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected String arg"),
          },
      },
  }

def native_string_slice_result (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 3 args, got 0"),
    List.cons s rest1 =>
      match rest1 {
        List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 3 args, got 1"),
        List.cons start rest2 =>
          match rest2 {
            List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 3 args, got 2"),
            List.cons len _ => native_string_slice_run s start len,
          },
      },
  }

def native_string_slice_run (s : Value) (start : Value) (len : Value) : Result CoreEvalError Value :=
  match value_as_i64 start {
    Option.some i =>
      match value_as_i64 len {
        Option.some n =>
          match value_as_str s {
            Option.some x => Result.ok (str_value (String.slice x i n)),
            Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected String arg"),
          },
        Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 length"),
      },
    Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 start"),
  }

def native_string_drop_result (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 0"),
    List.cons n rest1 =>
      match rest1 {
        List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 1"),
        List.cons s _ => native_string_drop_run n s,
      },
  }

def native_string_drop_run (n : Value) (s : Value) : Result CoreEvalError Value :=
  match value_as_i64 n {
    Option.some i =>
      match value_as_str s {
        Option.some x => Result.ok (str_value (String.drop i x)),
        Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected String arg"),
      },
    Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 count"),
  }

/// `String -> List U8` / `List U8 -> String` bridge. The compiled natives
/// return and take real Monad values; the evaluator needs `Value`s, so
/// each side walks the other representation.
def u8_value (b : U8) : Value := Value.v_lit (IrLit.ir_num (U8.to_i64 b) NumSuffix.u8)

def list_u8_to_value (xs : List U8) : Value :=
  match xs {
    List.empty => Value.v_con 0 List.empty,
    List.cons h t =>
      Value.v_con 1 (List.cons (u8_value h) (List.cons (list_u8_to_value t) List.empty)),
  }

def native_string_to_list (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 1 arg, got 0"),
    List.cons a _ =>
      match value_as_str a {
        Option.some x => Result.ok (list_u8_to_value (String.to_list x)),
        Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected String arg"),
      },
  }

def native_string_from_list (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 1 arg, got 0"),
    List.cons a _ =>
      match value_to_list_u8 a {
        Result.err e => Result.err e,
        Result.ok bytes => Result.ok (str_value (String.from_list bytes)),
      },
  }

def byte_of_value (v : Value) : Result CoreEvalError U8 :=
  match v {
    Value.v_lit l =>
      match irlit_as_i64 l {
        Option.some n => Result.ok (U32.to_u8 (I64.to_u32 n)),
        Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected a byte"),
      },
    Value.v_con _ _ => Result.err (CoreEvalError.ce_native_arg_error "expected a byte"),
    Value.v_closure _ _ => Result.err (CoreEvalError.ce_native_arg_error "expected a byte"),
    Value.v_partial_ntv _ _ => Result.err (CoreEvalError.ce_native_arg_error "expected a byte"),
  }

def value_to_list_u8 (v : Value) : Result CoreEvalError (List U8) :=
  match v {
    Value.v_con tag args =>
      if I64.beq tag 0
      then Result.ok List.empty
      else match args {
        List.cons hd rest =>
          match byte_of_value hd {
            Result.err e => Result.err e,
            Result.ok b =>
              match rest {
                List.cons tail _ =>
                  match value_to_list_u8 tail {
                    Result.err e => Result.err e,
                    Result.ok t => Result.ok (List.cons b t),
                  },
                List.empty => Result.err (CoreEvalError.ce_native_arg_error "malformed List U8"),
              },
          },
        List.empty => Result.err (CoreEvalError.ce_native_arg_error "malformed List U8"),
      },
    Value.v_lit _ => Result.err (CoreEvalError.ce_native_arg_error "expected List U8"),
    Value.v_closure _ _ => Result.err (CoreEvalError.ce_native_arg_error "expected List U8"),
    Value.v_partial_ntv _ _ => Result.err (CoreEvalError.ce_native_arg_error "expected List U8"),
  }

def native_string_get (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 0"),
    List.cons s rest =>
      match rest {
        List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 1"),
        List.cons i _ =>
          match value_as_str s {
            Option.some x =>
              match value_as_i64 i {
                Option.some n => Result.ok (option_u8_to_value (String.get x n)),
                Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 index"),
              },
            Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected String arg"),
          },
      },
  }

def option_u8_to_value (o : Option U8) : Value :=
  match o {
    Option.some b => Value.v_con 0 (List.cons (u8_value b) List.empty),
    Option.none => Value.v_con 1 List.empty,
  }

def option_char_to_value (o : Option Char) : Value :=
  match o {
    Option.some c =>
      match c {
        Char.of_bytes bytes => Value.v_con 0 (List.cons (list_u8_to_value bytes) List.empty),
      },
    Option.none => Value.v_con 1 List.empty,
  }

def native_string_get_char (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 0"),
    List.cons s rest =>
      match rest {
        List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 2 args, got 1"),
        List.cons i _ =>
          match value_as_str s {
            Option.some x =>
              match value_as_i64 i {
                Option.some n => Result.ok (option_char_to_value (String.get_char x n)),
                Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected I64 index"),
              },
            Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected String arg"),
          },
      },
  }

def native_string_hash (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 1 arg, got 0"),
    List.cons a _ =>
      match value_as_str a {
        Option.some x => Result.ok (int_value (U64.to_i64 (String.hash x)) NumSuffix.u64),
        Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected String arg"),
      },
  }

// ─── Dispatch ─────────────────────────────────────────────────────────

def exec_native (name : Identifier) (args : List Value) : Result CoreEvalError Value :=
  match name {
    Identifier.id s => exec_native_by_name s args,
  }

def exec_native_by_name (s : String) (args : List Value) : Result CoreEvalError Value :=
  if String.beq s "i64_add" then native_i64_binop I64.add args
  else if String.beq s "i64_sub" then native_i64_binop I64.sub args
  else if String.beq s "i64_mul" then native_i64_binop I64.mul args
  else if String.beq s "i64_div" then native_i64_div_binop args
  else if String.beq s "i64_eq" then native_i64_bool_binop I64.beq args
  else if String.beq s "i64_lt" then native_i64_bool_binop I64.lt args
  else if String.beq s "i64_gt" then native_i64_bool_binop I64.gt args
  else if String.beq s "i64_to_string" then native_i64_to_string I64.to_string args
  else if String.beq s "i64_to_u64" then native_i64_to_i64_value NumSuffix.u64 (fn (x : I64) => x) args
  else if String.beq s "i64_to_u32" then native_i64_to_i64_value NumSuffix.u32 mask_u32 args
  else if String.beq s "i64_to_i32" then native_i64_to_i64_value NumSuffix.i32 (sign_extend 4294967296 2147483647) args
  // I8 / I16 / I32: unmasked i64 arithmetic, tagged I64 (see the block
  // comment). Division is guarded; the comparisons are plain i64 ones.
  else if String.beq s "i8_add" then native_i64_binop I64.add args
  else if String.beq s "i8_sub" then native_i64_binop I64.sub args
  else if String.beq s "i8_mul" then native_i64_binop I64.mul args
  else if String.beq s "i8_div" then native_i64_div_binop args
  else if String.beq s "i8_eq" then native_i64_bool_binop I64.beq args
  else if String.beq s "i8_lt" then native_i64_bool_binop I64.lt args
  else if String.beq s "i8_gt" then native_i64_bool_binop I64.gt args
  else if String.beq s "i8_to_string" then native_i64_to_string (fn (x : I64) => I64.to_string (sign_extend 256 127 x)) args
  else if String.beq s "i16_add" then native_i64_binop I64.add args
  else if String.beq s "i16_sub" then native_i64_binop I64.sub args
  else if String.beq s "i16_mul" then native_i64_binop I64.mul args
  else if String.beq s "i16_div" then native_i64_div_binop args
  else if String.beq s "i16_eq" then native_i64_bool_binop I64.beq args
  else if String.beq s "i16_lt" then native_i64_bool_binop I64.lt args
  else if String.beq s "i16_gt" then native_i64_bool_binop I64.gt args
  else if String.beq s "i16_to_string" then native_i64_to_string (fn (x : I64) => I64.to_string (sign_extend 65536 32767 x)) args
  else if String.beq s "i32_add" then native_i64_binop I64.add args
  else if String.beq s "i32_sub" then native_i64_binop I64.sub args
  else if String.beq s "i32_mul" then native_i64_binop I64.mul args
  else if String.beq s "i32_div" then native_i64_div_binop args
  else if String.beq s "i32_eq" then native_i64_bool_binop I64.beq args
  else if String.beq s "i32_lt" then native_i64_bool_binop I64.lt args
  else if String.beq s "i32_gt" then native_i64_bool_binop I64.gt args
  else if String.beq s "i32_to_string" then native_i64_to_string (fn (x : I64) => I64.to_string (sign_extend 4294967296 2147483647 x)) args
  else if String.beq s "i32_to_i64" then native_i64_to_i64_value NumSuffix.i64 (fn (x : I64) => x) args
  // U8 / U16: unmasked like the reference; to_string prints the width's
  // canonical value (that part IS width-correct, matching `as u8`).
  else if String.beq s "u8_add" then native_i64_binop I64.add args
  else if String.beq s "u8_sub" then native_i64_binop I64.sub args
  else if String.beq s "u8_mul" then native_i64_binop I64.mul args
  else if String.beq s "u8_div" then native_i64_div_binop args
  else if String.beq s "u8_eq" then native_i64_bool_binop I64.beq args
  else if String.beq s "u8_lt" then native_i64_bool_binop I64.lt args
  else if String.beq s "u8_gt" then native_i64_bool_binop I64.gt args
  else if String.beq s "u8_to_string" then native_i64_to_string (fn (x : I64) => I64.to_string (mask_u8 x)) args
  else if String.beq s "u8_to_u32" then native_i64_to_i64_value NumSuffix.u32 mask_u32 args
  else if String.beq s "u8_to_u64" then native_i64_to_i64_value NumSuffix.u64 (fn (x : I64) => x) args
  else if String.beq s "u8_to_i64" then native_i64_to_i64_value NumSuffix.i64 (fn (x : I64) => x) args
  else if String.beq s "u16_add" then native_i64_binop I64.add args
  else if String.beq s "u16_sub" then native_i64_binop I64.sub args
  else if String.beq s "u16_mul" then native_i64_binop I64.mul args
  else if String.beq s "u16_div" then native_i64_div_binop args
  else if String.beq s "u16_eq" then native_i64_bool_binop I64.beq args
  else if String.beq s "u16_lt" then native_i64_bool_binop I64.lt args
  else if String.beq s "u16_gt" then native_i64_bool_binop I64.gt args
  else if String.beq s "u16_to_string" then native_i64_to_string (fn (x : I64) => I64.to_string (wrap 65536 x)) args
  else if String.beq s "u16_to_i64" then native_i64_to_i64_value NumSuffix.i64 (fn (x : I64) => x) args
  // U32: the width-correct family.
  else if String.beq s "u32_add" then native_u32_binop U32.add args
  else if String.beq s "u32_sub" then native_u32_binop U32.sub args
  else if String.beq s "u32_mul" then native_u32_binop U32.mul args
  else if String.beq s "u32_div" then native_u32_div args
  else if String.beq s "u32_and" then native_u32_binop U32.and args
  else if String.beq s "u32_or" then native_u32_binop U32.or args
  else if String.beq s "u32_xor" then native_u32_binop U32.xor args
  else if String.beq s "u32_shl" then native_u32_binop U32.shl args
  else if String.beq s "u32_shr" then native_u32_binop U32.shr args
  else if String.beq s "u32_eq" then native_u32_cmp U32.beq args
  else if String.beq s "u32_lt" then native_u32_cmp U32.lt args
  else if String.beq s "u32_gt" then native_u32_cmp U32.gt args
  else if String.beq s "u32_to_string" then native_i64_to_string (fn (x : I64) => U32.to_string (I64.to_u32 x)) args
  else if String.beq s "u32_to_u8" then native_i64_to_i64_value NumSuffix.u8 mask_u8 args
  else if String.beq s "u32_to_i64" then native_i64_to_i64_value NumSuffix.i64 mask_u32 args
  // U64: raw i64 except the unsigned division/remainder/xor.
  else if String.beq s "u64_add" then native_i64_binop I64.add args
  else if String.beq s "u64_sub" then native_i64_binop I64.sub args
  else if String.beq s "u64_mul" then native_i64_binop I64.mul args
  else if String.beq s "u64_div" then native_u64_div args
  else if String.beq s "u64_mod" then native_u64_mod args
  else if String.beq s "u64_xor" then native_u64_xor args
  else if String.beq s "u64_eq" then native_i64_bool_binop I64.beq args
  else if String.beq s "u64_lt" then native_i64_bool_binop I64.lt args
  else if String.beq s "u64_gt" then native_i64_bool_binop I64.gt args
  else if String.beq s "u64_to_string" then native_i64_to_string (fn (x : I64) => U64.to_string (I64.to_u64 x)) args
  else if String.beq s "u64_to_i64" then native_i64_to_i64_value NumSuffix.i64 (fn (x : I64) => x) args
  // String
  else if String.beq s "string_concat" then native_string_binop_str_result String.concat args
  else if String.beq s "string_eq" then native_string_binop_bool_result String.beq args
  else if String.beq s "string_lt" then native_string_binop_bool_result String.lt args
  else if String.beq s "string_gt" then native_string_binop_bool_result String.gt args
  else if String.beq s "string_to_lowercase" then native_string_unop_str_result String.to_lowercase args
  else if String.beq s "string_length" then native_string_length_result args
  else if String.beq s "string_slice" then native_string_slice_result args
  else if String.beq s "string_drop" then native_string_drop_result args
  else if String.beq s "string_starts_with" then native_string_binop_bool_result String.starts_with args
  else if String.beq s "string_count_newlines" then native_string_len_i64 String.count_newlines args
  else if String.beq s "string_trailing_chars" then native_string_len_i64 String.trailing_chars args
  else if String.beq s "string_get" then native_string_get args
  else if String.beq s "string_get_char" then native_string_get_char args
  else if String.beq s "string_to_list" then native_string_to_list args
  else if String.beq s "string_from_list" then native_string_from_list args
  else if String.beq s "string_concat_list" then native_string_concat_list args
  else if String.beq s "string_hash" then native_string_hash args
  // Pure constants (`init/prelude.mo`). Their whole implementation is the
  // constant, so exposing them costs nothing.
  else if String.beq s "ptr_null" then Result.ok (i64_value 0)
  else if String.beq s "ptr_minus_one" then Result.ok (i64_value (-1))
  else Result.err (CoreEvalError.ce_native_arg_error (String.concat "unknown native: " s))

def native_string_concat_list (args : List Value) : Result CoreEvalError Value :=
  match args {
    List.empty => Result.err (CoreEvalError.ce_native_arg_error "expected 1 arg, got 0"),
    List.cons a _ =>
      match value_to_list_string a {
        Result.err e => Result.err e,
        Result.ok ss => Result.ok (str_value (String.concat_list ss)),
      },
  }

def value_to_list_string (v : Value) : Result CoreEvalError (List String) :=
  match v {
    Value.v_con tag args =>
      if I64.beq tag 0
      then Result.ok List.empty
      else match args {
        List.cons hd rest =>
          match value_as_str hd {
            Option.none => Result.err (CoreEvalError.ce_native_arg_error "expected List String"),
            Option.some s =>
              match rest {
                List.cons tail _ =>
                  match value_to_list_string tail {
                    Result.err e => Result.err e,
                    Result.ok t => Result.ok (List.cons s t),
                  },
                List.empty => Result.err (CoreEvalError.ce_native_arg_error "malformed List String"),
              },
          },
        List.empty => Result.err (CoreEvalError.ce_native_arg_error "malformed List String"),
      },
    Value.v_lit _ => Result.err (CoreEvalError.ce_native_arg_error "expected List String"),
    Value.v_closure _ _ => Result.err (CoreEvalError.ce_native_arg_error "expected List String"),
    Value.v_partial_ntv _ _ => Result.err (CoreEvalError.ce_native_arg_error "expected List String"),
  }

/// One `NativeSpec` per implemented native, in id order: the i-th entry's
/// position IS its native id (`Value.v_partial_ntv` / `CoreIr.ntv` carry
/// that index). `lang/lower_core_ir.mo` maps names through
/// `native_id_for_name` below, so this list is the single source of truth.
struct NativeSpec {
    name : String,
    arity : I64,
}

/// The annotated-return-type constructor: a bare `{ name := ..., arity := ... }`
/// list element has no expected type for the Rust host's struct-literal
/// desugaring (`native_specs` failed to infer), the same pitfall AGENTS.md
/// records for literals in argument/return position.
def spec (name : String) (arity : I64) : NativeSpec :=
    { name := name, arity := arity }

def native_specs : List NativeSpec := [
    spec "i64_add" 2,
    spec "i64_sub" 2,
    spec "i64_mul" 2,
    spec "i64_eq" 2,
    spec "i64_lt" 2,
    spec "string_concat" 2,
    spec "string_eq" 2,
    spec "string_to_lowercase" 1,
    spec "string_length" 1,
    spec "string_slice" 3,
    spec "string_drop" 2,
    spec "string_starts_with" 2,
    spec "i64_div" 2,
    spec "i64_gt" 2,
    spec "i64_to_string" 1,
    spec "i64_to_u64" 1,
    spec "i64_to_u32" 1,
    spec "i64_to_i32" 1,
    spec "i8_add" 2,
    spec "i8_sub" 2,
    spec "i8_mul" 2,
    spec "i8_div" 2,
    spec "i8_eq" 2,
    spec "i8_lt" 2,
    spec "i8_gt" 2,
    spec "i8_to_string" 1,
    spec "i16_add" 2,
    spec "i16_sub" 2,
    spec "i16_mul" 2,
    spec "i16_div" 2,
    spec "i16_eq" 2,
    spec "i16_lt" 2,
    spec "i16_gt" 2,
    spec "i16_to_string" 1,
    spec "i32_add" 2,
    spec "i32_sub" 2,
    spec "i32_mul" 2,
    spec "i32_div" 2,
    spec "i32_eq" 2,
    spec "i32_lt" 2,
    spec "i32_gt" 2,
    spec "i32_to_string" 1,
    spec "i32_to_i64" 1,
    spec "u8_add" 2,
    spec "u8_sub" 2,
    spec "u8_mul" 2,
    spec "u8_div" 2,
    spec "u8_eq" 2,
    spec "u8_lt" 2,
    spec "u8_gt" 2,
    spec "u8_to_string" 1,
    spec "u8_to_u32" 1,
    spec "u8_to_u64" 1,
    spec "u8_to_i64" 1,
    spec "u16_add" 2,
    spec "u16_sub" 2,
    spec "u16_mul" 2,
    spec "u16_div" 2,
    spec "u16_eq" 2,
    spec "u16_lt" 2,
    spec "u16_gt" 2,
    spec "u16_to_string" 1,
    spec "u16_to_i64" 1,
    spec "u32_add" 2,
    spec "u32_sub" 2,
    spec "u32_mul" 2,
    spec "u32_div" 2,
    spec "u32_and" 2,
    spec "u32_or" 2,
    spec "u32_xor" 2,
    spec "u32_shl" 2,
    spec "u32_shr" 2,
    spec "u32_eq" 2,
    spec "u32_lt" 2,
    spec "u32_gt" 2,
    spec "u32_to_string" 1,
    spec "u32_to_u8" 1,
    spec "u32_to_i64" 1,
    spec "u64_add" 2,
    spec "u64_sub" 2,
    spec "u64_mul" 2,
    spec "u64_div" 2,
    spec "u64_mod" 2,
    spec "u64_xor" 2,
    spec "u64_eq" 2,
    spec "u64_lt" 2,
    spec "u64_gt" 2,
    spec "u64_to_string" 1,
    spec "u64_to_i64" 1,
    spec "string_lt" 2,
    spec "string_gt" 2,
    spec "string_count_newlines" 2,
    spec "string_trailing_chars" 2,
    spec "string_get" 2,
    spec "string_get_char" 2,
    spec "string_to_list" 1,
    spec "string_from_list" 1,
    spec "string_concat_list" 1,
    spec "string_hash" 1,
    spec "ptr_null" 0,
    spec "ptr_minus_one" 0,
]

def spec_names (specs : List NativeSpec) : List Identifier :=
  match specs {
    List.empty => List.empty,
    List.cons s rest => List.cons (Identifier.id s.name) (spec_names rest),
  }

def spec_arities (specs : List NativeSpec) : List I64 :=
  match specs {
    List.empty => List.empty,
    List.cons s rest => List.cons s.arity (spec_arities rest),
  }

def spec_index (name : String) (specs : List NativeSpec) (i : I64) : Option I64 :=
  match specs {
    List.empty => Option.none,
    List.cons s rest =>
      if String.beq s.name name then Option.some i else spec_index name rest (i + 1),
  }

/// The native table every lowering/interpretation path builds. Ids are
/// positions in `native_specs`; `lang/lower_core_ir.mo` uses
/// `native_id_for_name` directly, so a new native is added in ONE place.
pub def basic_native_table : NativeTable :=
  NativeTable.native_table (spec_names native_specs) (spec_arities native_specs)

pub def native_id_for_name (name : Identifier) : Option I64 :=
  match name {
    Identifier.id s => spec_index s native_specs 0,
  }


// ─── Tests (mirror core_eval.rs's #[cfg(test)] module) ─────────────────

def empty_globals : GlobalTable := GlobalTable.global_table List.empty

def run (ir : CoreIr) : Pair (Result CoreEvalError Value) GlobalCache :=
  eval ir Env.env_nil empty_globals basic_native_table (global_cache_new 0)

def is_num (outcome : Pair (Result CoreEvalError Value) GlobalCache) (expected : I64) : Bool :=
  match outcome {
    Pair.pair r _ =>
      match r {
        Result.ok v =>
          match value_as_i64 v {
            Option.some n => I64.beq n expected,
            Option.none => false,
          },
        Result.err _ => false,
      },
  }

def is_err (outcome : Pair (Result CoreEvalError Value) GlobalCache) : Bool :=
  match outcome {
    Pair.pair r _ =>
      match r {
        Result.ok _ => false,
        Result.err _ => true,
      },
  }

def num_lit (n : I64) : CoreIr := CoreIr.lit (IrLit.ir_num n NumSuffix.i64)

def str_lit (s : String) : CoreIr := CoreIr.lit (IrLit.ir_str s)

def is_str (outcome : Pair (Result CoreEvalError Value) GlobalCache) (expected : String) : Bool :=
  match outcome {
    Pair.pair r _ =>
      match r {
        Result.ok v =>
          match value_as_str v {
            Option.some s => String.beq s expected,
            Option.none => false,
          },
        Result.err _ => false,
      },
  }

def is_con_with_tag_and_arity (v : Value) (expected_tag : I64) (expected_arity : I64) : Bool :=
  match v {
    Value.v_con tag args => I64.beq tag expected_tag && I64.beq (List.length args) expected_arity,
    Value.v_lit _ => false,
    Value.v_closure _ _ => false,
    Value.v_partial_ntv _ _ => false,
  }

def is_closure (v : Value) : Bool :=
  match v {
    Value.v_closure _ _ => true,
    Value.v_lit _ => false,
    Value.v_con _ _ => false,
    Value.v_partial_ntv _ _ => false,
  }

#[test]
def test_eval_lit : Bool := is_num (run (num_lit 7)) 7

#[test]
def test_eval_identity_application : Bool :=
  // (\x -> x) 99
  is_num (run (CoreIr.app (CoreIr.lam (CoreIr.local 0)) (num_lit 99))) 99

#[test]
def test_k_combinator_closure_captures_correct_binding : Bool :=
  // (\x -> \y -> x) 1 2 -- only correct if `lam` captures the environment
  // live when it was BUILT (here: the one where x=1 is already bound),
  // not the caller's environment. This is exactly the shape the old
  // `EvalTerm` evaluator (lang/eval.mo) gets wrong.
  let k : CoreIr := CoreIr.lam (CoreIr.lam (CoreIr.local 1)) in
  let applied : CoreIr := CoreIr.app (CoreIr.app k (num_lit 1)) (num_lit 2) in
  is_num (run applied) 1

#[test]
def test_nested_lambdas_independent_applications_do_not_interfere : Bool :=
  // Two separate partial applications of the same closure must capture
  // independent environments -- persistence, not mutation.
  let k : CoreIr := CoreIr.lam (CoreIr.lam (CoreIr.local 1)) in
  match eval k Env.env_nil empty_globals basic_native_table (global_cache_new 0) {
    Pair.pair r cache0 =>
      match r {
        Result.ok k_val =>
          match apply k_val (i64_value 10) empty_globals basic_native_table cache0 {
            Pair.pair r1 cache1 =>
              match r1 {
                Result.ok f1 =>
                  match apply k_val (i64_value 20) empty_globals basic_native_table cache1 {
                    Pair.pair r2 cache2 =>
                      match r2 {
                        Result.ok f2 =>
                          is_num (apply f1 (i64_value 999) empty_globals basic_native_table cache2) 10
                            && is_num (apply f2 (i64_value 999) empty_globals basic_native_table cache2) 20,
                        Result.err _ => false,
                      },
                  },
                Result.err _ => false,
              },
          },
        Result.err _ => false,
      },
  }

#[test]
def test_match_arm_body_can_reach_an_outer_enclosing_binding : Bool :=
  // \x -> match (con #0/2 a b) { [2 fields] => x }
  // The arm's body (`local 2`) must walk past the 2 newly-bound fields to
  // reach the outer `x` (`local 0` at the point the lambda body starts).
  let scrutinee : CoreIr := CoreIr.con 0 2 [num_lit 111, num_lit 222] in
  let matcher : CoreIr := CoreIr.match_ scrutinee [MatchArm.arm 2 (CoreIr.local 2)] in
  let outer_fn : CoreIr := CoreIr.lam matcher in
  is_num (run (CoreIr.app outer_fn (num_lit 42))) 42

#[test]
def test_con_partial_application_via_apply : Bool :=
  // A 2-arity constructor applied one argument at a time.
  match eval (CoreIr.con 0 2 List.empty) Env.env_nil empty_globals basic_native_table (global_cache_new 0) {
    Pair.pair r cache0 =>
      match r {
        Result.ok partial =>
          match apply partial (i64_value 1) empty_globals basic_native_table cache0 {
            Pair.pair r1 cache1 =>
              match r1 {
                Result.ok partial2 =>
                  match apply partial2 (i64_value 2) empty_globals basic_native_table cache1 {
                    Pair.pair r2 _ =>
                      match r2 {
                        Result.ok v => is_con_with_tag_and_arity v 0 2,
                        Result.err _ => false,
                      },
                  },
                Result.err _ => false,
              },
          },
        Result.err _ => false,
      },
  }

#[test]
def test_ntv_i64_add : Bool :=
  is_num (run (CoreIr.ntv 0 [num_lit 3, num_lit 4])) 7

#[test]
def test_ntv_i64_lt_true_branch_via_match : Bool :=
  // if (3 < 4) then 100 else 200, compiled through match_ against Bool's
  // two tags (true=0, false=1), exactly like a real `if` lowering would.
  let cond : CoreIr := CoreIr.ntv 4 [num_lit 3, num_lit 4] in // i64_lt
  let iff : CoreIr := CoreIr.match_ cond [MatchArm.arm 0 (num_lit 100), MatchArm.arm 0 (num_lit 200)] in
  is_num (run iff) 100

#[test]
def test_ntv_string_concat : Bool :=
  is_str (run (CoreIr.ntv 5 [str_lit "foo", str_lit "bar"])) "foobar"

#[test]
def test_ntv_string_eq_true : Bool :=
  // string_eq -> Bool, dispatched through match_ against Bool's two
  // tags exactly like i64_lt's own test above.
  let cond : CoreIr := CoreIr.ntv 6 [str_lit "abc", str_lit "abc"] in
  let iff : CoreIr := CoreIr.match_ cond [MatchArm.arm 0 (num_lit 1), MatchArm.arm 0 (num_lit 0)] in
  is_num (run iff) 1

#[test]
def test_ntv_string_eq_false : Bool :=
  let cond : CoreIr := CoreIr.ntv 6 [str_lit "abc", str_lit "xyz"] in
  let iff : CoreIr := CoreIr.match_ cond [MatchArm.arm 0 (num_lit 1), MatchArm.arm 0 (num_lit 0)] in
  is_num (run iff) 0

#[test]
def test_ntv_string_to_lowercase : Bool :=
  is_str (run (CoreIr.ntv 7 [str_lit "MixedCase"])) "mixedcase"

#[test]
def test_not_a_function_error : Bool :=
  is_err (run (CoreIr.app (num_lit 1) (num_lit 2)))

#[test]
def test_non_exhaustive_match_error : Bool :=
  let mf : CoreIr := CoreIr.match_fail (ModulePath.mk [Identifier.id "Option"]) (Identifier.id "some") in
  is_err (run mf)

def globals_with (defs : List GlobalDef) : GlobalTable := GlobalTable.global_table defs

#[test]
def test_global_memoization : Bool :=
  let globals : GlobalTable := globals_with [GlobalDef.gd_def (num_lit 42)] in
  match force_global 0 globals basic_native_table (global_cache_new 1) {
    Pair.pair r1 cache1 =>
      match r1 {
        Result.ok v1 =>
          match value_as_i64 v1 {
            Option.some n1 =>
              I64.beq n1 42
                // Already memoized -- a fresh force_global re-reads the
                // cache without re-walking the body.
                && is_num (force_global 0 globals basic_native_table cache1) 42,
            Option.none => false,
          },
        Result.err _ => false,
      },
  }

#[test]
def test_cycle_detection_on_unguarded_self_reference : Bool :=
  // Global 0's own body directly references global 0, with no `lam` in
  // between to defer the reference -- a genuine, unguarded cycle.
  let globals : GlobalTable := globals_with [GlobalDef.gd_def (CoreIr.global 0)] in
  is_err (force_global 0 globals basic_native_table (global_cache_new 1))

#[test]
def test_safe_recursion_behind_lam_does_not_trigger_cycle : Bool :=
  // Global 0's body is `\n -> global0 n` -- a recursive reference, but
  // guarded behind a `lam`, so simply *forcing* global 0 to a value (a
  // closure) never re-enters its own in-progress slot.
  let self_recursive_body : CoreIr := CoreIr.lam (CoreIr.app (CoreIr.global 0) (CoreIr.local 0)) in
  let globals : GlobalTable := globals_with [GlobalDef.gd_def self_recursive_body] in
  match force_global 0 globals basic_native_table (global_cache_new 1) {
    Pair.pair r _ =>
      match r {
        Result.ok v => is_closure v,
        Result.err _ => false,
      },
  }

#[test]
def test_depth_limit_is_off_for_plain_caches : Bool :=
  // Only the browser REPL's cache carries a nesting cap: its wasm stack is
  // a fixed 32 MiB, and a trap there is uncatchable. Every other entry
  // point -- `monad eval`, and the compiler's own meta-evaluator, which
  // legitimately nests past 200 frames compiling a derive-heavy type --
  // must stay uncapped. A cap here broke the weaver build in CI with
  // `ce_recursion_too_deep`.
  match enter_depth (global_cache_with_depth (global_cache_new 0) (I64.add max_call_depth 100)) {
    Result.ok cache => I64.beq (global_cache_depth cache) (I64.add max_call_depth 101),
    Result.err _ => false,
  }

#[test]
def test_depth_limit_is_enforced_for_fueled_caches : Bool :=
  // The cap `eval_fueled` installs: at `depth_limit` the call is still
  // allowed, one past it fails cleanly instead of trapping the stack.
  let cache : GlobalCache := global_cache_with_depth (global_cache_new_fueled 0 (-1) 3) 4
  in
  match enter_depth cache {
    Result.ok _ => false,
    Result.err e =>
      match e {
        CoreEvalError.ce_recursion_too_deep => true,
        _ => false,
      },
  }
