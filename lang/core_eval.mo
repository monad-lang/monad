use lang.core_ir {CoreIr, IrLit, MatchArm}
use lang.core_value {
  CoreEvalCycle, Env, GlobalCache, GlobalDef, GlobalTable, NativeTable, Value,
  env_extend, env_get, global_cache_begin, global_cache_fail, global_cache_get,
  global_cache_new, global_cache_store, global_table_get, native_table_arity,
  native_table_name,
}
use lang.types {Identifier, ModulePath}
use std.list {length}

/// The evaluator core loop, mirroring `core/src/core_eval.rs` (Rust).
///
/// The payoff of `lang/core_ir.mo` + `lang/core_value.mo`: reduces
/// `CoreIr` to `Value` via environment-extending closures, not
/// substitution. `app` evaluates its function to a `v_closure` and its
/// argument to a `Value` (strict call-by-value, matching
/// `core/src/eval.rs::eval_app`'s real semantics), then *extends* the
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

type CoreEvalError {
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
def eval
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
      eval body (env_extend closure_env a) globals natives cache,
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

#[partial]
def force_global_def
    (idx : I64) (gd : GlobalDef) (globals : GlobalTable) (natives : NativeTable)
    (cache : GlobalCache)
    : Pair (Result CoreEvalError Value) GlobalCache :=
  match gd {
    GlobalDef.gd_constructor tag arity => eval_ok (Value.v_con tag List.empty) cache,
    GlobalDef.gd_native native_id arity => eval_ok (Value.v_partial_ntv native_id List.empty) cache,
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

// ─── A small, fixed native table (not a ported core_native.rs) ─────────
// See this file's own doc comment: executing a native op just calls
// through to Monad's own stdlib function of the same meaning. This
// covers only what's needed to run real recursive test programs.

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

def i64_value (n : I64) : Value := Value.v_lit (IrLit.ir_num n NumSuffix.i64)

def str_value (s : String) : Value := Value.v_lit (IrLit.ir_str s)

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

def exec_native (name : Identifier) (args : List Value) : Result CoreEvalError Value :=
  match name {
    Identifier.id s => exec_native_by_name s args,
  }

def exec_native_by_name (s : String) (args : List Value) : Result CoreEvalError Value :=
  if String.beq s "i64_add" then native_i64_binop I64.add args
  else if String.beq s "i64_sub" then native_i64_binop I64.sub args
  else if String.beq s "i64_mul" then native_i64_binop I64.mul args
  else if String.beq s "i64_eq" then native_i64_bool_binop I64.beq args
  else if String.beq s "i64_lt" then native_i64_bool_binop I64.lt args
  else if String.beq s "string_concat" then native_string_binop_str_result String.concat args
  else if String.beq s "string_eq" then native_string_binop_bool_result String.beq args
  else if String.beq s "string_to_lowercase" then native_string_unop_str_result String.to_lowercase args
  else Result.err (CoreEvalError.ce_native_arg_error (String.concat "unknown native: " s))

/// A fixed 8-entry native table matching `exec_native_by_name` above --
/// what `lang/lower_core_ir.mo` and this module's own tests build
/// `NativeTable`s from. The 3 string natives (ids 5/6/7) exist to
/// support self-hosted `reflect_type_info!` evaluation
/// (`lang/typecheck/meta_eval.mo`) -- `std/derive.mo`'s
/// `derive_lens_meta`/`derive_beq_meta`/etc and `lang/cli.mo`'s
/// `derive_cli_meta` transitively call exactly `String.concat`/
/// `String.beq`/`String.to_lowercase` among natives (everything else
/// they use is ordinary Monad-defined code, no native involved).
def basic_native_table : NativeTable :=
  NativeTable.native_table
    [Identifier.id "i64_add", Identifier.id "i64_sub", Identifier.id "i64_mul",
     Identifier.id "i64_eq", Identifier.id "i64_lt",
     Identifier.id "string_concat", Identifier.id "string_eq", Identifier.id "string_to_lowercase"]
    [2, 2, 2, 2, 2, 2, 2, 1]

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
  let mf : CoreIr := CoreIr.match_fail (ModulePath.mp [Identifier.id "Option"]) (Identifier.id "some") in
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
