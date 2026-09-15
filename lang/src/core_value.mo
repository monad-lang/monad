use lang.core_ir {CoreIr, IrLit}
use lang.types {Identifier, ModulePath}
use std.list {length}

/// `Value`/`Env` — the runtime representation the closure-based evaluator
/// (`lang/core_eval.mo`) reduces `CoreIr` to, mirroring
/// `core/src/core_value.rs` (Rust). See that file's own doc comment for
/// the full design rationale.
///
/// This is the direct fix for the former `EvalTerm`'s
/// substitution-based design: a `lam` evaluates to a `v_closure` that
/// *captures* its environment, and applying it *extends* that
/// environment with one new binding instead of rewriting the body — there
/// is no substitution function anywhere in this file, and there never
/// needs to be one.
///
/// **No mutation.** Rust's `GlobalCache` is threaded through `eval`/
/// `apply`/`force_global` as `&mut` state. Monad has no interior
/// mutability to reach for here, so this module's `GlobalCache` is a
/// plain, persistent value: every operation that would "mutate" it
/// (`global_cache_begin`/`global_cache_store`/`global_cache_fail`)
/// instead returns a *new* `GlobalCache`, which callers in
/// `lang/core_eval.mo` thread through explicitly (functional-state-
/// passing), the same way `Env` is threaded rather than mutated.
///
/// **Match patterns in this module are always single-level** (`Ctor arg
/// => ...`, never `Ctor (Inner x) => ...`) — Monad's `match` grammar
/// doesn't parse nested constructor patterns (confirmed against
/// `core/src/parser.rs`'s `match_case_parser`, which only accepts a
/// constructor name followed by plain identifier args). Where the Rust
/// original nests a pattern, this file instead nests a `match`
/// *expression* in the arm body — the same style already used throughout
/// `lang/eval.mo`.

/// A persistent (immutable, shared-tail) cons-list environment, indexed
/// the same way `CoreIr.local`/`Term.var` are: 0 = innermost (most
/// recently bound). A plain cons-list, not a `BTreeMap`/`HashMap` —
/// deliberately: see `AGENTS.md`'s "Known Type Checker Issues" #4, which
/// measured `BTreeMap` as ~25x *slower* than `List`+linear-scan for the
/// small collection sizes typical of this self-hosted interpreter's own
/// code. An environment stack is exactly that shape.
type Env {
  env_nil,
  env_cons (v: Value) (rest: Env),
}

/// A runtime value. Distinct from `CoreIr` (the compiled syntax it's
/// reduced from) on purpose — a value here is always already in normal
/// form, never a still-to-be-reduced expression.
type Value {
  /// Scalar literals reuse `core_ir.IrLit` directly.
  v_lit (l: IrLit),
  /// What a `lam` evaluates to: the still-unevaluated body plus the
  /// environment it closes over.
  v_closure (body: CoreIr) (env: Env),
  /// A fully- or partially-applied constructor. `args`'s length is
  /// `<= arity` (arity itself lives on the `con`/`GlobalDef` node that
  /// produced this, not duplicated here); application appends to `args`
  /// left-to-right.
  v_con (tag: I64) (args: List Value),
  /// A native/builtin call with some but not all of its arguments
  /// supplied yet.
  v_partial_ntv (native_id: I64) (args: List Value),
}

def env_extend (env : Env) (v : Value) : Env := Env.env_cons v env

#[partial]
def env_get (env : Env) (idx : I64) : Option Value :=
  match env {
    Env.env_nil => Option.none,
    Env.env_cons v rest =>
      if I64.beq idx 0
      then Option.some v
      else env_get rest (idx - 1),
  }

// ─── Global table: a read-only view over a whole-program's global slots ─

/// One global slot's compiled definition — mirrors
/// `lower_core_ir::GlobalDef` (Rust); produced by `lang/lower_core_ir.mo`.
type GlobalDef {
  /// An ordinary def, instance method, or assembled instance dictionary
  /// -- has a real `CoreIr` body to evaluate (once, then memoize).
  gd_def (body: CoreIr),
  /// A constructor referenced point-free (no `CoreIr` body exists for
  /// it) -- resolves straight to a synthesized, empty `v_con`, filled
  /// left-to-right by ordinary application.
  gd_constructor (tag: I64) (arity: I64),
  /// A native-attributed def with no explicit body -- resolves straight
  /// to a synthesized, empty `v_partial_ntv`, filled left-to-right.
  gd_native (native_id: I64) (arity: I64),
  /// A def that failed to lower for a known, already-diagnosed reason --
  /// forcing this slot at evaluation time errors clearly.
  gd_unresolved (path: ModulePath),
}

type GlobalTable {
  global_table (globals: List GlobalDef),
}

def global_table_get (table : GlobalTable) (idx : I64) : Option GlobalDef :=
  match table {
    GlobalTable.global_table globals => List.get idx globals,
  }

def global_table_len (table : GlobalTable) : I64 :=
  match table {
    GlobalTable.global_table globals => List.length globals,
  }

// ─── Native table: name + arity, resolved once at lowering time ────────

type NativeTable {
  native_table (names: List Identifier) (arities: List I64),
}

def native_table_name (table : NativeTable) (id : I64) : Option Identifier :=
  match table {
    NativeTable.native_table names arities => List.get id names,
  }

/// A native's fixed arity -- `0` for an out-of-range id (an internal
/// lowering bug, same convention `global_table_get` leaves callers to
/// handle via `Option`, not a panic).
def native_table_arity (table : NativeTable) (id : I64) : I64 :=
  match table {
    NativeTable.native_table names arities =>
      Option.get_or_default 0 (List.get id arities),
  }

// ─── Global cache: memoized, cycle-checked forced global values ────────

/// One global slot's memoization state. `slot_in_progress` exists purely
/// to turn a genuine reference cycle into a clear, immediate error
/// instead of infinite recursion.
type Slot {
  slot_empty,
  slot_in_progress,
  slot_done (v: Value),
}

def slot_done_value (slot : Slot) : Option Value :=
  match slot {
    Slot.slot_done v => Option.some v,
    Slot.slot_empty => Option.none,
    Slot.slot_in_progress => Option.none,
  }

def slot_is_in_progress (slot : Slot) : Bool :=
  match slot {
    Slot.slot_in_progress => true,
    Slot.slot_empty => false,
    Slot.slot_done _ => false,
  }

/// Explicit, caller-threaded cache of forced global values -- one slot
/// per `GlobalTable` entry. Unlike the Rust original, this is not mutated
/// in place: every "mutating" operation below returns a new `GlobalCache`
/// value (see this module's doc comment).
type GlobalCache {
  global_cache (slots: List Slot),
}

/// A global slot was still `slot_in_progress` when it was referenced
/// again -- see `global_cache_begin`.
type CoreEvalCycle {
  core_eval_cycle (idx: I64),
}

#[partial]
def list_replicate (n : I64) (v : Slot) : List Slot :=
  if I64.beq n 0
  then List.empty
  else List.cons v (list_replicate (n - 1) v)

def global_cache_new (len : I64) : GlobalCache :=
  GlobalCache.global_cache (list_replicate len Slot.slot_empty)

/// Already-forced value for `idx`, if any -- never a re-evaluation.
def global_cache_get (cache : GlobalCache) (idx : I64) : Option Value :=
  match cache {
    GlobalCache.global_cache slots =>
      match List.get idx slots {
        Option.some slot => slot_done_value slot,
        Option.none => Option.none,
      },
  }

#[partial]
def list_set_nth (idx : I64) (v : Slot) (l : List Slot) : List Slot :=
  match l {
    List.empty => List.empty,
    List.cons hd rest =>
      if I64.beq idx 0
      then List.cons v rest
      else List.cons hd (list_set_nth (idx - 1) v rest),
  }

/// Mark `idx` as currently being forced -- `err` if it already was (a
/// genuine cycle: some global's own evaluation transitively depends on
/// its own not-yet-computed value). Callers (`lang/core_eval.mo`'s
/// `force_global`) call this before evaluating a slot's body and
/// `global_cache_store` after.
def global_cache_begin (cache : GlobalCache) (idx : I64) : Result CoreEvalCycle GlobalCache :=
  match cache {
    GlobalCache.global_cache slots =>
      match List.get idx slots {
        Option.some slot =>
          if slot_is_in_progress slot
          then Result.err (CoreEvalCycle.core_eval_cycle idx)
          else Result.ok (GlobalCache.global_cache (list_set_nth idx Slot.slot_in_progress slots)),
        Option.none =>
          Result.ok (GlobalCache.global_cache (list_set_nth idx Slot.slot_in_progress slots)),
      },
  }

def global_cache_store (cache : GlobalCache) (idx : I64) (value : Value) : GlobalCache :=
  match cache {
    GlobalCache.global_cache slots =>
      GlobalCache.global_cache (list_set_nth idx (Slot.slot_done value) slots),
  }

/// Release `idx`'s in-progress marker back to empty after its evaluation
/// failed -- called on every error path in `force_global`. Without this,
/// a slot that fails once stays `slot_in_progress` forever, so any later,
/// unrelated attempt to force the same slot sees a spurious cycle instead
/// of the real, deterministic error. See `core_value.rs`'s
/// `GlobalCache::fail` doc comment -- a real, previously-hit bug class.
def global_cache_fail (cache : GlobalCache) (idx : I64) : GlobalCache :=
  match cache {
    GlobalCache.global_cache slots =>
      GlobalCache.global_cache (list_set_nth idx Slot.slot_empty slots),
  }

// ─── Tests (mirror core_value.rs's #[cfg(test)] module) ────────────────

def test_lit (v : I64) : Value := Value.v_lit (IrLit.ir_num v NumSuffix.i64)

/// Test helper: single-level accessors chained via nested `match`
/// expressions (never nested patterns) to pull an `I64` out of an
/// `Option Value` known to wrap `v_lit (ir_num n _)`.
def value_as_num (v : Value) : Option I64 :=
  match v {
    Value.v_lit l => irlit_as_num l,
    Value.v_closure _ _ => Option.none,
    Value.v_con _ _ => Option.none,
    Value.v_partial_ntv _ _ => Option.none,
  }

def irlit_as_num (l : IrLit) : Option I64 :=
  match l {
    IrLit.ir_num n _ => Option.some n,
    IrLit.ir_str _ => Option.none,
    IrLit.ir_char _ => Option.none,
    IrLit.ir_float _ _ => Option.none,
    IrLit.ir_sort _ => Option.none,
  }

def opt_value_num_is (ov : Option Value) (expected : I64) : Bool :=
  match ov {
    Option.some v =>
      match value_as_num v {
        Option.some n => I64.beq n expected,
        Option.none => false,
      },
    Option.none => false,
  }

def opt_is_none (ov : Option Value) : Bool :=
  match ov {
    Option.none => true,
    Option.some _ => false,
  }

#[test]
def test_env_nil_get_is_none : Bool :=
  opt_is_none (env_get Env.env_nil 0)

#[test]
def test_env_extend_and_get_innermost_first : Bool :=
  let env : Env := env_extend Env.env_nil (test_lit 1) in // bound first, will be idx 1 once another is pushed
  let env2 : Env := env_extend env (test_lit 2) in // bound last, is idx 0 -- innermost
  opt_value_num_is (env_get env2 0) 2
  && opt_value_num_is (env_get env2 1) 1
  && opt_is_none (env_get env2 2)

#[test]
def test_env_extend_does_not_disturb_shared_tail : Bool :=
  // Two branches extending the SAME base environment must not see each
  // other's bindings -- this is the whole point of a persistent (not
  // in-place-mutated) structure.
  let base : Env := env_extend Env.env_nil (test_lit 0) in
  let branch_a : Env := env_extend base (test_lit 1) in
  let branch_b : Env := env_extend base (test_lit 2) in
  opt_value_num_is (env_get branch_a 0) 1
  && opt_value_num_is (env_get branch_b 0) 2
  && opt_value_num_is (env_get base 0) 0

#[test]
def test_global_cache_starts_empty : Bool :=
  let cache : GlobalCache := global_cache_new 3 in
  opt_is_none (global_cache_get cache 0)
  && opt_is_none (global_cache_get cache 1)

def cache_or_fail_bool (r : Result CoreEvalCycle GlobalCache) (f : GlobalCache -> Bool) : Bool :=
  match r {
    Result.ok cache => f cache,
    Result.err _ => false,
  }

#[test]
def test_global_cache_store_and_get : Bool :=
  let cache0 : GlobalCache := global_cache_new 2 in
  cache_or_fail_bool (global_cache_begin cache0 0) (fn cache1 =>
    let cache2 : GlobalCache := global_cache_store cache1 0 (test_lit 42) in
    opt_value_num_is (global_cache_get cache2 0) 42
      && opt_is_none (global_cache_get cache2 1))

#[test]
def test_global_cache_detects_reentrant_cycle : Bool :=
  let cache0 : GlobalCache := global_cache_new 1 in
  cache_or_fail_bool (global_cache_begin cache0 0) (fn cache1 =>
    // A second `begin` on the same still-in-progress slot is exactly the
    // "some global's value transitively depends on itself" case.
    match global_cache_begin cache1 0 {
      Result.err cycle => cycle_idx_is cycle 0,
      Result.ok _ => false,
    })

def cycle_idx_is (cycle : CoreEvalCycle) (expected : I64) : Bool :=
  match cycle {
    CoreEvalCycle.core_eval_cycle idx => I64.beq idx expected,
  }

def gd_is_constructor (gd : GlobalDef) (expected_tag : I64) (expected_arity : I64) : Bool :=
  match gd {
    GlobalDef.gd_constructor tag arity => I64.beq tag expected_tag && I64.beq arity expected_arity,
    GlobalDef.gd_def _ => false,
    GlobalDef.gd_native _ _ => false,
    GlobalDef.gd_unresolved _ => false,
  }

def gd_is_unresolved (gd : GlobalDef) : Bool :=
  match gd {
    GlobalDef.gd_unresolved _ => true,
    GlobalDef.gd_def _ => false,
    GlobalDef.gd_constructor _ _ => false,
    GlobalDef.gd_native _ _ => false,
  }

#[test]
def test_global_table_basic_access : Bool :=
  let table : GlobalTable :=
    GlobalTable.global_table [
      GlobalDef.gd_constructor 0 2,
      GlobalDef.gd_unresolved (ModulePath.mp [Identifier.id "Foo"]),
    ]
  in
  I64.beq (global_table_len table) 2
  && match global_table_get table 0 {
    Option.some gd => gd_is_constructor gd 0 2,
    Option.none => false,
  }
  && match global_table_get table 1 {
    Option.some gd => gd_is_unresolved gd,
    Option.none => false,
  }
  && match global_table_get table 2 {
    Option.none => true,
    Option.some _ => false,
  }
