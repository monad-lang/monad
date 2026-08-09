//! The evaluator core loop — Phase 4 of
//! `plans/implementations/core-term-closure-evaluator.md`.
//!
//! This is the direct payoff of Phases 1-3: reduces `CoreIr` to `Value`
//! via environment-extending closures, not substitution. There is no
//! `subst`/`shift` function anywhere in this file, on purpose — `App`
//! evaluates its function to a `Value::Closure` and its argument to a
//! `Value` (strict call-by-value, matching `core/src/eval.rs::eval_app`'s
//! confirmed real semantics exactly — see the plan's Context section),
//! then *extends* the closure's captured environment by one binding
//! (`Env::extend`, O(1)) and evaluates the body there. Each argument is
//! evaluated exactly once; every subsequent `Local` reference to it is a
//! shared `Value` clone off the environment, not a re-evaluation — this
//! is the concrete fix for the unmemoized-call-by-name blowup that was
//! the likely dominant cause of `EvalTerm`'s measured 16x regression.
//!
//! Native execution (Phase 5) fires through `core_native::exec_native`
//! once a `CoreIr::Ntv`/`Value::PartialNtv` has accumulated as many args
//! as its native's declared arity (`NativeTable::arity` — resolved once,
//! program-wide, at lowering time, since `CoreIr::Ntv` itself only
//! carries a `native_id`, not an arity; see `core_ir.rs`). Below that
//! count it stays a `Value::PartialNtv`, exactly like an
//! under-saturated `Value::Con`.

use crate::core_ir::{CoreIr, MatchArm};
use crate::core_native::exec_native;
use crate::core_value::{CoreEvalCycle, Env, EnvRef, GlobalCache, GlobalTable, NativeTable, Value};
use crate::lower_core_ir::GlobalDef;
use crate::term::{Identifier, ModulePath};

#[derive(Debug, Clone)]
pub enum CoreEvalError {
  /// A `Local(i)` with no matching environment frame — an internal
  /// lowering bug (the compiled IR references a binder that isn't
  /// actually in scope), not a normal runtime condition.
  UnboundLocal(u32),
  /// A `Global(i)` past the end of `GlobalTable` — also an internal
  /// lowering bug (an index that was never actually assembled).
  UnknownGlobal(u32),
  /// A `Global` slot that `lower_core_ir::lower_program` recorded as
  /// `GlobalDef::Unresolved` (a known, already-diagnosed gap — e.g. a
  /// class method with no dictionary-projection capture yet — see that
  /// module's doc comment) was actually forced at runtime.
  UnresolvedGlobal(ModulePath),
  /// Applied a `Value` that isn't a function, constructor, or native —
  /// only a `Lit` can reach this (the other three variants are all
  /// callable/curryable).
  NotAFunction(Value),
  /// A `Match` scrutinee reduced to something other than `Value::Con` —
  /// only constructors are ever matchable (mirrors `dispatch_recursor`'s
  /// equivalent check in the old `eval_term.rs`).
  NotAConstructor(Value),
  /// A `Match`'s scrutinee tag has no corresponding arm — an internal
  /// lowering bug (`lower_match` builds exactly one arm per constructor
  /// of the scrutinee's inductive, so a valid tag should always have
  /// one).
  CaseIndexOutOfBounds(u32),
  /// A matched constructor's field count didn't match its arm's
  /// declared `bind_count` — another internal-invariant violation, not
  /// a normal runtime condition.
  ArityMismatch { expected: u32, got: u32 },
  /// Forcing a global re-entered its own still-in-progress slot — a
  /// genuine reference cycle. See `GlobalCache::begin`'s doc comment.
  Cycle(CoreEvalCycle),
  /// A `CoreIr::Ntv`/`Value::PartialNtv` referenced a `native_id` with no
  /// entry in `NativeTable` (`core_native.rs`, Phase 5) — an internal
  /// lowering bug (an id `lower_program` never actually interned).
  UnknownNative(u32),
  /// A native fired via `core_native::exec_native` with the wrong number
  /// or shape of arguments (e.g. a string op given a non-`Str` `Value`) —
  /// mirrors `eval_term::EvalError::PrimCallFailed`.
  NativeArgError(String),
  /// A native needed a well-known constructor (`Bool.true`, `Option.some`,
  /// ...) that `WellKnownCtors::resolve` couldn't find in the checked
  /// program — indicates the prelude wasn't loaded, not a normal runtime
  /// condition.
  MissingWellKnownCtor(&'static str),
  /// A `match` with no wildcard, and no case for `ctor` either, actually
  /// produced a value of `ctor` at runtime — see `CoreIr::MatchFail`'s
  /// own doc comment for why this is a genuine (if rare) runtime error
  /// rather than a lowering-time one, unlike every other variant here.
  NonExhaustiveMatch(ModulePath, Identifier),
}

impl std::fmt::Display for CoreEvalError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      CoreEvalError::UnboundLocal(i) => write!(f, "unbound local index {i}"),
      CoreEvalError::UnknownGlobal(i) => write!(f, "unknown global index {i}"),
      CoreEvalError::UnresolvedGlobal(path) => write!(f, "unresolved global: {path}"),
      CoreEvalError::NotAFunction(_) => write!(f, "value is not a function"),
      CoreEvalError::NotAConstructor(_) => write!(f, "value is not a constructor"),
      CoreEvalError::CaseIndexOutOfBounds(tag) => write!(f, "no match arm for tag {tag}"),
      CoreEvalError::ArityMismatch { expected, got } => {
        write!(f, "expected {expected} constructor fields, got {got}")
      }
      CoreEvalError::Cycle(c) => write!(f, "circular global reference at slot {}", c.idx),
      CoreEvalError::UnknownNative(id) => write!(f, "unknown native id {id}"),
      CoreEvalError::NativeArgError(msg) => write!(f, "native call failed: {msg}"),
      CoreEvalError::MissingWellKnownCtor(name) => {
        write!(f, "missing well-known constructor: {name}")
      }
      CoreEvalError::NonExhaustiveMatch(inductive, ctor) => {
        write!(
          f,
          "non-exhaustive match: {inductive}.{ctor} was constructed but not covered by this match"
        )
      }
    }
  }
}

/// Evaluate `ir` to a `Value` in environment `env`, against whole-program
/// `globals`/`natives`, memoizing any global references forced along the
/// way into `cache`.
pub fn eval(
  ir: &CoreIr,
  env: &EnvRef,
  globals: &GlobalTable,
  natives: &NativeTable,
  cache: &mut GlobalCache,
) -> Result<Value, CoreEvalError> {
  match ir {
    CoreIr::Local(i) => Env::get(env, *i)
      .cloned()
      .ok_or(CoreEvalError::UnboundLocal(*i)),
    CoreIr::Global(idx) => force_global(*idx, globals, natives, cache),
    CoreIr::Lam { body } => Ok(Value::Closure {
      body: body.clone(),
      env: env.clone(),
    }),
    CoreIr::App { fun, arg } => {
      // Strict call-by-value: both sides are fully reduced to a Value
      // before `apply` ever runs — no unevaluated thunk is ever
      // substituted in, unlike `EvalTerm::eval`'s naive-call-by-name
      // `subst`.
      let f = eval(fun, env, globals, natives, cache)?;
      let a = eval(arg, env, globals, natives, cache)?;
      apply(f, a, globals, natives, cache)
    }
    CoreIr::Lit(l) => Ok(Value::Lit(l.clone())),
    CoreIr::Match { scrutinee, arms } => {
      let v = eval(scrutinee, env, globals, natives, cache)?;
      dispatch(v, arms, env, globals, natives, cache)
    }
    CoreIr::MatchFail { inductive, ctor } => Err(CoreEvalError::NonExhaustiveMatch(
      inductive.clone(),
      ctor.clone(),
    )),
    CoreIr::Con {
      tag,
      arity: _,
      args,
    } => {
      let mut evaluated = Vec::with_capacity(args.len());
      for a in args {
        evaluated.push(eval(a, env, globals, natives, cache)?);
      }
      Ok(Value::Con {
        tag: *tag,
        args: evaluated,
      })
    }
    CoreIr::Ntv { native_id, args } => {
      let mut evaluated = Vec::with_capacity(args.len());
      for a in args {
        evaluated.push(eval(a, env, globals, natives, cache)?);
      }
      fire_or_accumulate(*native_id, evaluated, natives)
    }
  }
}

/// Fire a native call once `args.len()` reaches its declared arity
/// (`NativeTable::arity`); below that, stay a `Value::PartialNtv`,
/// exactly like an under-saturated `Value::Con`. Shared between
/// `CoreIr::Ntv`'s own (typically already-saturated — see
/// `core_native.rs`'s doc comment) evaluation and `apply`'s incremental,
/// one-arg-at-a-time accumulation.
fn fire_or_accumulate(
  native_id: u32,
  args: Vec<Value>,
  natives: &NativeTable,
) -> Result<Value, CoreEvalError> {
  let arity = natives.arity(native_id) as usize;
  if args.len() >= arity {
    let name = natives
      .name(native_id)
      .ok_or(CoreEvalError::UnknownNative(native_id))?;
    exec_native(name.as_str(), &args, natives)
  } else {
    Ok(Value::PartialNtv { native_id, args })
  }
}

/// Apply `f` to `a`. The `Closure` case is the direct fix for
/// `EvalTerm`'s substitution-based beta reduction: extend the closure's
/// *captured* environment by one binding (O(1) — one `Arc` allocation,
/// no tree copy) and evaluate its body there, rather than rewriting the
/// body to replace every occurrence of the bound variable. Public so a
/// caller that's already forced a global to a `Value` (e.g. `main`, in
/// `lib.rs::run`) can apply further arguments to it (CLI `argv`) without
/// re-deriving this match itself.
pub fn apply(
  f: Value,
  a: Value,
  globals: &GlobalTable,
  natives: &NativeTable,
  cache: &mut GlobalCache,
) -> Result<Value, CoreEvalError> {
  match f {
    Value::Closure { body, env } => {
      let extended = Env::extend(&env, a);
      eval(&body, &extended, globals, natives, cache)
    }
    Value::Con { tag, mut args } => {
      args.push(a);
      Ok(Value::Con { tag, args })
    }
    Value::PartialNtv {
      native_id,
      mut args,
    } => {
      args.push(a);
      fire_or_accumulate(native_id, args, natives)
    }
    Value::Lit(lit) => Err(CoreEvalError::NotAFunction(Value::Lit(lit))),
  }
}

/// Constructor-tag dispatch: index straight into `arms` by the
/// scrutinee's tag (no scan, unlike a name-keyed `match` — this is
/// exactly `lower_match`'s whole point), then extend the *enclosing*
/// environment (`env` — the one active where this `Match` node itself
/// sits, NOT a fresh one) with the constructor's own fields. This
/// matters: a match arm's body is not closed over just its own fields —
/// `CoreMatchCase.value` is lowered without `open_n` (see
/// `lower_core_ir.rs::lower_match`'s doc comment), so a `Bound`/`Local`
/// index inside it can still count *past* the newly-introduced field
/// bindings to reach an outer enclosing binder (e.g. `\x -> match xs {
/// cons h t => x }` — `x`'s reference inside the arm has to walk past
/// `h`/`t` to reach it). Fields are pushed in their natural (declaration)
/// order, which leaves the *last*-declared field innermost (`Local(0)`),
/// matching `project_dict_field`'s documented `fields.len()-1-idx`
/// convention.
fn dispatch(
  scrutinee: Value,
  arms: &[MatchArm],
  env: &EnvRef,
  globals: &GlobalTable,
  natives: &NativeTable,
  cache: &mut GlobalCache,
) -> Result<Value, CoreEvalError> {
  let Value::Con { tag, args } = scrutinee else {
    return Err(CoreEvalError::NotAConstructor(scrutinee));
  };
  let arm = arms
    .get(tag as usize)
    .ok_or(CoreEvalError::CaseIndexOutOfBounds(tag))?;
  if args.len() != arm.bind_count as usize {
    return Err(CoreEvalError::ArityMismatch {
      expected: arm.bind_count,
      got: args.len() as u32,
    });
  }
  let mut extended = env.clone();
  for field in args {
    extended = Env::extend(&extended, field);
  }
  eval(&arm.body, &extended, globals, natives, cache)
}

/// Force global slot `idx` to a `Value`, memoizing the result in
/// `cache` — each global's body is walked to a `Value` at most once per
/// `cache`, ever, regardless of how many call sites reference it (this
/// is what gives dictionary/typeclass-method access the same O(1),
/// resolve-once treatment as any other global — see
/// `lower_core_ir::lower_program`'s doc comment on assembling an
/// instance's dictionary as a `Con` of `Global` references specifically
/// so this memoization applies to it too).
pub fn force_global(
  idx: u32,
  globals: &GlobalTable,
  natives: &NativeTable,
  cache: &mut GlobalCache,
) -> Result<Value, CoreEvalError> {
  if let Some(v) = cache.get(idx) {
    return Ok(v.clone());
  }
  cache.begin(idx).map_err(CoreEvalError::Cycle)?;
  // Computed in a closure, not inline, so every error path below (the
  // unknown-index `?`, `eval`'s own `?`, `Unresolved`'s explicit
  // `return Err`) funnels through the SAME `cache.fail` cleanup below —
  // without it, a slot that fails once stays `InProgress` forever, and
  // any LATER, unrelated force of the same slot (real scenario: several
  // callers share one `GlobalCache` across many top-level forces, e.g.
  // `core_parity.rs` forcing every discovered test in a file) reports a
  // spurious `Cycle` instead of retrying and surfacing the real error.
  let result = (|| -> Result<Value, CoreEvalError> {
    Ok(
      match globals.get(idx).ok_or(CoreEvalError::UnknownGlobal(idx))? {
        GlobalDef::Def(ir) => eval(ir, &Env::nil(), globals, natives, cache)?,
        // A constructor referenced point-free (no CoreIr body -- see
        // GlobalDef::Constructor's doc comment) resolves straight to an
        // empty, ready-to-fill constructor value; ordinary `apply` fills it
        // left-to-right from there, same as any partially-applied Con.
        GlobalDef::Constructor { tag, arity: _ } => Value::Con {
          tag: *tag,
          args: Vec::new(),
        },
        // A native-attributed def with no explicit body (no useful `CoreIr`
        // body exists for it either — see `GlobalDef::Native`'s doc comment)
        // resolves the same way `Constructor` does: an empty, ready-to-fill
        // value (0 args accumulated so far), filled left-to-right by ordinary
        // `apply`/`fire_or_accumulate` — which also handles the (currently
        // unused in practice, but not assumed away) `arity == 0` case by
        // firing immediately instead of leaving a permanently-`PartialNtv`
        // value nothing would ever apply an argument to.
        GlobalDef::Native { native_id, .. } => fire_or_accumulate(*native_id, Vec::new(), natives)?,
        GlobalDef::Unresolved(path) => return Err(CoreEvalError::UnresolvedGlobal(path.clone())),
      },
    )
  })();
  match result {
    Ok(value) => {
      cache.store(idx, value.clone());
      Ok(value)
    }
    Err(e) => {
      cache.fail(idx);
      Err(e)
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::core_ir::{self, IrLit};
  use crate::lower_core_ir::GlobalDef;
  use crate::term::NumSuffix;

  fn num(v: i64) -> CoreIr {
    core_ir::lit(IrLit::Num(v, NumSuffix::I64))
  }

  fn empty_natives() -> NativeTable {
    NativeTable::new(vec![], vec![], Default::default())
  }

  fn eval_closed(ir: &CoreIr) -> Result<Value, CoreEvalError> {
    let globals = GlobalTable::new(vec![]);
    let natives = empty_natives();
    let mut cache = GlobalCache::new(0);
    eval(ir, &Env::nil(), &globals, &natives, &mut cache)
  }

  #[test]
  fn test_literal_evaluates_to_itself() {
    let v = eval_closed(&num(42)).unwrap();
    assert!(matches!(v, Value::Lit(IrLit::Num(42, _))));
  }

  #[test]
  fn test_identity_application() {
    // (\x -> x) 42
    let id_fn = core_ir::lam(core_ir::local(0));
    let applied = core_ir::app(id_fn, num(42));
    let v = eval_closed(&applied).unwrap();
    assert!(matches!(v, Value::Lit(IrLit::Num(42, _))));
  }

  #[test]
  fn test_k_combinator_closure_captures_correct_binding() {
    // (\x -> \y -> x) 1 2 -- classic test that closures capture the
    // right environment frame, not just "some" environment: if `Lam`
    // captured the environment incorrectly (e.g. shared/aliased across
    // both applications), this would return 2, not 1.
    let k = core_ir::lam(core_ir::lam(core_ir::local(1)));
    let applied = core_ir::app(core_ir::app(k, num(1)), num(2));
    let v = eval_closed(&applied).unwrap();
    assert!(matches!(v, Value::Lit(IrLit::Num(1, _))));
  }

  #[test]
  fn test_nested_lambdas_independent_applications_do_not_interfere() {
    // let add_one = \x -> \y -> y in (add_one 1) applied to 10, then
    // SEPARATELY (add_one 2) applied to 20 -- each partial application
    // must capture its OWN `x`, not share/overwrite one across calls.
    // (add_one always returns y here since we're not testing arithmetic,
    // just environment independence -- see test_closure_after_extend_*
    // below for the actual "x" case.)
    let add_one = core_ir::lam(core_ir::lam(core_ir::local(0)));
    let partial_a = core_ir::app(add_one.clone(), num(1));
    let partial_b = core_ir::app(add_one, num(2));
    let call_a = core_ir::app(partial_a, num(10));
    let call_b = core_ir::app(partial_b, num(20));
    assert!(matches!(
      eval_closed(&call_a).unwrap(),
      Value::Lit(IrLit::Num(10, _))
    ));
    assert!(matches!(
      eval_closed(&call_b).unwrap(),
      Value::Lit(IrLit::Num(20, _))
    ));
  }

  #[test]
  fn test_applying_a_literal_errors() {
    let bad = core_ir::app(num(1), num(2));
    let err = eval_closed(&bad).unwrap_err();
    assert!(matches!(err, CoreEvalError::NotAFunction(_)));
  }

  #[test]
  fn test_con_construction_and_partial_application() {
    // A 2-arity constructor applied to only one argument stays partial.
    let partial = core_ir::con(0, 2, vec![num(1)]);
    let v = eval_closed(&partial).unwrap();
    let Value::Con { tag, ref args } = v else {
      panic!("expected Con")
    };
    assert_eq!(tag, 0);
    assert_eq!(args.len(), 1);

    // Applying the remaining argument (via `apply`, as ordinary
    // application would) fills it.
    let globals = GlobalTable::new(vec![]);
    let natives = empty_natives();
    let mut cache = GlobalCache::new(0);
    let filled = apply(
      v,
      Value::Lit(IrLit::Num(2, NumSuffix::I64)),
      &globals,
      &natives,
      &mut cache,
    )
    .unwrap();
    let Value::Con { args, .. } = filled else {
      panic!("expected Con")
    };
    assert_eq!(args.len(), 2);
  }

  #[test]
  fn test_match_dispatches_to_correct_arm_and_binds_fields() {
    // match Con(tag=1, [10, 20]) { [_, _ -> local0] , [x,y -> x] } --
    // tag 1's arm binds 2 fields and returns the first-declared one
    // (Local(1), since the LAST-declared field is Local(0) -- see
    // dispatch's own doc comment).
    let scrutinee = core_ir::con(1, 2, vec![num(10), num(20)]);
    let arm0 = core_ir::arm(0, num(999)); // never reached
    let arm1 = core_ir::arm(2, core_ir::local(1)); // first-declared field
    let m = core_ir::match_(scrutinee, vec![arm0, arm1]);
    let v = eval_closed(&m).unwrap();
    assert!(matches!(v, Value::Lit(IrLit::Num(10, _))));
  }

  #[test]
  fn test_match_arm_body_can_reach_an_outer_enclosing_binding() {
    // \x -> match Con(1, [field]) { arm0(binds 0) => 999, arm1(binds 1)
    // => Local(1) } -- arm1's Local(1) must walk PAST its own one bound
    // field (Local(0)) to reach `x` (the outer Lam's parameter), proving
    // `dispatch` extends the *enclosing* environment rather than
    // starting fresh from empty (a real bug caught and fixed while
    // writing this evaluator -- a match at the top level, like the test
    // above, can't distinguish the two, since the outer environment is
    // already empty there).
    let scrutinee = core_ir::con(1, 1, vec![num(0)]);
    let arm0 = core_ir::arm(0, num(999));
    let arm1 = core_ir::arm(1, core_ir::local(1)); // reaches past the 1 bound field to `x`
    let body = core_ir::match_(scrutinee, vec![arm0, arm1]);
    let f = core_ir::lam(body);
    let applied = core_ir::app(f, num(77));
    let v = eval_closed(&applied).unwrap();
    assert!(matches!(v, Value::Lit(IrLit::Num(77, _))));
  }

  #[test]
  fn test_match_on_non_constructor_errors() {
    let m = core_ir::match_(num(1), vec![core_ir::arm(0, num(0))]);
    let err = eval_closed(&m).unwrap_err();
    assert!(matches!(err, CoreEvalError::NotAConstructor(_)));
  }

  #[test]
  fn test_global_resolves_and_memoizes() {
    // globals[0] = 5 (a plain literal def)
    let globals = GlobalTable::new(vec![GlobalDef::Def(std::sync::Arc::new(num(5)))]);
    let natives = empty_natives();
    let mut cache = GlobalCache::new(1);
    let v1 = force_global(0, &globals, &natives, &mut cache).unwrap();
    assert!(matches!(v1, Value::Lit(IrLit::Num(5, _))));
    // Second force must come from the cache -- confirmed structurally
    // (not just "returns the same value again", which a non-memoized
    // re-evaluation would also do): the cache slot is populated after
    // the first call.
    assert!(cache.get(0).is_some());
    let v2 = force_global(0, &globals, &natives, &mut cache).unwrap();
    assert!(matches!(v2, Value::Lit(IrLit::Num(5, _))));
  }

  #[test]
  fn test_global_referencing_constructor_slot_is_empty_con() {
    let globals = GlobalTable::new(vec![GlobalDef::Constructor { tag: 3, arity: 2 }]);
    let natives = empty_natives();
    let mut cache = GlobalCache::new(1);
    let v = force_global(0, &globals, &natives, &mut cache).unwrap();
    assert!(matches!(v, Value::Con { tag: 3, ref args } if args.is_empty()));
  }

  #[test]
  fn test_unresolved_global_errors() {
    let globals = GlobalTable::new(vec![GlobalDef::Unresolved(crate::term::mpt("Foo.bar"))]);
    let natives = empty_natives();
    let mut cache = GlobalCache::new(1);
    let err = force_global(0, &globals, &natives, &mut cache).unwrap_err();
    assert!(matches!(err, CoreEvalError::UnresolvedGlobal(_)));
  }

  #[test]
  fn test_failed_global_does_not_permanently_poison_cache_as_a_false_cycle() {
    // A slot that fails once must NOT stay stuck `InProgress` forever --
    // a real scenario (`core_parity.rs` shares one `GlobalCache` across
    // every discovered test in a file, and two unrelated tests can
    // easily share a common helper global) is a LATER, unrelated force
    // of the SAME slot after an earlier failure. Without releasing the
    // `InProgress` marker on error, that later force would incorrectly
    // report `CoreEvalError::Cycle` -- masking the real, deterministic
    // error (there's no external mutable state here to make the second
    // attempt behave differently) behind a false "circular reference".
    let globals = GlobalTable::new(vec![GlobalDef::Unresolved(crate::term::mpt("Foo.bar"))]);
    let natives = empty_natives();
    let mut cache = GlobalCache::new(1);
    let err1 = force_global(0, &globals, &natives, &mut cache).unwrap_err();
    assert!(matches!(err1, CoreEvalError::UnresolvedGlobal(_)));
    let err2 = force_global(0, &globals, &natives, &mut cache).unwrap_err();
    assert!(
      matches!(err2, CoreEvalError::UnresolvedGlobal(_)),
      "expected the same real error again on retry, got {err2:?}"
    );
  }

  #[test]
  fn test_direct_self_reference_cycle_errors_cleanly() {
    // globals[0]'s own body directly references Global(0) -- a genuine
    // cycle (not the safe "recursion inside a Lam body" case, since
    // this Global reference sits at the def's own top-level spine, not
    // behind a Lam -- forcing it immediately re-enters itself).
    let globals = GlobalTable::new(vec![GlobalDef::Def(std::sync::Arc::new(core_ir::global(
      0,
    )))]);
    let natives = empty_natives();
    let mut cache = GlobalCache::new(1);
    let err = force_global(0, &globals, &natives, &mut cache).unwrap_err();
    assert!(matches!(err, CoreEvalError::Cycle(_)));
  }

  #[test]
  fn test_ordinary_recursive_function_is_not_a_false_cycle() {
    // globals[0] = \n -> Global(0)  -- an ordinary recursive function
    // reference (the Global sits behind a Lam, never forced until
    // applied) must NOT be treated as a cycle -- this is exactly the
    // "mutual/self recursion between functions is safe" case the plan's
    // Open Question #6 investigated.
    let globals = GlobalTable::new(vec![GlobalDef::Def(std::sync::Arc::new(core_ir::lam(
      core_ir::global(0),
    )))]);
    let natives = empty_natives();
    let mut cache = GlobalCache::new(1);
    let v = force_global(0, &globals, &natives, &mut cache).unwrap();
    assert!(matches!(v, Value::Closure { .. }));
  }
}
