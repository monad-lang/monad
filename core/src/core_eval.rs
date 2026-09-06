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

use std::sync::Arc;

use crate::core_ir::{CoreIr, IrRef};
use crate::core_native::exec_native;
use crate::core_value::{
  ConArgs, CoreEvalCycle, Env, EnvRef, GlobalCache, GlobalTable, NativeTable, Value,
};
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
  /// A native outside `core_native::is_pure_native`'s allowlist was
  /// called against a `GlobalCache::new_pure` cache — see
  /// `GlobalCache`'s `pure_only` field doc comment
  /// (`core/src/core_value.rs`). Not possible against an ordinary
  /// (`GlobalCache::new`) cache, which never sets this restriction.
  ImpureNativeBlocked(String),
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
      CoreEvalError::ImpureNativeBlocked(name) => {
        write!(
          f,
          "native `{name}` is unavailable here — this code runs in a pure, IO/concurrency-free \
           sandbox (macro-expansion-time evaluation)"
        )
      }
    }
  }
}

/// Evaluate `ir` to a `Value` in environment `env`, against whole-program
/// `globals`/`natives`, memoizing any global references forced along the
/// way into `cache`.
///
/// Structured as a `loop` over owned `(cur_ir, cur_env)` state, not a
/// plain recursive `match`, specifically so a tail call — `App` applying
/// to a `Value::Closure`, or `Match` dispatching to an arm — becomes a
/// loop `continue` (reassign `cur_ir`/`cur_env`, no new Rust stack frame)
/// instead of a real recursive `eval` call. Without this, every
/// self-recursive closure application (an ordinary accumulator-style
/// loop written in `.mo`) grew the native Rust stack by a frame per
/// iteration, even though it's syntactically a tail call — confirmed by
/// `bench/scope_lookup.mo` stack-overflowing at n≈1000 even under 64MB
/// worker-thread stacks (see self-hosted-compiler-perf.md Step 3).
/// `CoreIr`'s recursive fields are already `IrRef = Arc<CoreIr>`, so
/// reassigning `cur_ir`/`cur_env` each iteration is an `Arc::clone`
/// (O(1) refcount bump), not a subtree copy.
///
/// Every OTHER recursive `eval` call below (evaluating `App`'s
/// `fun`/`arg`, `Match`'s `scrutinee`, `Con`/`Ntv`'s argument list) stays
/// real Rust recursion, deliberately: those are bounded by *static*
/// source-term nesting depth, not by *dynamic* call count, so they don't
/// need trampolining — only the two positions that can loop an unbounded
/// number of times at runtime do. This means genuinely non-tail-recursive
/// `.mo` code (e.g. `len xs = match xs { cons _ t => 1 + len t, ... }`,
/// where the recursive call is wrapped by `+`) still consumes O(N) Rust
/// stack depth, same as in any language with TCO — the 64MB worker-thread
/// stack (`lib.rs`) stays in place as a backstop for that case.
pub fn eval(
  ir: &IrRef,
  env: &EnvRef,
  globals: &GlobalTable,
  natives: &NativeTable,
  cache: &mut GlobalCache,
) -> Result<Value, CoreEvalError> {
  let mut cur_ir: IrRef = ir.clone();
  let mut cur_env: EnvRef = env.clone();
  loop {
    match cur_ir.as_ref() {
      CoreIr::Local(i) => {
        return Env::get(&cur_env, *i)
          .cloned()
          .ok_or_else(|| CoreEvalError::UnboundLocal(*i));
      }
      CoreIr::Global(idx) => {
        return force_global(*idx, globals, natives, cache);
      }
      CoreIr::Lam { body } => {
        return Ok(Value::Closure {
          body: body.clone(),
          env: cur_env.clone(),
        });
      }
      CoreIr::App { fun, arg } => {
        // Strict call-by-value: both sides are fully reduced to a Value
        // before applying — no unevaluated thunk is ever substituted
        // in, unlike `EvalTerm::eval`'s naive-call-by-name `subst`.
        let f = eval(fun, &cur_env, globals, natives, cache)?;
        let a = eval(arg, &cur_env, globals, natives, cache)?;
        // Inlined from the former standalone `apply` (still kept, see
        // below, for callers that already hold a `Value` to apply):
        // the `Closure` branch is the actual tail-call fix — loop back
        // instead of recursing into `eval` — every other branch
        // terminates immediately, same as `apply` does today.
        match f {
          Value::Closure { body, env } => {
            cur_env = Env::extend(&env, a);
            cur_ir = body;
            continue;
          }
          Value::Con { tag, mut args } => {
            Arc::make_mut(&mut args).push(a);
            return Ok(Value::Con { tag, args });
          }
          Value::PartialNtv {
            native_id,
            mut args,
          } => {
            Arc::make_mut(&mut args).push(a);
            return fire_or_accumulate(native_id, args, globals, natives, cache);
          }
          Value::Lit(lit) => {
            return Err(CoreEvalError::NotAFunction(Value::Lit(lit)));
          }
        }
      }
      CoreIr::Lit(l) => {
        return Ok(Value::Lit(l.clone()));
      }
      CoreIr::Match { scrutinee, arms } => {
        let v = eval(scrutinee, &cur_env, globals, natives, cache)?;
        // Inlined from the former standalone `dispatch` (no external
        // callers — folded in directly rather than kept as a separate
        // function that would need its own tail-call handling): index
        // straight into `arms` by the scrutinee's tag (no scan — this
        // is exactly `lower_match`'s whole point), then extend the
        // *enclosing* environment (`cur_env` — the one active where
        // this `Match` node itself sits, NOT a fresh one) with the
        // constructor's own fields. This matters: a match arm's body is
        // not closed over just its own fields — `CoreMatchCase.value`
        // is lowered without `open_n` (see `lower_core_ir.rs::
        // lower_match`'s doc comment), so a `Bound`/`Local` index inside
        // it can still count *past* the newly-introduced field bindings
        // to reach an outer enclosing binder (e.g. `\x -> match xs {
        // cons h t => x }` — `x`'s reference inside the arm has to walk
        // past `h`/`t` to reach it). Fields are pushed in their natural
        // (declaration) order, which leaves the *last*-declared field
        // innermost (`Local(0)`), matching `project_dict_field`'s
        // documented `fields.len()-1-idx` convention.
        let Value::Con { tag, args } = v else {
          return Err(CoreEvalError::NotAConstructor(v));
        };
        let arm = arms
          .get(tag as usize)
          .ok_or_else(|| CoreEvalError::CaseIndexOutOfBounds(tag))?;
        if args.len() != arm.bind_count as usize {
          return Err(CoreEvalError::ArityMismatch {
            expected: arm.bind_count,
            got: args.len() as u32,
          });
        }
        let mut extended = cur_env.clone();
        // The single most-executed `Con`-consumption point in the
        // evaluator (every pattern match against a constructor), so what
        // it allocates matters. This used to be
        // `Arc::make_mut(&mut args).drain(..)`, justified as "O(1) in the
        // common (uniquely-owned) case" — but uniquely-owned is the RARE
        // case here, not the common one: the scrutinee came from
        // `eval(scrutinee, ...)`, and for the overwhelmingly common
        // `CoreIr::Local` case that is `Env::get(...).cloned()` (above),
        // so the environment still holds a second `Arc` and `make_mut`
        // takes the COPY path — allocating a fresh `Vec`, shallow-cloning
        // `arity` values into it, draining it, and dropping it, on every
        // single match. Splitting the two cases explicitly allocates no
        // `Vec` on either path: uniquely owned (`try_unwrap`) moves each
        // field out with no clone at all, and shared borrows in place and
        // clones each field, which is an O(1) refcount bump per `Value`
        // since the `Con`/`PartialNtv` args Arc-wrap.
        match Arc::try_unwrap(args) {
          Ok(mut owned) => {
            for field in owned.drain(..) {
              extended = Env::extend(&extended, field);
            }
          }
          Err(shared) => {
            for field in shared.iter() {
              extended = Env::extend(&extended, field.clone());
            }
          }
        }
        cur_env = extended;
        cur_ir = arm.body.clone();
        continue;
      }
      CoreIr::MatchFail { inductive, ctor } => {
        return Err(CoreEvalError::NonExhaustiveMatch(
          inductive.clone(),
          ctor.clone(),
        ));
      }
      CoreIr::Con {
        tag,
        arity: _,
        args,
      } => {
        let mut evaluated = Vec::with_capacity(args.len());
        for a in args {
          evaluated.push(eval(a, &cur_env, globals, natives, cache)?);
        }
        return Ok(Value::Con {
          tag: *tag,
          args: Arc::new(evaluated.into()),
        });
      }
      CoreIr::Ntv { native_id, args } => {
        let mut evaluated = Vec::with_capacity(args.len());
        for a in args {
          evaluated.push(eval(a, &cur_env, globals, natives, cache)?);
        }
        return fire_or_accumulate(
          *native_id,
          Arc::new(evaluated.into()),
          globals,
          natives,
          cache,
        );
      }
    }
  }
}

/// Fire a native call once `args.len()` reaches its declared arity
/// (`NativeTable::arity`); below that, stay a `Value::PartialNtv`,
/// exactly like an under-saturated `Value::Con`. Shared between
/// `CoreIr::Ntv`'s own (typically already-saturated — see
/// `core_native.rs`'s doc comment) evaluation and `apply`'s incremental,
/// one-arg-at-a-time accumulation.
///
/// Takes `globals`/`cache` (not just `natives`, unlike `exec_native`
/// itself) purely for `await_fiber`'s sake: running a forked fiber's
/// deferred action means applying its stored closure, which needs the
/// same `apply` this function's own callers already have in scope. Every
/// other native ignores them and goes through `exec_native` unchanged —
/// see `core_native::await_fiber`'s own doc comment for why it alone
/// needs this.
fn fire_or_accumulate(
  native_id: u32,
  args: Arc<ConArgs>,
  globals: &GlobalTable,
  natives: &NativeTable,
  cache: &mut GlobalCache,
) -> Result<Value, CoreEvalError> {
  let arity = natives.arity(native_id) as usize;
  if args.len() >= arity {
    let name = natives
      .name(native_id)
      .ok_or_else(|| CoreEvalError::UnknownNative(native_id))?;
    // `await_fiber` is handled outside `exec_native`'s own allowlisted
    // match (see this function's doc comment), so it needs its own
    // purity check here rather than falling under `is_pure_native`.
    if cache.is_pure_only() && !crate::core_native::is_pure_native(name.as_str()) {
      return Err(CoreEvalError::ImpureNativeBlocked(name.to_string()));
    }
    if name.as_str() == "await_fiber" {
      crate::core_native::await_fiber(&args, globals, natives, cache)
    } else {
      exec_native(name.as_str(), &args, natives)
    }
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
/// `lib.rs::run`, or `await_fiber` in `core_native.rs`) can apply further
/// arguments to it without re-deriving this match itself. Delegating the
/// `Closure` branch into `eval` (trampolined — see its doc comment) means
/// these callers get the same bounded-native-stack-growth guarantee for
/// whatever closure they apply, with no changes needed on their end —
/// `eval`'s own internal `App`-to-`Closure` tail calls are just the
/// hottest, most common way this same code path gets reached.
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
      Arc::make_mut(&mut args).push(a);
      Ok(Value::Con { tag, args })
    }
    Value::PartialNtv {
      native_id,
      mut args,
    } => {
      Arc::make_mut(&mut args).push(a);
      fire_or_accumulate(native_id, args, globals, natives, cache)
    }
    Value::Lit(lit) => Err(CoreEvalError::NotAFunction(Value::Lit(lit))),
  }
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
  // Some globals are an EFFECT, not a value: forcing one performs
  // something, so it must be performed again on the next reference
  // rather than answered from `cache`. Everything else here (an ordinary
  // def's body, a constructor, an instance dictionary) is pure and
  // memoizes safely — which is the entire point of the caching below.
  //
  // Bypassing the cache means both halves: never reading a previous
  // force's result, and never storing this one. That is what lets a
  // second textual reference observe a fresh result.
  //
  // Two shapes qualify, and BOTH are needed — they are the same bug at
  // different levels of indirection:
  //
  //   `Native { arity: 0 }`  the def IS the native, bodyless
  //                          (`#[native current_time] def
  //                          IO.current_time : IO I64`). Without this,
  //                          `scope_new` called from two `#[test]` defs
  //                          sharing one `GlobalCache` hands both the
  //                          SAME registry handle, and the second test's
  //                          `scope_drop`/`scope_fork` fails with "scope
  //                          <id> not found" because the first already
  //                          removed it.
  //
  //   `Effect(..)`           the def WRAPS one (`def Bench.now : IO I64
  //                          := current_time`). Having a body made it
  //                          lower to `Def`, which the native-only check
  //                          above never saw, so it memoized — freezing
  //                          every `--verbose` stage timing in the
  //                          compiler to one constant. Keyed on the
  //                          declared type (`lower_core_ir`'s
  //                          `is_effect_type`), which no amount of
  //                          wrapping can launder away.
  match globals.get(idx) {
    Some(GlobalDef::Native {
      native_id,
      arity: 0,
    }) => {
      return fire_or_accumulate(
        *native_id,
        Arc::new(Vec::new().into()),
        globals,
        natives,
        cache,
      );
    }
    Some(GlobalDef::Effect(ir)) => {
      let ir = ir.clone();
      return eval(&ir, &Env::nil(), globals, natives, cache);
    }
    _ => {}
  }
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
      match globals
        .get(idx)
        .ok_or_else(|| CoreEvalError::UnknownGlobal(idx))?
      {
        GlobalDef::Def(ir) => eval(ir, &Env::nil(), globals, natives, cache)?,
        // Unreachable: the early return above takes every `Effect` slot
        // before the cache is ever consulted. Spelled out rather than
        // folded into a catch-all so that adding a variant here stays a
        // compile error.
        GlobalDef::Effect(ir) => eval(ir, &Env::nil(), globals, natives, cache)?,
        // A constructor referenced point-free (no CoreIr body -- see
        // GlobalDef::Constructor's doc comment) resolves straight to an
        // empty, ready-to-fill constructor value; ordinary `apply` fills it
        // left-to-right from there, same as any partially-applied Con.
        GlobalDef::Constructor { tag, arity: _ } => Value::Con {
          tag: *tag,
          args: Arc::new(Vec::new().into()),
        },
        // A native-attributed def with no explicit body (no useful `CoreIr`
        // body exists for it either — see `GlobalDef::Native`'s doc comment)
        // resolves the same way `Constructor` does: an empty, ready-to-fill
        // value (0 args accumulated so far), filled left-to-right by ordinary
        // `apply`/`fire_or_accumulate` — which also handles the (currently
        // unused in practice, but not assumed away) `arity == 0` case by
        // firing immediately instead of leaving a permanently-`PartialNtv`
        // value nothing would ever apply an argument to.
        GlobalDef::Native { native_id, .. } => fire_or_accumulate(
          *native_id,
          Arc::new(Vec::new().into()),
          globals,
          natives,
          cache,
        )?,
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
    let ir_ref: IrRef = std::sync::Arc::new(ir.clone());
    eval(&ir_ref, &Env::nil(), &globals, &natives, &mut cache)
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
  fn test_partial_con_application_from_shared_value_does_not_leak_across_branches() {
    // The copy-on-write hazard `Value::Con`'s `Arc<Vec<Value>>` args
    // introduces (see its doc comment, `core_value.rs`): a memoized
    // global constructor is forced twice, so both `base_a`/`base_b` (and
    // the still-`cache`-stored copy) share ONE underlying `Arc`. Each
    // branch then applies a DIFFERENT extra argument to its own copy —
    // `Arc::make_mut`'s copy-on-write must kick in so neither branch's
    // argument leaks into the other, or into the cache's own stored
    // value.
    let globals = GlobalTable::new(vec![GlobalDef::Constructor { tag: 0, arity: 2 }]);
    let natives = empty_natives();
    let mut cache = GlobalCache::new(1);

    let base_a = force_global(0, &globals, &natives, &mut cache).unwrap();
    let base_b = force_global(0, &globals, &natives, &mut cache).unwrap();

    let branch_a = apply(
      base_a,
      Value::Lit(IrLit::Num(1, NumSuffix::I64)),
      &globals,
      &natives,
      &mut cache,
    )
    .unwrap();
    let branch_b = apply(
      base_b,
      Value::Lit(IrLit::Num(2, NumSuffix::I64)),
      &globals,
      &natives,
      &mut cache,
    )
    .unwrap();

    let Value::Con { args: args_a, .. } = branch_a else {
      panic!("expected Con")
    };
    let Value::Con { args: args_b, .. } = branch_b else {
      panic!("expected Con")
    };
    assert!(matches!(args_a.as_slice(), [Value::Lit(IrLit::Num(1, _))]));
    assert!(matches!(args_b.as_slice(), [Value::Lit(IrLit::Num(2, _))]));

    // The cache's own stored copy (a third alias of the same base value)
    // must be unaffected by either branch's mutation.
    let Value::Con {
      args: cached_args, ..
    } = cache.get(0).unwrap()
    else {
      panic!("expected Con")
    };
    assert!(cached_args.is_empty());
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
  fn test_zero_arity_native_global_is_not_memoized() {
    // Unlike `test_global_resolves_and_memoizes` above: a zero-arity
    // native-attributed def (`IO.current_time`/`scope_new` — always
    // side-effecting, that's the whole reason they're natives rather
    // than ordinary `def`s) must be re-run on every reference, never
    // cached — see `force_global`'s own doc comment for the real bug
    // this fixes (`scope_new` shared across two `#[test]` defs via one
    // `GlobalCache` returning the same already-consumed registry handle
    // to both).
    let globals = GlobalTable::new(vec![GlobalDef::Native {
      native_id: 0,
      arity: 0,
    }]);
    // `current_time` is `IO I64`, so it wraps its result in `IO.io` --
    // that constructor has to be known here or the native fails before
    // memoization is ever exercised.
    let natives = NativeTable::new(
      vec![crate::term::id("current_time")],
      vec![0],
      crate::lower_core_ir::WellKnownCtors {
        io_io: Some(crate::lower_core_ir::CtorTag { tag: 0, arity: 1 }),
        ..Default::default()
      },
    );
    let mut cache = GlobalCache::new(1);
    force_global(0, &globals, &natives, &mut cache).unwrap();
    // The defining structural check (mirrors the memoized case's own
    // "cache slot is populated" assertion, negated): a memoized global
    // would have its slot populated after the first force; this one must
    // NOT, so a second force still re-executes rather than reading a
    // stale cached value.
    assert!(cache.get(0).is_none());
    force_global(0, &globals, &natives, &mut cache).unwrap();
  }

  /// The sibling of the test above, for the shape that actually
  /// regressed. `def Bench.now : IO I64 := current_time` has a BODY, so
  /// it lowers to a `Def`-like slot rather than `Native` — the
  /// native-only check above never sees it, and it memoized. Every
  /// `--verbose` stage timing the compiler printed collapsed to one
  /// constant, because each `Bench.now` answered from cache.
  ///
  /// The test above cannot catch this: it hand-builds a
  /// `GlobalDef::Native` table, which is precisely the case that was
  /// already handled. This one wraps the native in a slot with a real
  /// body, exactly as `lower_program` does for an `IO`-typed zero-arity
  /// def.
  #[test]
  fn test_zero_arity_io_def_wrapping_a_native_is_not_memoized() {
    // Slot 0: the effectful wrapper, body = `global 1`. Slot 1: the
    // bodyless native it defers to.
    let globals = GlobalTable::new(vec![
      GlobalDef::Effect(std::sync::Arc::new(core_ir::global(1))),
      GlobalDef::Native {
        native_id: 0,
        arity: 0,
      },
    ]);
    let natives = NativeTable::new(
      vec![crate::term::id("current_time")],
      vec![0],
      crate::lower_core_ir::WellKnownCtors {
        io_io: Some(crate::lower_core_ir::CtorTag { tag: 0, arity: 1 }),
        ..Default::default()
      },
    );
    let mut cache = GlobalCache::new(2);
    force_global(0, &globals, &natives, &mut cache).unwrap();
    // The whole point: the wrapper's slot must stay empty, so the next
    // reference performs the effect again instead of replaying this one.
    assert!(cache.get(0).is_none());
    force_global(0, &globals, &natives, &mut cache).unwrap();
    assert!(cache.get(0).is_none());
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

  #[test]
  fn test_tail_recursive_countdown_survives_a_million_iterations_on_default_stack() {
    // The direct proof of self-hosted-compiler-perf.md Step 3's fix:
    // a self-recursive `Global` closure shaped like an ordinary
    // accumulator-style `.mo` loop --
    //   countdown n acc = if n == 0 then acc else countdown (n-1) (acc+1)
    // -- driven to a large N, run under whatever stack size this test
    // binary's own thread already has (no `thread::Builder` stack
    // override, unlike the 64MB worker-thread pattern `lib.rs` uses as a
    // backstop for genuinely non-tail-recursive code). Before this fix,
    // `bench/scope_lookup.mo` stack-overflowed at n≈1000 even under 64MB
    // stacks -- every tail call grew the native Rust stack by a frame.
    // `i64_eq`/`i64_sub`/`i64_add` are wired as ordinary named natives
    // (arbitrary small ids/tags local to this test, not the real
    // dispatch table's) purely to drive the loop's termination check and
    // accumulator update without needing a real inductive `Bool`.
    use crate::core_ir::IrLit;
    use crate::lower_core_ir::{CtorTag, WellKnownCtors};
    use crate::term::id;

    let natives = NativeTable::new(
      vec![id("i64_eq"), id("i64_sub"), id("i64_add")],
      vec![2, 2, 2],
      WellKnownCtors {
        bool_true: Some(CtorTag { tag: 0, arity: 0 }),
        bool_false: Some(CtorTag { tag: 1, arity: 0 }),
        ..Default::default()
      },
    );

    // \n -> \acc ->
    //   match (i64_eq n 0) {
    //     [tag 0, true]  => acc
    //     [tag 1, false] => Global(0) (i64_sub n 1) (i64_add acc 1)
    //   }
    // Local(0) = acc (innermost), Local(1) = n, inside the body -- same
    // De Bruijn convention `test_k_combinator_closure_captures_correct_
    // binding` above already relies on. Both arms bind 0 fields (`Bool`
    // constructors are nullary), so the match doesn't shift indices.
    let body = core_ir::lam(core_ir::lam(core_ir::match_(
      core_ir::ntv(0, vec![core_ir::local(1), num(0)]),
      vec![
        core_ir::arm(0, core_ir::local(0)),
        core_ir::arm(
          0,
          core_ir::app(
            core_ir::app(
              core_ir::global(0),
              core_ir::ntv(1, vec![core_ir::local(1), num(1)]),
            ),
            core_ir::ntv(2, vec![core_ir::local(0), num(1)]),
          ),
        ),
      ],
    )));
    let globals = GlobalTable::new(vec![GlobalDef::Def(std::sync::Arc::new(body))]);
    let mut cache = GlobalCache::new(1);
    let countdown = force_global(0, &globals, &natives, &mut cache).unwrap();

    let n: i64 = 1_000_000;
    let with_n = apply(
      countdown,
      Value::Lit(IrLit::Num(n, NumSuffix::I64)),
      &globals,
      &natives,
      &mut cache,
    )
    .unwrap();
    let result = apply(
      with_n,
      Value::Lit(IrLit::Num(0, NumSuffix::I64)),
      &globals,
      &natives,
      &mut cache,
    )
    .unwrap();
    assert!(matches!(result, Value::Lit(IrLit::Num(v, _)) if v == n));
  }
}
