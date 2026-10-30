//! End-to-end regression tests for the constrained-call dictionary gaps
//! fixed on the self-hosted checker (`lang/src/scope.mo`, PR #76), pinned
//! here on the Rust host so the coverage survives CI's transition to
//! running only the Rust test suite.
//!
//! The four gaps, all diagnosed on
//! `motes/tui/src/tests/tuit_tests.mo`'s compiled segfault
//! (`driver exited -1`) and recorded in
//! `plans/implementations/2026-10-17-compiled-segfault-lambda-class-method-in-constrained-def.md`:
//!
//!   1. the dict ABI: a constrained callee whose body never references
//!      its class must take no dict parameter and no dict argument
//!      (a raw-vs-qualifying constraint mismatch shifted every
//!      parameter left by one and the driver called a dict field as a
//!      function);
//!   2. the expectation channel: a 0-arg constrained op has no value
//!      argument to infer a carrier from, and must resolve its dict
//!      from the annotated binding's own type;
//!   3. the instance registry: an instance whose arg mentions an
//!      undeclared type variable (`Monad (TI M I I)` with no `{I}`
//!      binder) must still match a concrete carrier, or the prelude's
//!      variable-headed bridge (`instance {I} [IndexedMonad M] Monad
//!      (M I I)`) takes the call instead;
//!   4. the dict candidate: the constraint's own still-unresolved
//!      variable is the question, not an answer, and must never be
//!      offered as the carrier a catch-all bridge "matches".
//!
//! The Rust host was green on all of these shapes when the self-hosted
//! checker was not; these tests keep it that way, because the host is
//! the reference the self-hosted compiler is held to and the fallback
//! CI builds with when the nightly-hosted self-compile fails.

use monad_core::eval_core_program;
use monad_core::term::ModulePath;

fn run(name: &str, source: &str) -> monad_core::core_value::Value {
  let path = ModulePath::top(name);
  eval_core_program(&path, source).unwrap_or_else(|e| panic!("eval_core_program failed: {e}"))
}

fn as_i64(v: &monad_core::core_value::Value) -> i64 {
  match v {
    monad_core::core_value::Value::Lit(monad_core::core_ir::IrLit::Num(n, _)) => *n,
    other => panic!("expected an int literal, got {other:?}"),
  }
}

/// Layers 3 and 4: do-notation over `TI MockM Rw Rw`, where BOTH the
/// hand-written wrapper `instance [Monad M] Monad (TI M I I)` (its `I`
/// undeclared) and the prelude's bridge
/// `instance {I} [IndexedMonad M] Monad (M I I)` match the carrier, at
/// equal indices. The bind chain must dispatch through the wrapper and
/// resolve its `[Monad M]` dictionary to `MockM`'s — a checker that
/// picks the bridge (or mints the bridge's dict for the wrapper's
/// methods) misdispatches, and the result 21 (`b * 10 + a`, a=1, b=2)
/// is what only the correct chain produces: a dropped or reordered bind
/// gives 12, 2, or 1, and a failed dispatch fails the check outright.
const EQUAL_INDEX_DO: &str = r#"
use init

type MockM A { mock_m (a : A) }

instance Monad MockM {
    def pure (a : A) : MockM A := MockM.mock_m a
    def bind (ma : MockM A) (f : A -> MockM B) : MockM B :=
        match ma { MockM.mock_m a => f a }
}

type Rw {}
type Term (M : Type -> Type) { term (u : M Unit) }
def Term.unit {M : Type -> Type} (t : Term M) : M Unit := match t { term u => u }
type TI (M : Type -> Type) (I : Type) (J : Type) (A : Type) { ti_mk (action : Term M -> M A) }
def TI.run {M : Type -> Type} {I : Type} {J : Type} {A : Type} (ma : TI M I J A) (t : Term M) : M A :=
    match ma { ti_mk action => action t }

instance [Monad M] IndexedMonad (TI M) {
    def pure (a : A) : TI M I I A := TI.ti_mk (fn (_ : Term M) => Monad.pure a)
    def bind (ma : TI M I J A) (f : A -> TI M J K B) : TI M I K B :=
        TI.ti_mk (fn (t : Term M) => Monad.bind (TI.run ma t) (fn (a : A) => TI.run (f a) t))
}

instance [Monad M] Monad (TI M I I) {
    def pure (a : A) : TI M I I A := TI.ti_mk (fn (_ : Term M) => Monad.pure a)
    def bind (ma : TI M I I A) (f : A -> TI M I I B) : TI M I I B :=
        TI.ti_mk (fn (t : Term M) => Monad.bind (TI.run ma t) (fn (a : A) => TI.run (f a) t))
}

def TI.op [Monad M] (n : I64) : TI M Rw Rw I64 :=
    TI.ti_mk (fn (_ : Term M) => Monad.pure n)

def prog_do : TI MockM Rw Rw I64 :=
    do { let a <- TI.op 1; let b <- TI.op 2; return (b * 10 + a) }

def main : I64 :=
    match TI.run prog_do (Term.term (MockM.mock_m Unit.unit)) {
        MockM.mock_m n => n
    }
"#;

#[test]
fn do_notation_at_equal_indices_dispatches_through_the_wrapper_instance() {
  assert_eq!(as_i64(&run("'equal_index_do", EQUAL_INDEX_DO)), 21);
}

/// Layer 1: a constrained def whose body never references its class
/// (`norefs_step`) must not grow a dict parameter -- and its callers
/// must not prepend one. If either half drifts (the raw constraint list
/// on one side, the qualifying one on the other), every parameter of
/// the callee shifts left by one and evaluation dies on a dict field
/// called as a function. `refs_step` is the qualifying sibling in the
/// same program, proving the shared predicate agrees both ways.
const CONSTRAINED_CALLEE: &str = r#"
use init

class Wrap (M : Type -> Type) { def wrap (m : M A) : M A }
instance Wrap Id { def wrap (m : Id A) : Id A := m }

def refs_step [Wrap M] {A : Type} (m : M A) : M A := Wrap.wrap m
def norefs_step [Wrap M] {B : Type} (m : M B) : M B := m

def main : I64 := Id.run (refs_step (Id.id 20)) + Id.run (norefs_step (Id.id 1))
"#;

#[test]
fn unreferenced_constrained_callee_takes_no_dict_argument() {
  assert_eq!(as_i64(&run("'constrained_callee", CONSTRAINED_CALLEE)), 21);
}

/// Layer 2: a 0-arg constrained op has no argument a carrier could be
/// inferred from; the annotated binding's own type is the one place the
/// source pins it, and the dictionary must resolve from there. A
/// checker that leaves the dict unresolved fails the check; one that
/// emits a closure awaiting the dict evaluates to a function value,
/// not 5.
const ZERO_ARG_OP: &str = r#"
use init

class Mk (M : Type -> Type) { def mk (a : I64) : M I64 }
instance Mk Id { def mk (a : I64) : Id I64 := Id.id a }

def op [Mk M] : M I64 := Mk.mk 5

def main : I64 := let x : Id I64 := op in Id.run x
"#;

#[test]
fn zero_arg_constrained_op_resolves_from_its_binding_type() {
  assert_eq!(as_i64(&run("'zero_arg_op", ZERO_ARG_OP)), 5);
}
