// Phase 10 table tests: TuiT over a MOCK terminal -- everything runs
// PURE, no raw mode, no tty, no IO.
//
// The base monad is a hand-rolled writer (`MockM`, the
// examples/state_monad.mo shape: single-param type + hand-written
// `Monad` instance, a head the evaluator actually dispatches). The
// plan's sketch stacked `StateT` here; that proof was originally
// DEFERRED on `StateT`'s own bind half ("a known-unexercised lowering
// bug"), but `test_statet_bind` in init/src/transformers_tests.mo now
// passes with the checker's dictionary-resolution fixes -- stacking
// `TuiT (StateT S IO)` is unblocked future work, and `MockM` keeps its
// place regardless: it exercises the same claim (TuiT over an
// arbitrary `Monad M` that is not IO) and doubles as the observation
// channel -- the mock's `write` and `set_mode` append to the log, so
// every test asserts the exact sequence of terminal actions a program
// performed.

use lib::core {empty_screen, mk_rect}
use lib::render {render}
use lib::terminal {Terminal.cursor_show_code, Terminal.leave_alt_screen_code, Terminal.reset_style_code}
use lib::tuit {Closed, Cooked, Raw, Term, TuiT, screen_repaint}
use lib::types {Screen}
use lib::widget {label}
use std::list {List.length}

// ==================== the mock base monad ====================

/// A writer monad specialized to a `List String` log (entries in
/// chronological order: `bind` appends).
type MockM A {
    mock_m (log : List String) (a : A)
}

def mock_pure {A : Type} (a : A) : MockM A :=
    MockM.mock_m List.empty a

/// The bind step, one match per `MockM` instantiation (the
/// nested-match lowering limitation): this def only matches the
/// CONTINUATION's monad.
def mock_bind_run {A : Type} {B : Type} (f : A -> MockM B) (log : List String) (a : A) : MockM B :=
    match f a {
        MockM.mock_m log2 b => MockM.mock_m (List.append log log2) b
    }

pub instance Monad MockM {
    def pure (a : A) : MockM A := mock_pure a
    def bind (ma : MockM A) (f : A -> MockM B) : MockM B :=
        match ma {
            mock_m log a => mock_bind_run f log a
        }
}

/// Run a `MockM` computation, keeping only the log.
def mock_log {A : Type} (m : MockM A) : List String :=
    match m {
        MockM.mock_m log _ => log
    }

// ==================== the mock terminal ====================

/// The write channel: one log entry.
def mock_write (s : String) : MockM Unit :=
    MockM.mock_m (List.cons s List.empty) Unit.unit

/// The mode channel: log `"raw"`/`"cooked"` so a test can pin the
/// lifecycle order, and report success.
def mock_set_mode (raw : Bool) : MockM Bool :=
    MockM.mock_m (List.cons (if raw then "raw" else "cooked") List.empty) true

def mock_term : Term MockM :=
    Term.term (mock_pure (Pair.pair 4 20)) (fn (_ : I64) => mock_pure false) mock_write mock_set_mode

// ==================== helpers ====================

def strs_be (a : List String) (b : List String) : Bool :=
    match a {
        empty => List.length b == 0,
        cons x xs =>
            match b {
                empty => false,
                cons y ys => x == y && strs_be xs ys
            }
    }

def demo_screen : Screen :=
    render (label "hi") (mk_rect 0 0 4 2) (empty_screen 2 4)

/// Outside every do-block and bind argument on purpose: a class-method
/// call (`++` queues an `Append` dict-projection entry) nested inside a
/// `Monad` entry desyncs the checker/lowerer match queue
/// (`MatchTraversalMismatch`) -- a known compiler gap; hoisting is the
/// standing workaround.
def restore_code : String :=
    Terminal.reset_style_code ++ Terminal.leave_alt_screen_code ++ Terminal.cursor_show_code

// ==================== the lifecycle ====================

// Every op value is bound by an ANNOTATED let, and every `prog` keeps
// its declared type: the compiled backend resolves a constrained
// call's `[Monad M]` dictionary from type information alone, and these
// annotations are where it comes from at these call sites -- the
// 0-arg ops (`enter_raw_mode`, `close`) from the binding's own type
// (the checker's expect channel), the `and_then` calls from their
// arguments' bound types (carrier inference, which walks the
// `TuiT M I I` wrapper instance's own `[Monad M]` down to the `MockM`
// leaf). An inline, un-annotated op reference has neither, and the
// self-hosted resolver leaves the call's dictionary unresolved.

/// enter_raw_mode -> draw -> close, the full Cooked..Closed arc: the
/// log pins the exact order (mode, repaint, restore, mode).
#[test]
def test_lifecycle_log : Bool :=
    strs_be (mock_log (TuiT.run prog_lifecycle mock_term))
        ["raw", screen_repaint demo_screen, restore_code, "cooked"]

def prog_lifecycle : TuiT MockM Cooked Closed Unit :=
    let enter : TuiT MockM Cooked Raw Unit := TuiT.enter_raw_mode in
    let paint : TuiT MockM Raw Raw Unit := TuiT.draw demo_screen in
    let bye : TuiT MockM Raw Closed Unit := TuiT.close in
    TuiT.and_then enter (TuiT.and_then paint bye)

/// enter_cooked_mode is the inverse transition: Raw -> Cooked, no
/// restore write (close owns that).
#[test]
def test_cooked_roundtrip : Bool :=
    strs_be (mock_log (TuiT.run prog_roundtrip mock_term)) ["raw", "cooked"]

def prog_roundtrip : TuiT MockM Cooked Cooked Unit :=
    let enter : TuiT MockM Cooked Raw Unit := TuiT.enter_raw_mode in
    let cook : TuiT MockM Raw Cooked Unit := TuiT.enter_cooked_mode in
    TuiT.and_then enter cook

// ==================== the transformer property ====================

/// `TuiT.lift` embeds base-monad actions, and they sequence BETWEEN
/// terminal ops -- the whole point of a transformer.
#[test]
def test_lift_interleaves_with_ops : Bool :=
    strs_be (mock_log (TuiT.run prog_lifted mock_term))
        ["before", screen_repaint demo_screen, "after"]

def prog_lifted : TuiT MockM Raw Raw Unit :=
    let before : TuiT MockM Raw Raw Unit := TuiT.lift (mock_write "before") in
    let paint : TuiT MockM Raw Raw Unit := TuiT.draw demo_screen in
    let after : TuiT MockM Raw Raw Unit := TuiT.lift (mock_write "after") in
    TuiT.and_then before (TuiT.and_then paint after)

/// The equal-index `Monad (TuiT M I I)` bridge: do-notation over
/// `TuiT MockM Raw Raw` dispatches to the hand-written instance, and
/// the bound value (the mock's 4x20 size) flows through.
#[test]
def test_do_notation_at_equal_indices : Bool :=
    size_ok (TuiT.run prog_bridged mock_term)

def prog_bridged : TuiT MockM Raw Raw (Pair I64 I64) := do {
    let sz <- TuiT.size;
    return sz
}

/// One match per type (the nested-match lowering limitation):
/// `size_ok` matches `MockM (Pair I64 I64)`; the inner pair gets its
/// own def.
def size_ok (m : MockM (Pair I64 I64)) : Bool :=
    match m {
        MockM.mock_m log sz => strs_be log [] && dims_ok sz
    }

def dims_ok (sz : Pair I64 I64) : Bool :=
    match sz {
        Pair.pair rows cols => rows == 4 && cols == 20
    }

/// `IndexedMonad.map` preserves indices (Raw stays Raw), via the
/// instance method rather than the wrapper def. The call needs its own
/// declared-type def, like every other prog here: the instance's
/// `[Monad M]` dictionary argument resolves from the call's own
/// type-level information, and for an INLINE call that information
/// only becomes available in a later sibling argument (`mock_term`
/// here) -- the checker's desugar pass re-derives types left-to-right
/// with fresh metas and never looks back, a recorded compiler gap.
/// A declared type pins the base monad up front (the peek at the
/// method's return type), and resolution goes through.
def prog_mapped : TuiT MockM Raw Raw I64 :=
    IndexedMonad.map (fn (p : Pair I64 I64) => 4) TuiT.size

#[test]
def test_indexed_monad_map : Bool :=
    match TuiT.run prog_mapped mock_term {
        MockM.mock_m log n => strs_be log [] && n == 4
    }
