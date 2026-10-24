// Terminal UI Library - the TuiT monad transformer (Phase 10)
//
// `TuiT M I J A` is a terminal-effect transformer over any base monad
// `M`, with the terminal lifecycle tracked by phantom type indices:
// `enter_raw_mode` is `TuiT M Cooked Raw Unit`, so "draw without
// entering raw mode" does not type-check, and `close` ends at `Closed`
// so nothing runs after it. The indices are the same trick as
// shuttle's `Agent` (motes/shuttle/src/agent.mo) and the plan's §2
// sketch; the payload is the same too: `Term M -> M A`, where `Term M`
// is the terminal as FOUR CLOSURES over `M` -- size, poll, write,
// set_mode -- so a test mock is a `Term (StateT (List String) Id)` and
// `Term.io` is the real one.
//
// v1 shape deviations from the plan's sketch, recorded so they are
// decisions, not drift:
//   * The lifecycle markers are phantom TYPES (`Cooked`/`Raw`/
//     `Closed`, below), not constructors of a `TerminalState` enum --
//     an enum index is a kind error, the exact lesson agent-skills
//     Phase 5 baked in as workaround 1 (and the plan's own §2 points
//     at the same verified-state notes).
//   * The capability record is `Term M`, not `Terminal M`: terminal.mo
//     already owns the `Terminal` namespace (the term_ctl wrappers),
//     and a type cannot share it.
//   * `read_event (timeout)` is deferred: the reader (input.mo) is
//     native-backed and IO-typed, so v1 exposes `TuiT.size`/`TuiT.poll`
//     passthroughs instead; `run_app` (tui.mo) stays the live
//     event-reading loop, and `TuiT.lift` embeds an `Input.produce`
//     call for the `TuiT IO` case.
//   * `draw (screen)` paints a FULL repaint (every non-blank cell
//     against a blank screen of the same size) -- the same emission
//     `run_app`'s resize path uses. The diff-based fast path belongs
//     to the loop, which owns the previous frame; a stateless op
//     cannot.
//
// Both instances follow the verified precedents exactly: the
// `IndexedMonad` instance spells ALL FIVE methods (an instance missing
// a class default passes checking and fails at runtime), and the
// equal-index `Monad (TuiT M I I)` bridge is hand-written because the
// prelude's generic `{I} [IndexedMonad M] Monad (M I I)` bridge never
// dispatches (its head is a variable -- `KnownInstances` keys on the
// first argument's head).

use lib::core { empty_screen }
use lib::render { apply_deltas, diff }
use lib::types { Screen }
use lib::terminal {
    Terminal.enter_raw_mode, Terminal.leave_raw_mode, Terminal.leave_alt_screen_code,
    Terminal.cursor_show_code, Terminal.poll, Terminal.size
}

/// Phantom lifecycle markers. Empty single-constructor types, not an
/// enum: `TuiT M I J A` indexes with `I : Type`, and a
/// `TerminalState`-style enum in that position is a kind error.
pub type Cooked {}
pub type Raw {}
pub type Closed {}

/// The terminal as four closures over the base monad `M` -- the entire
/// surface TuiT's ops need. Single-constructor `type` (parameterized
/// structs do not parse); the accessors below are its field access.
pub type Term (M : Type -> Type) {
    term (size : M (Pair I64 I64))
        (poll : I64 -> M Bool)
        (write : String -> M Unit)
        (set_mode : Bool -> M Bool)
}

/// A single-constructor `type`, not a `struct`, for the same reason.
pub type TuiT (M : Type -> Type) (I : Type) (J : Type) (A : Type) {
    tui_t (action : Term M -> M A)
}

// ==================== Term: accessors and the IO record ====================

pub def Term.size {M : Type -> Type} (t : Term M) : M (Pair I64 I64) :=
    match t { term s _ _ _ => s }

pub def Term.poll {M : Type -> Type} (t : Term M) (timeout_ms : I64) : M Bool :=
    match t { term _ p _ _ => p timeout_ms }

pub def Term.write {M : Type -> Type} (t : Term M) (s : String) : M Unit :=
    match t { term _ _ w _ => w s }

pub def Term.set_mode {M : Type -> Type} (t : Term M) (raw : Bool) : M Bool :=
    match t { term _ _ _ m => m raw }

/// The flush is part of the write contract: the landed stack's writes
/// are buffered, and an unflushed restore sequence is a lost one.
def io_write_flush (s : String) : IO Unit := do {
    IO.write_stdout s;
    IO.flush_stdout;
    return Unit.unit
}

def io_set_mode (raw : Bool) : IO Bool :=
    if raw then Terminal.enter_raw_mode else Terminal.leave_raw_mode

/// The real terminal: the landed term_ctl stack behind the four
/// closures. Everything else in this file is polymorphic in `M`.
pub def Term.io : Term IO :=
    Term.term Terminal.size Terminal.poll io_write_flush io_set_mode

// ==================== TuiT: the indexed structure ====================

pub def TuiT.run {M : Type -> Type} {I : Type} {J : Type} {A : Type} (ma : TuiT M I J A) (t : Term M) : M A :=
    match ma { TuiT.tui_t action => action t }

pub def TuiT.pure [Monad M] {I : Type} {A : Type} (a : A) : TuiT M I I A :=
    TuiT.tui_t (fn (_ : Term M) => Monad.pure a)

/// The bind step, extracted per the transformers.mo pattern: instance
/// bodies stay single-line, and the step itself is a small def.
def tui_apply [Monad M] {J : Type} {K : Type} {A : Type} {B : Type} (f : A -> TuiT M J K B) (a : A) (t : Term M) : M B :=
    TuiT.run (f a) t

/// `bind` reaches `Monad` through `tui_apply`; the see-through table
/// (`qualifying_dict_constraints`, lang/src/scope.mo) marks this def and
/// the call site forwards its own `[Monad M]` binding.
pub def TuiT.bind [Monad M] {I : Type} {J : Type} {K : Type} {A : Type} {B : Type} (ma : TuiT M I J A) (f : A -> TuiT M J K B) : TuiT M I K B :=
    TuiT.tui_t (fn (t : Term M) => Monad.bind (TuiT.run ma t) (fn (a : A) => tui_apply f a t))

/// `TuiT.pure (f a)` would read naturally here, but a call to a
/// constrained def nested inside another constrained call's lambda gets
/// its forwarded dictionary as `Term.var 0` (`resolve_dict_arg`,
/// lang/src/scope.mo) -- index 0 is the lambda's own binder, not the
/// def's `__dict_Monad` -- so it must stay spelled inline until that
/// insertion computes the enclosing call's real depth.
pub def TuiT.map [Monad M] {I : Type} {J : Type} {A : Type} {B : Type} (f : A -> B) (ma : TuiT M I J A) : TuiT M I J B :=
    TuiT.bind ma (fn (a : A) => TuiT.tui_t (fn (_ : Term M) => Monad.pure (f a)))

pub def TuiT.and_then [Monad M] {I : Type} {J : Type} {K : Type} {A : Type} {B : Type} (first : TuiT M I J A) (second : TuiT M J K B) : TuiT M I K B :=
    TuiT.bind first (fn (_ : A) => second)

/// The full `IndexedMonad` structure, ALL five methods explicit -- an
/// instance that silently inherits a class default passes checking and
/// fails at runtime (the lesson the plan and agent-skills both record).
pub instance [Monad M] IndexedMonad (TuiT M) {
    def pure (a : A) : TuiT M I I A := TuiT.pure a
    def bind (ma : TuiT M I J A) (f : A -> TuiT M J K B) : TuiT M I K B := TuiT.bind ma f
    def map (f : A -> B) (ma : TuiT M I J A) : TuiT M I J B := TuiT.map f ma
    def and_then (first : TuiT M I J A) (second : TuiT M J K B) : TuiT M I K B := TuiT.and_then first second
    def lift (a : A) : TuiT M I I A := TuiT.pure a
}

/// Do-notation at equal indices. Hand-written concrete instance -- the
/// prelude's generic `{I} [IndexedMonad M] Monad (M I I)` bridge never
/// dispatches (variable head), exactly the `Agent` precedent.
pub instance [Monad M] Monad (TuiT M I I) {
    def pure (a : A) : TuiT M I I A := TuiT.pure a
    def bind (ma : TuiT M I I A) (f : A -> TuiT M I I B) : TuiT M I I B := TuiT.bind ma f
}

// ==================== TuiT: the terminal ops ====================

/// Run a base-monad action without touching the terminal.
pub def TuiT.lift [Monad M] {I : Type} {A : Type} (m : M A) : TuiT M I I A :=
    TuiT.tui_t (fn (_ : Term M) => m)

/// Discard a capability's `Bool` payload (`set_mode` reports success;
/// the type-level lifecycle is the record that matters).
def tui_discard_bool [Monad M] (m : M Bool) : M Unit :=
    Monad.bind m (fn (_ : Bool) => Monad.pure Unit.unit)

/// Cooked -> Raw. The mode change itself is the transition; the
/// return code is discarded (the index now says raw).
pub def TuiT.enter_raw_mode [Monad M] : TuiT M Cooked Raw Unit :=
    TuiT.tui_t (fn (t : Term M) => tui_discard_bool (Term.set_mode t true))

/// Raw -> Cooked: the inverse transition.
pub def TuiT.enter_cooked_mode [Monad M] : TuiT M Raw Cooked Unit :=
    TuiT.tui_t (fn (t : Term M) => tui_discard_bool (Term.set_mode t false))

/// The terminal size, inside the effect.
pub def TuiT.size [Monad M] : TuiT M Raw Raw (Pair I64 I64) :=
    TuiT.tui_t Term.size

/// Poll for input within `timeout_ms` (negative blocks) -- the v1
/// stand-in for the plan's `read_event`, which the native-backed
/// reader (input.mo) cannot yet provide generically over `M`.
pub def TuiT.poll [Monad M] (timeout_ms : I64) : TuiT M Raw Raw Bool :=
    TuiT.tui_t (fn (t : Term M) => Term.poll t timeout_ms)

/// A full repaint of `screen`: every non-blank cell against a blank
/// screen of the same size, the emission `run_app`'s resize path uses.
/// The diff-based fast path needs the previous frame and stays with
/// the loop (tui.mo); a stateless op can only paint whole.
def screen_repaint (screen : Screen) : String :=
    apply_deltas (diff (empty_screen screen.rows screen.cols) screen)

/// Paint `screen`.
pub def TuiT.draw [Monad M] (screen : Screen) : TuiT M Raw Raw Unit :=
    TuiT.tui_t (fn (t : Term M) => Term.write t (screen_repaint screen))

/// The restore handshake: leave the alternate screen, bring the
/// cursor back, and return to cooked mode. `Closed` is a one-way
/// index -- nothing in this module runs after it.
pub def TuiT.close [Monad M] : TuiT M Raw Closed Unit :=
    TuiT.tui_t (fn (t : Term M) => tui_close_go t)

/// Outside the `Monad.bind` argument on purpose: a class-method call
/// (`++` queues an `Append` dict-projection entry) inside another
/// class-method call's argument (`Monad.bind` queues a `Monad` entry)
/// desyncs the checker/lowerer match queue (`MatchTraversalMismatch`)
/// -- the two traversals visit the nested call in opposite order.
/// Hoisting is the standing workaround; `restore_terminal` in tui.mo
/// keeps its own copy only because that file has no `bind` to clash
/// with.
def tui_close_code : String :=
    Terminal.leave_alt_screen_code ++ Terminal.cursor_show_code

def tui_close_go [Monad M] (t : Term M) : M Unit :=
    Monad.bind (Term.write t tui_close_code)
        (fn (_ : Unit) => tui_discard_bool (Term.set_mode t false))
