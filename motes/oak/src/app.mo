// The abstract model/update/view layer: pure data plus a fold, with no
// runtime attached. A server or wasm host supplies a `Host N E Msg` that
// interprets effects and decides how to render `App.view`; this module
// never assumes either.
//
// Semantics are ported from tui's `step_batch`/`step_cmd`
// (motes/tui/src/tui.mo): `dispatch` queues a message for the next batch,
// `perform` runs the host effect immediately and folds its optional
// message back into the CURRENT batch, and `quit` stops the batch.

use xml_html::html {Html.Node}

// ═══ Types ═══
//
// Single-constructor parameterized `type`s, not structs (parameterized
// structs do not parse). Constructors are reached through the type
// (`Cmd.none`, `Host.host`, `App.app`).

pub type Cmd (E : Type) (Msg : Type) {
    none,
    quit,
    dispatch (msg : Msg),
    perform (effect : E)
}

pub type Host (N : Type -> Type) (E : Type) (Msg : Type) {
    host (run_effect : E -> N (Option Msg))
}

pub type App (S : Type) (Msg : Type) (E : Type) {
    app (init : S)
        (update : S -> Msg -> Pair S (Cmd E Msg))
        (view : S -> Html.Node)
}

// ═══ Accessors ═══
//
// Constrained defs live outside `with` blocks: the block parser does not
// accept a type-class bracket after an inner def's name.

pub def Host.run_effect {N : Type -> Type} {E : Type} {Msg : Type}
    (h : Host N E Msg) (effect : E) : N (Option Msg) :=
    match h { Host.host f => f effect }

with App {
    pub def init {S : Type} {Msg : Type} {E : Type} (a : App S Msg E) : S :=
        match a { App.app s _ _ => s }

    pub def view {S : Type} {Msg : Type} {E : Type} (a : App S Msg E) (s : S) : Html.Node :=
        match a { App.app _ _ v => v s }

    /// The pure `update` projection.
    pub def step {S : Type} {Msg : Type} {E : Type}
        (a : App S Msg E) (s : S) (msg : Msg) : Pair S (Cmd E Msg) :=
        match a { App.app _ update _ => update s msg }
}

/// Fold a batch to quiescence: run it, then drain the messages its
/// `dispatch` commands queued as subsequent batches. Returns the final
/// model and whether `quit` was requested. An update that always
/// dispatches does not terminate; the host owns progress.
pub def App.run_batch [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : App S Msg E) (h : Host N E Msg) (s : S) (msgs : List Msg) : N (Pair S Bool) :=
    run_pending a h s msgs

// ═══ The inner fold ═══
//
// A single batch returns `Pair (Pair S Bool) (List Msg)`: (final model,
// quit?) and the messages dispatched for the next batch. Each def matches
// exactly one constructor; the mutually recursive group is marked
// `#[terminating]` because the recursion is not structural on a subterm.

def queue_dispatched {S : Type} {Msg : Type}
    (d : Msg) (stepped : Pair (Pair S Bool) (List Msg)) : Pair (Pair S Bool) (List Msg) :=
    match stepped {
        Pair.pair inner pending => Pair.pair inner (List.cons d pending)
    }

#[terminating]
def step_msg [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : App S Msg E) (h : Host N E Msg) (model : S) (rest : List Msg)
    (p : Pair S (Cmd E Msg)) : N (Pair (Pair S Bool) (List Msg)) :=
    match p { Pair.pair model2 cmd => step_cmd a h model2 rest cmd }

#[terminating]
def step_batch [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : App S Msg E) (h : Host N E Msg) (model : S) (msgs : List Msg)
    : N (Pair (Pair S Bool) (List Msg)) :=
    match msgs {
        List.empty => Monad.pure (Pair.pair (Pair.pair model false) List.empty),
        List.cons m rest => step_msg a h model rest (App.step a model m)
    }

#[terminating]
def perform_step [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : App S Msg E) (h : Host N E Msg) (model : S) (rest : List Msg)
    (mo : Option Msg) : N (Pair (Pair S Bool) (List Msg)) :=
    match mo {
        Option.some m2 => step_batch a h model (List.cons m2 rest),
        Option.none => step_batch a h model rest
    }

#[terminating]
def step_cmd [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : App S Msg E) (h : Host N E Msg) (model : S) (rest : List Msg)
    (cmd : Cmd E Msg) : N (Pair (Pair S Bool) (List Msg)) :=
    match cmd {
        Cmd.none => step_batch a h model rest,
        Cmd.quit => Monad.pure (Pair.pair (Pair.pair model true) List.empty),
        Cmd.dispatch d =>
            Monad.bind (step_batch a h model rest)
                (fn (stepped : Pair (Pair S Bool) (List Msg)) =>
                    Monad.pure (queue_dispatched d stepped)),
        Cmd.perform effect =>
            Monad.bind (Host.run_effect h effect) (perform_step a h model rest)
    }

// ═══ Draining deferred dispatches ═══

#[terminating]
def run_result [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : App S Msg E) (h : Host N E Msg) (inner : Pair S Bool) (pending : List Msg)
    : N (Pair S Bool) :=
    match inner {
        Pair.pair model quit =>
            if quit
            then Monad.pure (Pair.pair model true)
            else if List.is_empty pending
            then Monad.pure (Pair.pair model false)
            else run_pending a h model pending
    }

#[terminating]
def run_stepped [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : App S Msg E) (h : Host N E Msg)
    (stepped : Pair (Pair S Bool) (List Msg)) : N (Pair S Bool) :=
    match stepped {
        Pair.pair inner pending => run_result a h inner pending
    }

#[terminating]
def run_pending [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : App S Msg E) (h : Host N E Msg) (model : S) (pending : List Msg)
    : N (Pair S Bool) :=
    Monad.bind (step_batch a h model pending)
        (fn (stepped : Pair (Pair S Bool) (List Msg)) => run_stepped a h stepped)
