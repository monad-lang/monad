/// The browser runtime for an Oak `Program`: mount, dispatch, tick.
///
/// The app owns three `#[export "c"]` thunks that call these:
///
///     oak_mount                 -> Runtime.mount init view
///     oak_dispatch_event(id)    -> Runtime.dispatch decode id
///     oak_tick                  -> Runtime.tick program host
///
/// and the state they share travels through `web_wasm.Keep` (the export ABI
/// is i64 words, so no Monad value can be an argument or a return).
///
/// The batch fold is written HERE, monomorphically over `IO`, rather than
/// instantiating `oak/src/app.mo`'s `Program.run_batch [Monad N]`: a compiled
/// dictionary call is exactly the open Phase 0 miscompile class
/// (`2026-10-18-compiled-constrained-generic-dict-call-miscompiles`). It
/// reuses the unconstrained accessors (`Program.init/step/view`,
/// `Host.run_effect`) and mirrors `run_batch`'s semantics line for line.
///
/// One batch per `oak_tick` (one animation frame): dispatch queues messages,
/// tick drains them, folds, re-renders, and patches the DOM.
use std::ref {Ref, Ref.get, Ref.set, Ref.update}
use xml_html::html {Html.Node}
use oak::app {Command, Host, Host.run_effect, Program, Program.step, Program.view}
use web_wasm::dom {Dom.root}
use web_wasm::keep {Keep.load, Keep.save}
use web_wasm::types {Node}
use lib::patch {Patch.diff, Patch.apply, Patch.hydrate_root}

pub type RuntimeState (S : Type) (Msg : Type) {
    st (root : Node) (last : Html.Node) (model : S) (queue : List Msg) (stopped : Bool)
}

/// Mount `view init` under the root the loader selected, and hand the state
/// to the next export call.
///
/// The container's server-rendered tree is ADOPTED when it matches (same
/// node types/tags, in order), so node state survives the first paint; on a
/// mismatch the container is cleared and the view mounted. The contract:
/// the container holds the SSR view root and nothing else, from an explicit
/// selector, and the markup is the serializer's exact output (no added
/// whitespace -- `Patch.hydrate` matches `childNodes` positionally).
pub def Runtime.mount {S : Type} {Msg : Type} (init : S) (view : S -> Html.Node) : IO Unit := do {
    let root <- Dom.root;
    let tree := view init;
    let _ <- Patch.hydrate_root root tree;
    let state : Ref (RuntimeState S Msg) <- Ref.new (RuntimeState.st root tree init List.empty false);
    let _ <- Keep.save state;
    return unit
}

/// Queue one message decoded from a DOM handler id.
pub def Runtime.dispatch {S : Type} {Msg : Type} (decode : I64 -> Option Msg) (handler : I64) : IO Unit := do {
    let state <- Runtime.load_state;
    match decode handler {
        Option.none => IO.pure unit,
        Option.some msg => do {
            let _ <- Ref.update state (Runtime.enqueue msg);
            return unit
        },
    }
}

/// Append, not cons: events arrive in order and a frame must fold them in
/// that order (`motes/oak/src/tests/app_tests.mo`'s `test_message_order`
/// pins FIFO for a batch). Consing reversed every pair of clicks that
/// landed in one frame.
def Runtime.enqueue {S : Type} {Msg : Type} (msg : Msg) (state : RuntimeState S Msg) : RuntimeState S Msg :=
    match state {
        RuntimeState.st root last model queue stopped =>
            RuntimeState.st root last model (List.append queue (List.cons msg List.empty)) stopped,
    }

/// One frame: drain the queue, fold it, re-render and patch. A no-op when
/// nothing was dispatched, and after `Command.quit`, so the rAF loop costs
/// one comparison per frame.
pub def Runtime.tick {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg) : IO Unit := do {
    let state <- Runtime.load_state;
    let snapshot <- Ref.get state;
    match snapshot {
        RuntimeState.st root last model queue stopped =>
            if stopped
            then IO.pure unit
            else if List.is_empty queue
            then IO.pure unit
            else Runtime.drain prog host state root last model queue,
    }
}

def Runtime.drain {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg) (state : Ref (RuntimeState S Msg))
    (root : Node) (last : Html.Node) (model : S) (queue : List Msg) : IO Unit := do {
    // Clear the queue first: a message dispatched while the batch runs lands
    // in the NEXT frame. The final write below reads the queue back so it is
    // not overwritten.
    let drained : RuntimeState S Msg := RuntimeState.st root last model List.empty false;
    let _ <- Ref.set state drained;
    let folded <- Runtime.run_batch prog host model queue;
    match folded {
        Pair.pair next_model quit => do {
            let tree := Program.view prog next_model;
            let patches := Patch.diff last tree;
            let _ <- Patch.apply root patches;
            let current <- Ref.get state;
            let pending := Runtime.pending_of current;
            let next : RuntimeState S Msg := RuntimeState.st root tree next_model pending quit;
            let _ <- Ref.set state next;
            return unit
        },
    }
}

/// The messages dispatched while the batch ran.
def Runtime.pending_of {S : Type} {Msg : Type} (state : RuntimeState S Msg) : List Msg :=
    match state {
        RuntimeState.st _root _last _model queue _stopped => queue,
    }

/// The state slot, typed for the caller. `Keep.load` is generic because the
/// slot is one opaque word; the annotation here is what pins it.
def Runtime.load_state {S : Type} {Msg : Type} : IO (Ref (RuntimeState S Msg)) :=
    Keep.load

// ─── The monomorphic IO fold (mirrors oak/src/app.mo) ─────────────────

pub def Runtime.run_batch {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg) (model : S) (msgs : List Msg) : IO (Pair S Bool) :=
    Runtime.run_pending prog host model msgs

#[terminating]
def Runtime.run_pending {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg) (model : S) (msgs : List Msg) : IO (Pair S Bool) := do {
    let stepped <- Runtime.step_batch prog host model msgs;
    Runtime.run_stepped prog host stepped
}

#[terminating]
def Runtime.run_stepped {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg)
    (stepped : Pair (Pair S Bool) (List Msg)) : IO (Pair S Bool) :=
    match stepped {
        Pair.pair inner pending => Runtime.run_result prog host inner pending,
    }

#[terminating]
def Runtime.run_result {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg)
    (inner : Pair S Bool) (pending : List Msg) : IO (Pair S Bool) :=
    match inner {
        Pair.pair model quit =>
            if quit then IO.pure (Pair.pair model true)
            else if List.is_empty pending then IO.pure (Pair.pair model false)
            else Runtime.run_pending prog host model pending,
    }

#[terminating]
def Runtime.step_batch {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg) (model : S) (msgs : List Msg)
    : IO (Pair (Pair S Bool) (List Msg)) := match msgs {
    List.empty => IO.pure (Pair.pair (Pair.pair model false) List.empty),
    List.cons msg rest => Runtime.step_msg prog host model rest (Program.step prog model msg),
}

#[terminating]
def Runtime.step_msg {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg) (model : S) (rest : List Msg)
    (stepped : Pair S (Command E Msg)) : IO (Pair (Pair S Bool) (List Msg)) :=
    match stepped {
        Pair.pair next_model cmd => Runtime.step_cmd prog host next_model rest cmd,
    }

#[terminating]
def Runtime.step_cmd {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg) (model : S) (rest : List Msg)
    (cmd : Command E Msg) : IO (Pair (Pair S Bool) (List Msg)) :=
    match cmd {
        Command.none => Runtime.step_batch prog host model rest,
        Command.quit => IO.pure (Pair.pair (Pair.pair model true) List.empty),
        Command.dispatch msg => do {
            let stepped <- Runtime.step_batch prog host model rest;
            match stepped {
                Pair.pair inner pending => return (Pair.pair inner (List.cons msg pending)),
            }
        },
        Command.perform effect => do {
            let produced <- Host.run_effect host effect;
            match produced {
                Option.some msg => Runtime.step_batch prog host model (List.cons msg rest),
                Option.none => Runtime.step_batch prog host model rest,
            }
        },
    }
