/// The browser runtime for an Oak `Program`: mount, dispatch, tick.
///
/// The app owns three `#[export "c"]` thunks that call these:
///
///     oak_mount                 -> Runtime.mount program
///     oak_dispatch_event(id)    -> Runtime.dispatch id
///     oak_tick                  -> Runtime.tick program host
///
/// The event id is assigned by `Oak.lower` (path + event name) and baked into
/// the lowered attribute. `Runtime.dispatch` looks it up in the pure handler
/// table, snapshots the live event into an `WebEvent`, runs the pure handler and
/// applies the `preventDefault`/`stopPropagation` it asks for. There is no
/// user decoder and no IO in the view or update.
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
use web_event::event {WebEvent, HandlerResult, ListenerFlags}
use oak::app {
    Command, Host, Host.run_effect, Program, Program.init, Program.step, Program.view,
    Program.subscriptions,
}
use oak::typed {Oak.Node, Oak.Lowered, Oak.lower, Handler.id, Handler.spec_of}
use oak::events {Subscription}
use web_wasm::dom {
    Dom.root, Dom.on_window, Dom.on_document, Dom.on_frame,
    Dom.off_window, Dom.off_document, Dom.off_frame,
}
use web_wasm::event {WebEvent.current, WebEvent.prevent_default, WebEvent.stop_propagation}
use web_wasm::keep {Keep.load, Keep.save}
use web_wasm::types {Node}
use lib::patch {Patch.diff, Patch.apply, Patch.hydrate_root}

// ═══ Subscriptions ═══
//
// A subscription is a pure declarative request (`Subscription`) for a window,
// document or animation-frame listener. The runtime diffs the list by key
// (target + event) after every batch and registers/unregisters the
// difference; the handlers themselves live in the dispatch table under a
// path-like id.

#[terminating]
def Runtime.sub_key {Msg : Type} (sub : Subscription Msg) : String :=
    match sub {
        Subscription.none => "",
        Subscription.window event _handler => String.concat "window:" event,
        Subscription.document event _handler => String.concat "document:" event,
        Subscription.animation_frame _handler => "frame",
    }

def Runtime.window_spec (event : String) : String :=
    Handler.spec_of (Handler.id List.empty (String.concat "window:" event)) ListenerFlags.none

def Runtime.document_spec (event : String) : String :=
    Handler.spec_of (Handler.id List.empty (String.concat "document:" event)) ListenerFlags.none

def Runtime.frame_spec : String :=
    Handler.spec_of (Handler.id List.empty "frame") ListenerFlags.none

pub def Runtime.install_sub {Msg : Type} (sub : Subscription Msg) : IO Unit :=
    match sub {
        Subscription.none => IO.pure unit,
        Subscription.window event _handler => Dom.on_window event (Runtime.window_spec event),
        Subscription.document event _handler => Dom.on_document event (Runtime.document_spec event),
        Subscription.animation_frame _handler => Dom.on_frame Runtime.frame_spec,
    }

pub def Runtime.remove_sub {Msg : Type} (sub : Subscription Msg) : IO Unit :=
    match sub {
        Subscription.none => IO.pure unit,
        Subscription.window event _handler => Dom.off_window event,
        Subscription.document event _handler => Dom.off_document event,
        Subscription.animation_frame _handler => Dom.off_frame,
    }

/// Install only the subscriptions whose key is not already applied.
#[terminating]
def Runtime.install_added {Msg : Type} (old : List (Subscription Msg)) (new : List (Subscription Msg)) : IO Unit :=
    match new {
        List.empty => IO.pure unit,
        List.cons sub rest =>
            if Runtime.key_in (Runtime.sub_key sub) old
            then Runtime.install_added old rest
            else do {
                let _ <- Runtime.install_sub sub;
                Runtime.install_added old rest
            },
    }

#[terminating]
def Runtime.key_in {Msg : Type} (key : String) (subs : List (Subscription Msg)) : Bool :=
    match subs {
        List.empty => false,
        List.cons sub rest =>
            if String.beq key (Runtime.sub_key sub) then true else Runtime.key_in key rest,
    }

#[terminating]
def Runtime.remove_stale {Msg : Type} (old : List (Subscription Msg)) (new : List (Subscription Msg)) : IO Unit :=
    match old {
        List.empty => IO.pure unit,
        List.cons sub rest =>
            if Runtime.key_in (Runtime.sub_key sub) new
            then Runtime.remove_stale rest new
            else do {
                let _ <- Runtime.remove_sub sub;
                Runtime.remove_stale rest new
            },
    }

pub def Runtime.apply_subs {Msg : Type} (old : List (Subscription Msg)) (new : List (Subscription Msg)) : IO Unit := do {
    let _ <- Runtime.install_added old new;
    Runtime.remove_stale old new
}

def Runtime.sub_handler {Msg : Type} (sub : Subscription Msg)
    : List (Pair U32 (WebEvent -> HandlerResult Msg)) :=
    match sub {
        Subscription.none => List.empty,
        Subscription.window event handler =>
            List.cons
                (Pair.pair (Handler.id List.empty (String.concat "window:" event))
                    (fn (e : WebEvent) => HandlerResult.msg (handler e)))
                List.empty,
        Subscription.document event handler =>
            List.cons
                (Pair.pair (Handler.id List.empty (String.concat "document:" event))
                    (fn (e : WebEvent) => HandlerResult.msg (handler e)))
                List.empty,
        Subscription.animation_frame handler =>
            List.cons
                (Pair.pair (Handler.id List.empty "frame")
                    (fn (e : WebEvent) => HandlerResult.msg (handler e)))
                List.empty,
    }

#[terminating]
def Runtime.collect_sub_handlers {Msg : Type} (subs : List (Subscription Msg))
    : List (Pair U32 (WebEvent -> HandlerResult Msg)) :=
    match subs {
        List.empty => List.empty,
        List.cons sub rest =>
            List.append (Runtime.sub_handler sub) (Runtime.collect_sub_handlers rest),
    }

pub type RuntimeState (S : Type) (Msg : Type) {
    st (root : Node) (last : Html.Node) (model : S)
       (queue : List Msg) (stopped : Bool)
       (handlers : List (Pair U32 (WebEvent -> HandlerResult Msg)))
       (subs : List (Subscription Msg))
}

/// Mount a `Program` under the root the loader selected, and hand the state
/// to the next export call. Initial subscriptions are registered before the
/// first render.
///
/// The container's server-rendered tree is ADOPTED when it matches (same
/// node types/tags, in order), so node state survives the first paint; on a
/// mismatch the container is cleared and the view mounted. The contract:
/// the container holds the SSR view root and nothing else, from an explicit
/// selector, and the markup is the serializer's exact output (no added
/// whitespace -- `Patch.hydrate` matches `childNodes` positionally).
pub def Runtime.mount {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) : IO Unit := do {
    let root <- Dom.root;
    let model := Program.init prog;
    let subs := (Program.subscriptions prog) model;
    let _ <- Runtime.apply_subs List.empty subs;
    match Oak.lower (Program.view prog model) {
        Oak.Lowered.lowered tree handlers => do {
            let _ <- Patch.hydrate_root root tree;
            let table := List.append handlers (Runtime.collect_sub_handlers subs);
            let state : Ref (RuntimeState S Msg) <-
                Ref.new (RuntimeState.st root tree model List.empty false table subs);
            let _ <- Keep.save state;
            return unit
        },
    }
}

/// Queue the message the handler registered for `id` produces.
///
/// The id is looked up in the handler table collected by the last render; the
/// live event is snapshotted while the browser is still dispatching, so the
/// pure handler sees a complete `WebEvent`.
pub def Runtime.dispatch {S : Type} {Msg : Type} (handler : I64) : IO Unit := do {
    let state <- Runtime.load_state;
    let snapshot <- Ref.get state;
    match snapshot {
        RuntimeState.st _root _last _model _queue stopped handlers _subs =>
            if stopped
            then IO.pure unit
            else
                match Runtime.lookup_handler (I64.to_u32 handler) handlers {
                    Option.none => IO.pure unit,
                    Option.some handler_fn => do {
                        let ev <- WebEvent.current;
                        let outcome := handler_fn ev;
                        match outcome {
                            HandlerResult.handler_result msg prevent stop => do {
                                let _ <- if prevent then WebEvent.prevent_default else IO.pure unit;
                                let _ <- if stop then WebEvent.stop_propagation else IO.pure unit;
                                match msg {
                                    Option.some m => do {
                                        let _ <- Ref.update state (Runtime.enqueue m);
                                        return unit
                                    },
                                    Option.none => IO.pure unit,
                                }
                            },
                        }
                    },
                },
    }
}

#[terminating]
def Runtime.lookup_handler {Msg : Type} (id : U32)
    (handlers : List (Pair U32 (WebEvent -> HandlerResult Msg)))
    : Option (WebEvent -> HandlerResult Msg) :=
    match handlers {
        List.empty => Option.none,
        List.cons entry rest =>
            match entry {
                Pair.pair key handler_fn =>
                    if U32.beq key id then Option.some handler_fn else Runtime.lookup_handler id rest,
            },
    }

/// Append, not cons: events arrive in order and a frame must fold them in
/// that order (`motes/oak/src/tests/app_tests.mo`'s `test_message_order`
/// pins FIFO for a batch). Consing reversed every pair of clicks that
/// landed in one frame.
def Runtime.enqueue {S : Type} {Msg : Type} (msg : Msg) (state : RuntimeState S Msg) : RuntimeState S Msg :=
    match state {
        RuntimeState.st root last model queue stopped handlers subs =>
            RuntimeState.st root last model (List.append queue (List.cons msg List.empty))
                stopped handlers subs,
    }

/// One frame: drain the queue, fold it, re-render and patch. A no-op when
/// nothing was dispatched, and after `Command.quit`, so the rAF loop costs
/// one comparison per frame.
pub def Runtime.tick {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg) : IO Unit := do {
    let state <- Runtime.load_state;
    let snapshot <- Ref.get state;
    match snapshot {
        RuntimeState.st root last model queue stopped handlers subs =>
            if stopped
            then IO.pure unit
            else if List.is_empty queue
            then IO.pure unit
            else Runtime.drain prog host state root last model queue handlers subs,
    }
}

def Runtime.drain {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg) (state : Ref (RuntimeState S Msg))
    (root : Node) (last : Html.Node) (model : S) (queue : List Msg)
    (handlers : List (Pair U32 (WebEvent -> HandlerResult Msg))) (subs : List (Subscription Msg)) : IO Unit := do {
    // Clear the queue first: a message dispatched while the batch runs lands
    // in the NEXT frame. The final write below reads the queue back so it is
    // not overwritten.
    let drained : RuntimeState S Msg :=
        RuntimeState.st root last model List.empty false handlers subs;
    let _ <- Ref.set state drained;
    let folded <- Runtime.run_batch prog host model queue;
    match folded {
        Pair.pair next_model quit => do {
            let next_subs := (Program.subscriptions prog) next_model;
            match Oak.lower (Program.view prog next_model) {
                Oak.Lowered.lowered tree next_handlers => do {
                    let table := List.append next_handlers (Runtime.collect_sub_handlers next_subs);
                    // Make the new handlers reachable BEFORE the DOM changes:
                    // a patch can fire an event synchronously (e.g. an
                    // autofocused input), and that event must resolve to the
                    // handler just lowered, not the previous frame's table.
                    let staged : RuntimeState S Msg :=
                        RuntimeState.st root last model List.empty false table next_subs;
                    let _ <- Ref.set state staged;
                    let patches := Patch.diff last tree;
                    let _ <- Patch.apply root patches;
                    let _ <- Runtime.apply_subs subs next_subs;
                    let current <- Ref.get state;
                    let pending := Runtime.pending_of current;
                    let next : RuntimeState S Msg :=
                        RuntimeState.st root tree next_model pending quit table next_subs;
                    let _ <- Ref.set state next;
                    return unit
                },
            }
        },
    }
}

/// The messages dispatched while the batch ran.
def Runtime.pending_of {S : Type} {Msg : Type} (state : RuntimeState S Msg) : List Msg :=
    match state {
        RuntimeState.st _root _last _model queue _stopped _handlers _subs => queue,
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
