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
    Dom.off_window, Dom.off_document, Dom.off_frame, Dom.focus,
}
use web_wasm::timer {Timer.after, Timer.is_id}
use web_wasm::media {Media.watch, Media.unwatch}
use web_wasm::types {WebSocket}
use web_wasm::websocket {
    WebSocket.connect, WebSocket.close, WebSocket.free, WebSocket.watch, WebSocket.unwatch,
    WebSocket.drain, WebSocket.send,
}
use web_event::websocket {WsData, WsEvent}
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
        Subscription.window_filter event _handler => String.concat "windowf:" event,
        Subscription.media query _handler => String.concat "media:" query,
        Subscription.websocket url protocols _handler =>
            String.concat "ws:" (String.concat url (String.concat "|" (Runtime.join_protocols protocols))),
    }

#[terminating]
def Runtime.join_protocols (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons x rest => Runtime.join_protocols_tail x (Runtime.join_protocols rest)
    }

def Runtime.join_protocols_tail (x : String) (tail : String) : String :=
    if String.beq tail "" then x else String.concat x (String.concat "," tail)

/// The dispatch id a socket's wake-up arrives under: the key's handler hash
/// with its top two bits cleared, offset by the socket base (0x40000000).
/// The result is always in [0x40000000, 0x80000000), the range timers
/// (top bit) never use.
pub def Runtime.socket_base : U32 := 0x40000000u32

pub def Runtime.socket_id (key : String) : U32 :=
    U32.add Runtime.socket_base (U32.and (Handler.id List.empty key) 0x3fffffffu32)

pub def Runtime.is_socket_id (id : U32) : Bool :=
    Bool.and (Bool.not (U32.lt id Runtime.socket_base)) (Bool.not (Timer.is_id id))

def Runtime.window_spec (event : String) : String :=
    Handler.spec_of (Handler.id List.empty (String.concat "window:" event)) ListenerFlags.none

/// A filtered window subscription gets its own key/id space, so switching a
/// `window` subscription to `window_filter` (or back) replaces the listener
/// instead of stacking two.
def Runtime.window_filter_spec (event : String) : String :=
    Handler.spec_of (Handler.id List.empty (String.concat "windowf:" event)) ListenerFlags.none

def Runtime.media_spec (query : String) : String :=
    Handler.spec_of (Handler.id List.empty (String.concat "media:" query)) ListenerFlags.none

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
        Subscription.window_filter event _handler =>
            Dom.on_window event (Runtime.window_filter_spec event),
        Subscription.media query _handler => Media.watch query (Runtime.media_spec query),
        Subscription.websocket url protocols handler => Runtime.install_socket url protocols handler,
    }

/// Open the subscription's socket and start waking the app with its key's
/// dispatch id. A failed connection still installs (the queue reports
/// `failed`), so a later batch sees the event.
def Runtime.install_socket {Msg : Type} (url : String) (protocols : List String)
    (handler : WsEvent -> Msg) : IO Unit := do {
    let ws <- WebSocket.connect url protocols;
    let key := String.concat "ws:" (String.concat url (String.concat "|" (Runtime.join_protocols protocols)));
    let _ <- WebSocket.watch ws (Runtime.socket_id key);
    let state <- Runtime.load_state;
    let _ <- Ref.update state (Runtime.add_socket (WsSocket.ws_socket key url ws handler));
    IO.pure unit
}

def Runtime.add_socket {S : Type} {Msg : Type} (entry : WsSocket Msg)
    (state : RuntimeState S Msg) : RuntimeState S Msg :=
    match state {
        RuntimeState.st root last model queue stopped handlers subs timers focus paint sockets =>
            RuntimeState.st root last model queue stopped handlers subs timers focus paint
                (List.cons entry sockets),
    }

/// A watched socket woke up: drain its queue and enqueue one message per
/// event through the subscription's handler.
def Runtime.dispatch_socket {S : Type} {Msg : Type} (id : I64) (sockets : List (WsSocket Msg)) : IO Unit := do {
    match Runtime.socket_for_id id sockets {
        Option.none => IO.pure unit,
        Option.some pair => match pair {
            Pair.pair ws handler => do {
                let events <- WebSocket.drain ws;
                let state <- Runtime.load_state;
                let _ <- Ref.update state (Runtime.enqueue_events handler events);
                IO.pure unit
            }
        }
    }
}

#[terminating]
def Runtime.socket_for_id {Msg : Type} (id : I64)
    (sockets : List (WsSocket Msg)) : Option (Pair WebSocket (WsEvent -> Msg)) :=
    match sockets {
        List.empty => Option.none,
        List.cons e rest =>
            match e {
                WsSocket.ws_socket key _url ws handler =>
                    if U32.beq (Runtime.socket_id key) (I64.to_u32 id)
                    then Option.some (Pair.pair ws handler)
                    else Runtime.socket_for_id id rest
            }
    }

def Runtime.enqueue_events {S : Type} {Msg : Type} (handler : WsEvent -> Msg)
    (events : List WsEvent) (state : RuntimeState S Msg) : RuntimeState S Msg :=
    Runtime.fold_enqueue (Runtime.map_events handler events) state

#[terminating]
def Runtime.map_events {Msg : Type} (handler : WsEvent -> Msg) (events : List WsEvent) : List Msg :=
    match events {
        List.empty => List.empty,
        List.cons e rest => List.cons (handler e) (Runtime.map_events handler rest)
    }

#[terminating]
def Runtime.fold_enqueue {S : Type} {Msg : Type} (msgs : List Msg) (state : RuntimeState S Msg)
    : RuntimeState S Msg :=
    match msgs {
        List.empty => state,
        List.cons m rest => Runtime.fold_enqueue rest (Runtime.enqueue m state)
    }

def Runtime.set_sockets {S : Type} {Msg : Type} (sockets : List (WsSocket Msg))
    (state : RuntimeState S Msg) : RuntimeState S Msg :=
    match state {
        RuntimeState.st root last model queue stopped handlers subs timers focus paint _old =>
            RuntimeState.st root last model queue stopped handlers subs timers focus paint sockets,
    }

/// The live sockets of a state value (pure).
def Runtime.state_sockets {S : Type} {Msg : Type} (st : RuntimeState S Msg) : List (WsSocket Msg) :=
    match st {
        RuntimeState.st _root _last _model _queue _stopped _handlers _subs _timers _focus _paint sockets =>
            sockets,
    }

def Runtime.sockets_of_state {S : Type} {Msg : Type} (state : Ref (RuntimeState S Msg))
    : IO (List (WsSocket Msg)) := do {
    let st <- Ref.get state;
    match st {
        RuntimeState.st _root _last _model _queue _stopped _handlers _subs _timers _focus _paint sockets =>
            IO.pure sockets,
    }
}

/// Send `data` on the socket a `Subscription.websocket` owns for `url`.
/// No subscription owns it (yet, or any more): the command is dropped.
def Runtime.send_on_socket {S : Type} {Msg : Type} (url : String) (data : WsData) : IO Unit := do {
    let state <- Runtime.load_state;
    let sockets <- Runtime.sockets_of_state state;
    match Runtime.find_socket url sockets {
        Option.none => IO.pure unit,
        Option.some ws => do {
            let _ <- WebSocket.send ws data;
            IO.pure unit
        }
    }
}

#[terminating]
def Runtime.find_socket {Msg : Type} (url : String) (sockets : List (WsSocket Msg)) : Option WebSocket :=
    match sockets {
        List.empty => Option.none,
        List.cons e rest =>
            match e {
                WsSocket.ws_socket _key entry_url ws _handler =>
                    if String.beq entry_url url then Option.some ws else Runtime.find_socket url rest
            }
    }

/// Forget the socket for `key` and close it.
def Runtime.drop_socket {S : Type} {Msg : Type} (key : String)
    (state : RuntimeState S Msg) : IO (RuntimeState S Msg) := do {
    match state {
        RuntimeState.st root last model queue stopped handlers subs timers focus paint sockets =>
            match Runtime.take_socket key sockets {
                Pair.pair gone rest => do {
                    let _ <- Runtime.close_gone gone;
                    IO.pure (RuntimeState.st root last model queue stopped handlers subs timers focus paint rest)
                }
            }
    }
}

def Runtime.close_gone {Msg : Type} (gone : Option (WsSocket Msg)) : IO Unit :=
    match gone {
        Option.none => IO.pure unit,
        Option.some e =>
            match e {
                WsSocket.ws_socket _key _url ws _handler => do {
                    let _ <- WebSocket.unwatch ws;
                    WebSocket.free ws
                }
            }
    }

def Runtime.take_socket {Msg : Type} (key : String) (sockets : List (WsSocket Msg))
    : Pair (Option (WsSocket Msg)) (List (WsSocket Msg)) :=
    Runtime.take_socket_go key sockets List.empty

#[terminating]
def Runtime.take_socket_go {Msg : Type} (key : String) (sockets : List (WsSocket Msg))
    (acc : List (WsSocket Msg)) : Pair (Option (WsSocket Msg)) (List (WsSocket Msg)) :=
    match sockets {
        List.empty => Pair.pair Option.none (List.reverse acc),
        List.cons e rest =>
            match e {
                WsSocket.ws_socket k _url _ws _handler =>
                    if String.beq k key
                    then Pair.pair (Option.some e) (List.append (List.reverse acc) rest)
                    else Runtime.take_socket_go key rest (List.cons e acc)
            }
    }

pub def Runtime.remove_sub {Msg : Type} (sub : Subscription Msg) : IO Unit :=
    match sub {
        Subscription.none => IO.pure unit,
        Subscription.window event _handler => Dom.off_window event,
        Subscription.document event _handler => Dom.off_document event,
        Subscription.animation_frame _handler => Dom.off_frame,
        Subscription.window_filter event _handler => Dom.off_window event,
        Subscription.media query _handler => Media.unwatch query,
        Subscription.websocket url protocols _handler => do {
            let key := String.concat "ws:" (String.concat url (String.concat "|" (Runtime.join_protocols protocols)));
            let state <- Runtime.load_state;
            let sockets <- Runtime.sockets_of_state state;
            match Runtime.take_socket key sockets {
                Pair.pair gone rest => do {
                    let _ <- Ref.update state (Runtime.set_sockets rest);
                    Runtime.close_gone gone
                }
            }
        },
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
    // Remove first: installing a new listener for an event can replace the
    // old one (the JS host keys listeners by event), and removing after the
    // install would then remove the new listener too.
    let _ <- Runtime.remove_stale old new;
    Runtime.install_added old new
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
        Subscription.window_filter event handler =>
            List.cons
                (Pair.pair (Handler.id List.empty (String.concat "windowf:" event))
                    (fn (e : WebEvent) =>
                        match handler e {
                            Option.some m => HandlerResult.msg m,
                            Option.none => HandlerResult.ignore,
                        }))
                List.empty,
        Subscription.media query handler =>
            List.cons
                (Pair.pair (Handler.id List.empty (String.concat "media:" query))
                    (fn (e : WebEvent) => HandlerResult.msg (handler e)))
                List.empty,
        Subscription.websocket _url _protocols _handler => List.empty,
    }

#[terminating]
def Runtime.collect_sub_handlers {Msg : Type} (subs : List (Subscription Msg))
    : List (Pair U32 (WebEvent -> HandlerResult Msg)) :=
    match subs {
        List.empty => List.empty,
        List.cons sub rest =>
            List.append (Runtime.sub_handler sub) (Runtime.collect_sub_handlers rest),
    }

/// One WebSocket a `Subscription.websocket` owns: its subscription key,
/// the live socket and the pure handler each `WsEvent` becomes a message
/// through. The handler id is `SOCKET_BASE + key` (see `Runtime.socket_id`),
/// which `Runtime.dispatch` routes to `Runtime.dispatch_socket`.
pub type WsSocket (Msg : Type) {
    ws_socket (key : String) (url : String) (ws : WebSocket) (handler : WsEvent -> Msg)
}

pub type RuntimeState (S : Type) (Msg : Type) {
    st (root : Node) (last : Html.Node) (model : S)
        (queue : List Msg) (stopped : Bool)
        (handlers : List (Pair U32 (WebEvent -> HandlerResult Msg)))
        (subs : List (Subscription Msg))
        /// Pending one-shot `Command.after` messages, keyed by timer id.
        (timers : List (Pair I64 Msg))
        /// Selectors a `Command.focus` asked for this batch.
        (focus : List String)
        /// `Command.after_render` effects for this batch, run after the
        /// patch. A thunk, not a stored `IO`: an action held in a
        /// constructor field can run at construction when compiled.
        (paint : List (Unit -> IO (Option Msg)))
        /// The live WebSockets owned by subscriptions.
        (sockets : List (WsSocket Msg))
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
    match Oak.lower (Program.view prog model) {
        Oak.Lowered.lowered tree handlers => do {
            let _ <- Patch.hydrate_root root tree;
            let table := List.append handlers (Runtime.collect_sub_handlers subs);
            let state : Ref (RuntimeState S Msg) <-
                Ref.new (RuntimeState.st root tree model List.empty false table subs
                    List.empty List.empty List.empty List.empty);
            let _ <- Keep.save state;
            // Subscriptions install AFTER the state exists: a WebSocket
            // subscription registers its socket through the state slot.
            let _ <- Runtime.apply_subs List.empty subs;
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
        RuntimeState.st _root _last _model _queue stopped handlers _subs timers _focus _paint sockets =>
            if stopped
            then IO.pure unit
            else if Timer.is_id (I64.to_u32 handler)
            then Runtime.dispatch_timer state handler timers
            else if Runtime.is_socket_id (I64.to_u32 handler)
            then Runtime.dispatch_socket handler sockets
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

/// A timer id is not in the render handler table: its message is stored in
/// `RuntimeState.timers`, so the id resolves here and the message is queued
/// for the next tick. An id already fired (or after `quit`) is ignored.
def Runtime.dispatch_timer {S : Type} {Msg : Type} (state : Ref (RuntimeState S Msg))
    (handler : I64) (timers : List (Pair I64 Msg)) : IO Unit :=
    match Runtime.take_timer handler timers {
        Pair.pair found remaining =>
            match found {
                Option.none => IO.pure unit,
                Option.some m => do {
                    let _ <- Ref.update state (Runtime.set_timers remaining);
                    let _ <- Ref.update state (Runtime.enqueue m);
                    return unit
                },
            },
    }

#[terminating]
def Runtime.take_timer {Msg : Type} (id : I64) (timers : List (Pair I64 Msg))
    : Pair (Option Msg) (List (Pair I64 Msg)) :=
    match timers {
        List.empty => Pair.pair Option.none List.empty,
        List.cons entry rest =>
            match entry {
                Pair.pair key msg =>
                    if I64.beq key id
                    then Pair.pair (Option.some msg) rest
                    else
                        match Runtime.take_timer id rest {
                            Pair.pair found remaining =>
                                Pair.pair found (List.cons entry remaining),
                        },
            },
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
        RuntimeState.st root last model queue stopped handlers subs timers focus paint sockets =>
            RuntimeState.st root last model (List.append queue (List.cons msg List.empty))
                stopped handlers subs timers focus paint sockets,
    }

def Runtime.set_timers {S : Type} {Msg : Type} (timers : List (Pair I64 Msg))
    (state : RuntimeState S Msg) : RuntimeState S Msg :=
    match state {
        RuntimeState.st root last model queue stopped handlers subs _old focus paint sockets =>
            RuntimeState.st root last model queue stopped handlers subs timers focus paint sockets,
    }

def Runtime.add_timer {S : Type} {Msg : Type} (id : I64) (msg : Msg)
    (state : RuntimeState S Msg) : RuntimeState S Msg :=
    match state {
        RuntimeState.st root last model queue stopped handlers subs timers focus paint sockets =>
            RuntimeState.st root last model queue stopped handlers subs
                (List.append timers (List.cons (Pair.pair id msg) List.empty)) focus paint sockets,
    }

def Runtime.add_focus {S : Type} {Msg : Type} (selector : String)
    (state : RuntimeState S Msg) : RuntimeState S Msg :=
    match state {
        RuntimeState.st root last model queue stopped handlers subs timers focus paint sockets =>
            RuntimeState.st root last model queue stopped handlers subs timers
                (List.append focus (List.cons selector List.empty)) paint sockets,
    }

def Runtime.add_paint {S : Type} {Msg : Type} (effect : Unit -> IO (Option Msg))
    (state : RuntimeState S Msg) : RuntimeState S Msg :=
    match state {
        RuntimeState.st root last model queue stopped handlers subs timers focus paint sockets =>
            RuntimeState.st root last model queue stopped handlers subs timers focus
                (List.append paint (List.cons effect List.empty)) sockets,
    }

/// Run a batch's `after_render` effects in order, after the patch, and
/// return the messages they produced (for the next frame).
#[terminating]
def Runtime.run_paint {Msg : Type} (effects : List (Unit -> IO (Option Msg))) : IO (List Msg) :=
    match effects {
        List.empty => IO.pure List.empty,
        List.cons effect rest => do {
            let produced <- effect unit;
            let more <- Runtime.run_paint rest;
            match produced {
                Option.some m => return (List.cons m more),
                Option.none => return more,
            }
        },
    }

/// Run a batch's focus requests, in order, after the patch has placed the
/// nodes they name.
#[terminating]
def Runtime.apply_focus (selectors : List String) : IO Unit :=
    match selectors {
        List.empty => IO.pure unit,
        List.cons selector rest => do {
            let _ <- Dom.focus selector;
            Runtime.apply_focus rest
        },
    }

/// One frame: drain the queue, fold it, re-render and patch. A no-op when
/// nothing was dispatched, and after `Command.quit`, so the rAF loop costs
/// one comparison per frame.
pub def Runtime.tick {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg) : IO Unit := do {
    let state <- Runtime.load_state;
    let snapshot <- Ref.get state;
    match snapshot {
        RuntimeState.st root last model queue stopped handlers subs timers _focus _paint _sockets =>
            if stopped
            then IO.pure unit
            else if List.is_empty queue
            then IO.pure unit
            else Runtime.drain prog host state root last model queue handlers subs timers,
    }
}

def Runtime.drain {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg) (state : Ref (RuntimeState S Msg))
    (root : Node) (last : Html.Node) (model : S) (queue : List Msg)
    (handlers : List (Pair U32 (WebEvent -> HandlerResult Msg)))
    (subs : List (Subscription Msg)) (timers : List (Pair I64 Msg)) : IO Unit := do {
    // Clear the queue first: a message dispatched while the batch runs lands
    // in the NEXT frame. The final write below reads the queue back so it is
    // not overwritten.
    let before <- Ref.get state;
    let live_sockets := Runtime.state_sockets before;
    let drained : RuntimeState S Msg :=
        RuntimeState.st root last model List.empty false handlers subs timers List.empty
            List.empty live_sockets;
    let _ <- Ref.set state drained;
    let folded <- Runtime.run_batch prog host model queue;
    match folded {
        Pair.pair next_model quit => do {
            let next_subs := (Program.subscriptions prog) next_model;
            match Oak.lower (Program.view prog next_model) {
                Oak.Lowered.lowered tree next_handlers => do {
                    let table := List.append next_handlers (Runtime.collect_sub_handlers next_subs);
                    // The batch may have scheduled timers and asked for
                    // focus while it ran; carry those across the staging
                    // write (which clears the queue).
                    let after_batch <- Ref.get state;
                    let batch_timers := Runtime.timers_of after_batch;
                    let batch_focus := Runtime.focus_of after_batch;
                    let batch_paint := Runtime.paint_of after_batch;
                    // Make the new handlers reachable BEFORE the DOM changes:
                    // a patch can fire an event synchronously (e.g. an
                    // autofocused input), and that event must resolve to the
                    // handler just lowered, not the previous frame's table.
                    let staged : RuntimeState S Msg :=
                        RuntimeState.st root last model List.empty false table next_subs
                            batch_timers batch_focus batch_paint (Runtime.state_sockets after_batch);
                    let _ <- Ref.set state staged;
                    let patches := Patch.diff last tree;
                    let _ <- Patch.apply root patches;
                    let _ <- Runtime.apply_subs subs next_subs;
                    let current <- Ref.get state;
                    // Focus runs after the patch, so a dialog inserted this
                    // frame is already in the DOM and can take focus.
                    let _ <- Runtime.apply_focus (Runtime.focus_of current);
                    // `after_render` effects see the patched DOM (a canvas
                    // mounted this frame exists); their messages, and any
                    // the effects dispatched, go to the next frame.
                    let painted <- Runtime.run_paint (Runtime.paint_of current);
                    let after_paint <- Ref.get state;
                    let pending := List.append (Runtime.pending_of after_paint) painted;
                    let next : RuntimeState S Msg :=
                        RuntimeState.st root tree next_model pending quit table next_subs
                            (Runtime.timers_of after_paint) List.empty List.empty
                            (Runtime.state_sockets after_paint);
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
        RuntimeState.st _root _last _model queue _stopped _handlers _subs _timers _focus _paint _sockets => queue,
    }

def Runtime.timers_of {S : Type} {Msg : Type} (state : RuntimeState S Msg) : List (Pair I64 Msg) :=
    match state {
        RuntimeState.st _root _last _model _queue _stopped _handlers _subs timers _focus _paint _sockets => timers,
    }

def Runtime.focus_of {S : Type} {Msg : Type} (state : RuntimeState S Msg) : List String :=
    match state {
        RuntimeState.st _root _last _model _queue _stopped _handlers _subs _timers focus _paint _sockets => focus,
    }

def Runtime.paint_of {S : Type} {Msg : Type} (state : RuntimeState S Msg) : List (Unit -> IO (Option Msg)) :=
    match state {
        RuntimeState.st _root _last _model _queue _stopped _handlers _subs _timers _focus paint sockets => paint,
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
        // `after` schedules the host timer and parks the message in the state
        // slot; `focus` is applied after the next patch; both let the fold
        // continue with the rest of the batch.
        Command.after ms msg => do {
            let id <- Timer.after ms;
            let state <- Runtime.load_state;
            let _ <- Ref.update state (Runtime.add_timer id msg);
            Runtime.step_batch prog host model rest
        },
        Command.focus selector => do {
            let state <- Runtime.load_state;
            let _ <- Ref.update state (Runtime.add_focus selector);
            Runtime.step_batch prog host model rest
        },
        Command.after_render effect => do {
            let state <- Runtime.load_state;
            let _ <- Ref.update state (Runtime.add_paint (Runtime.paint_thunk host effect));
            Runtime.step_batch prog host model rest
        },
        Command.batch cmds => Runtime.step_cmds prog host model rest cmds,
        Command.ws_send url data => do {
            let _ <- Runtime.send_on_socket url data;
            Runtime.step_batch prog host model rest
        },
    }

def Runtime.paint_thunk {E : Type} {Msg : Type} (host : Host IO E Msg) (effect : E)
    : Unit -> IO (Option Msg) :=
    fn (_u : Unit) => Host.run_effect host effect

/// The IO mirror of `oak::app`'s `step_cmds`/`collect_cmds`: effects run in
/// order, dispatches queue for the next batch, `quit` stops later commands,
/// and `after`/`focus`/`after_render` are performed as they are met.
#[terminating]
def Runtime.step_cmds {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg) (model : S) (rest : List Msg)
    (cmds : List (Command E Msg)) : IO (Pair (Pair S Bool) (List Msg)) := do {
    let collected <- Runtime.collect_cmds host cmds List.empty List.empty false;
    Runtime.finish_cmds prog host model rest collected
}

#[partial]
def Runtime.finish_cmds {S : Type} {Msg : Type} {E : Type}
    (prog : Program S Msg E) (host : Host IO E Msg) (model : S) (rest : List Msg)
    (collected : Pair (Pair (List Msg) (List Msg)) Bool) : IO (Pair (Pair S Bool) (List Msg)) :=
    match collected {
        Pair.pair pair quit =>
            match pair {
                Pair.pair perf disp =>
                    if quit
                    then IO.pure (Pair.pair (Pair.pair model true) List.empty)
                    else do {
                        let stepped <- Runtime.step_batch prog host model
                            (List.append (List.reverse perf) rest);
                        match stepped {
                            Pair.pair inner pending =>
                                return (Pair.pair inner (List.append pending (List.reverse disp))),
                        }
                    },
            },
    }

#[partial]
def Runtime.collect_cmds {E : Type} {Msg : Type} (host : Host IO E Msg)
    (cmds : List (Command E Msg)) (perf : List Msg) (disp : List Msg) (quit : Bool)
    : IO (Pair (Pair (List Msg) (List Msg)) Bool) :=
    match cmds {
        List.empty => IO.pure (Pair.pair (Pair.pair perf disp) quit),
        List.cons cmd more =>
            match cmd {
                Command.none => Runtime.collect_cmds host more perf disp quit,
                Command.quit => IO.pure (Pair.pair (Pair.pair perf disp) true),
                Command.dispatch d => Runtime.collect_cmds host more perf (List.cons d disp) quit,
                Command.perform effect => do {
                    let mo <- Host.run_effect host effect;
                    match mo {
                        Option.some m => Runtime.collect_cmds host more (List.cons m perf) disp quit,
                        Option.none => Runtime.collect_cmds host more perf disp quit,
                    }
                },
                Command.after ms msg => do {
                    let id <- Timer.after ms;
                    let state <- Runtime.load_state;
                    let _ <- Ref.update state (Runtime.add_timer id msg);
                    Runtime.collect_cmds host more perf disp quit
                },
                Command.focus selector => do {
                    let state <- Runtime.load_state;
                    let _ <- Ref.update state (Runtime.add_focus selector);
                    Runtime.collect_cmds host more perf disp quit
                },
                Command.after_render effect => do {
                    let state <- Runtime.load_state;
                    let _ <- Ref.update state (Runtime.add_paint (Runtime.paint_thunk host effect));
                    Runtime.collect_cmds host more perf disp quit
                },
                Command.batch inner =>
                    Runtime.collect_cmds host (List.append inner more) perf disp quit,
                Command.ws_send url data => do {
                    let _ <- Runtime.send_on_socket url data;
                    Runtime.collect_cmds host more perf disp quit
                },
            },
    }
