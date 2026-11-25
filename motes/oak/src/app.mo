// The abstract model/update/view layer: pure data plus a fold, with no
// runtime attached. A server or wasm host supplies a `Host N E Msg` that
// interprets effects and decides how to render `Program.view`; this module
// never assumes either.
//
// Semantics are ported from tui's `step_batch`/`step_cmd`
// (motes/tui/src/tui.mo): `dispatch` queues a message for the next batch,
// `perform` runs the host effect immediately and folds its optional
// message back into the CURRENT batch, and `quit` stops the batch.

use lib::events {Subscription}
use lib::typed {Oak.Node}
use web_event::websocket {WsData}
use web_event::sound {MediaCmd, SoundFx, Wave}
use web_event::rtc {RtcSdp, RtcIce, RtcData}

// ═══ Types ═══
//
// Single-constructor parameterized `type`s, not structs (parameterized
// structs do not parse). Constructors are reached through the type
// (`Command.none`, `Host.host`, `Program.program`). `Program.app` is a def
// (three arguments, no subscriptions) so existing call sites keep working;
// use `Program.with_subs` to declare global subscriptions.

pub type Command (E : Type) (Msg : Type) {
    none,
    quit,
    dispatch (msg : Msg),
    perform (effect : E),
    /// A one-shot delayed message, resolved by the browser runtime. The pure
    /// fold has no scheduler and treats it as inert.
    after (ms : I64) (msg : Msg),
    /// Move focus after the next patch. The pure fold has no DOM and treats
    /// it as inert.
    focus (selector : String),
    /// Run a host effect after the next patch, when the DOM shows this
    /// batch's view (a `<canvas>` rendered this frame exists). Its optional
    /// message goes to the NEXT batch. This is how a program draws: the
    /// update stays pure and returns the drawing as an effect. The pure fold
    /// has no DOM and treats it as inert.
    after_render (effect : E),
    /// Several commands, run left-to-right (see `step_cmds`).
    batch (cmds : List (Command E Msg)),
    /// Send a message on the WebSocket a `Subscription.websocket` opened
    /// for `url`. The pure fold has no socket and treats it as inert; the
    /// browser runtime sends it (and drops it when no subscription owns
    /// that url).
    ws_send (url : String) (data : WsData),
    /// Play one short sound (`SoundFx`): a synthesized note, a percussive
    /// hit, or a file the runtime decodes on first use. The sound is DATA,
    /// not an effect, so `update` stays pure; the pure fold has no
    /// AudioContext and treats it as inert. The browser runtime plays it
    /// (and resumes a suspended context on the first user gesture).
    sound (fx : SoundFx),
    /// Drive an `<audio>`/`<video>` element the view mounted: play, pause,
    /// seek, volume, mute, loop. Addressed by the element's selector, so a
    /// re-render cannot leave a stale handle behind. Inert in the pure fold.
    media (cmd : MediaCmd),
    /// Hand the browser a description the OTHER peer sent, on the peer a
    /// `Subscription.rtc` opened under `key`. This is the answering half of
    /// signalling: the offer arrives as `RtcEvent.local_description` and
    /// goes out over some transport, and the reply comes back through here.
    ///
    /// The field is `desc`, not `sdp`: `RtcSdp`'s own constructor is named
    /// `sdp`, and a field of that name shadows it in every match over this
    /// type (the checker then reports a confusing "ambiguous constructor
    /// `none`" at the match head).
    rtc_set_remote (key : String) (desc : RtcSdp),
    /// Add one ICE candidate learned from the other peer.
    rtc_add_ice (key : String) (ice : RtcIce),
    /// Open a data channel called `label` on the peer `key` owns. The
    /// channel is usable once `RtcEvent.channel_state` reports it ready.
    /// It is ordered; `max_retransmits` is -1 for reliable, `>= 0` for a
    /// partially reliable channel.
    rtc_open_channel (key : String) (label : String) (max_retransmits : I64),
    /// Send `data` on the channel called `label` on the peer `key` owns.
    /// (Adding a local camera or screen stream is NOT a command: a
    /// `MediaStream` is a web_wasm handle and this layer must not depend on
    /// web_wasm. Call `Rtc.add_stream` from an `after_render`/`perform`
    /// effect, before the offer.)
    rtc_send (key : String) (label : String) (data : RtcData)
}

pub type Host (N : Type -> Type) (E : Type) (Msg : Type) {
    host (run_effect : E -> N (Option Msg))
}

pub type Program (S : Type) (Msg : Type) (E : Type) {
    program (init : S)
        (update : S -> Msg -> Pair S (Command E Msg))
        (view : S -> Oak.Node Msg)
        (subscriptions : S -> List (Subscription Msg))
}

// ═══ Accessors ═══
//
// Constrained defs live outside `with` blocks: the block parser does not
// accept a type-class bracket after an inner def's name.

pub def Host.run_effect {N : Type -> Type} {E : Type} {Msg : Type}
    (h : Host N E Msg) (effect : E) : N (Option Msg) :=
    match h { Host.host f => f effect }

def no_subscriptions {S : Type} {Msg : Type} (_s : S) : List (Subscription Msg) := List.empty

with Program {
    /// A program with no subscriptions (the common case).
    pub def app {S : Type} {Msg : Type} {E : Type}
        (init : S)
        (update : S -> Msg -> Pair S (Command E Msg))
        (view : S -> Oak.Node Msg) : Program S Msg E :=
        Program.program init update view no_subscriptions

    /// A program that declares global subscriptions as a function of the
    /// model (Elm's `Subscription msg`).
    pub def with_subs {S : Type} {Msg : Type} {E : Type}
        (init : S)
        (update : S -> Msg -> Pair S (Command E Msg))
        (view : S -> Oak.Node Msg)
        (subscriptions : S -> List (Subscription Msg)) : Program S Msg E :=
        Program.program init update view subscriptions

    pub def init {S : Type} {Msg : Type} {E : Type} (a : Program S Msg E) : S :=
        match a { Program.program s _ _ _ => s }

    pub def view {S : Type} {Msg : Type} {E : Type} (a : Program S Msg E) (s : S) : Oak.Node Msg :=
        match a { Program.program _ _ v _ => v s }

    /// The pure `update` projection.
    pub def step {S : Type} {Msg : Type} {E : Type}
        (a : Program S Msg E) (s : S) (msg : Msg) : Pair S (Command E Msg) :=
        match a { Program.program _ update _ _ => update s msg }

    /// The pure subscription request for a model.
    pub def subscriptions {S : Type} {Msg : Type} {E : Type}
        (a : Program S Msg E) : S -> List (Subscription Msg) :=
        match a { Program.program _ _ _ subs => subs }
}

// ═══ Sound and media command helpers ═══
//
// `Command.sound (SoundFx.beep ...)` is the general form; these are the
// call sites an app actually writes. They are pure constructors, so an
// `update` that returns one stays pure and testable on any target.

/// A note: `Command.beep Wave.sine 880.0 0.3 120i64`.
pub def Command.beep {E : Type} {Msg : Type} (wave : Wave) (freq : F64) (gain : F64)
    (duration_ms : I64) : Command E Msg :=
    Command.sound (SoundFx.beep wave freq gain duration_ms)

/// A percussive hit: a noise burst, optionally lowpassed.
pub def Command.hit {E : Type} {Msg : Type} (gain : F64) (duration_ms : I64)
    (lowpass_hz : F64) : Command E Msg :=
    Command.sound (SoundFx.hit gain duration_ms lowpass_hz)

/// A sound decoded from `url` and played once ready.
pub def Command.play_file {E : Type} {Msg : Type} (url : String) (gain : F64) : Command E Msg :=
    Command.sound (SoundFx.file url gain)

/// Stop every sound this app started.
pub def Command.silence {E : Type} {Msg : Type} : Command E Msg :=
    Command.sound SoundFx.silence

/// One `<audio>`/`<video>` transport action, by selector.
pub def Command.media_cmd {E : Type} {Msg : Type} (cmd : MediaCmd) : Command E Msg :=
    Command.media cmd

/// Fold a batch to quiescence: run it, then drain the messages its
/// `dispatch` commands queued as subsequent batches. Returns the final
/// model and whether `quit` was requested. An update that always
/// dispatches does not terminate; the host owns progress.
pub def Program.run_batch [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : Program S Msg E) (h : Host N E Msg) (s : S) (msgs : List Msg) : N (Pair S Bool) :=
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
    (a : Program S Msg E) (h : Host N E Msg) (model : S) (rest : List Msg)
    (p : Pair S (Command E Msg)) : N (Pair (Pair S Bool) (List Msg)) :=
    match p { Pair.pair model2 cmd => step_cmd a h model2 rest cmd }

#[terminating]
def step_batch [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : Program S Msg E) (h : Host N E Msg) (model : S) (msgs : List Msg)
    : N (Pair (Pair S Bool) (List Msg)) :=
    match msgs {
        List.empty => Monad.pure (Pair.pair (Pair.pair model false) List.empty),
        List.cons m rest => step_msg a h model rest (Program.step a model m)
    }

#[terminating]
def perform_step [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : Program S Msg E) (h : Host N E Msg) (model : S) (rest : List Msg)
    (mo : Option Msg) : N (Pair (Pair S Bool) (List Msg)) :=
    match mo {
        Option.some m2 => step_batch a h model (List.cons m2 rest),
        Option.none => step_batch a h model rest
    }

#[terminating]
def step_cmd [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : Program S Msg E) (h : Host N E Msg) (model : S) (rest : List Msg)
    (cmd : Command E Msg) : N (Pair (Pair S Bool) (List Msg)) :=
    match cmd {
        Command.none => step_batch a h model rest,
        Command.quit => Monad.pure (Pair.pair (Pair.pair model true) List.empty),
        Command.dispatch d =>
            Monad.bind (step_batch a h model rest)
                (fn (stepped : Pair (Pair S Bool) (List Msg)) =>
                    Monad.pure (queue_dispatched d stepped)),
        Command.perform effect =>
            Monad.bind (Host.run_effect h effect) (perform_step a h model rest),
        // The pure fold has no scheduler and no DOM: `after`/`focus` are
        // runtime commands (oak_wasm's fold implements them), inert here; so is
        // `after_render`.
        Command.after _ms _msg => step_batch a h model rest,
        Command.focus _selector => step_batch a h model rest,
        Command.after_render _effect => step_batch a h model rest,
        Command.batch cmds => step_cmds a h model rest cmds,
        Command.rtc_set_remote _key _desc => step_batch a h model rest,
        Command.rtc_add_ice _key _ice => step_batch a h model rest,
        Command.rtc_open_channel _key _label _retrans => step_batch a h model rest,
        Command.rtc_send _key _label _data => step_batch a h model rest,
        Command.ws_send _url _data => step_batch a h model rest,
        // No AudioContext and no DOM in the pure fold: both are runtime
        // commands `oak_wasm`'s fold implements.
        Command.sound _fx => step_batch a h model rest,
        Command.media _cmd => step_batch a h model rest
    }

/// Several commands, left-to-right. `perform` effects run immediately in
/// order and their optional messages fold into this batch; `dispatch`
/// messages queue for the NEXT batch; `quit` stops later commands. `after`
/// and `focus` are inert here (the wasm runtime implements them).
#[terminating]
def step_cmds [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : Program S Msg E) (h : Host N E Msg) (model : S) (rest : List Msg)
    (cmds : List (Command E Msg)) : N (Pair (Pair S Bool) (List Msg)) :=
    Monad.bind (collect_cmds h cmds List.empty List.empty false)
        (fn (collected : Pair (Pair (List Msg) (List Msg)) Bool) =>
            finish_cmds a h model rest collected)

/// Runs a batch's collected effects through the model fold. The list it
/// folds is not a structural subterm of the command batch, so the
/// termination checker cannot see the measure; the recursion is bounded by
/// the model's own `quit`/settling behaviour, like the rest of the fold.
#[partial]
def finish_cmds [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : Program S Msg E) (h : Host N E Msg) (model : S) (rest : List Msg)
    (collected : Pair (Pair (List Msg) (List Msg)) Bool) : N (Pair (Pair S Bool) (List Msg)) :=
    match collected {
        Pair.pair pair quit =>
            match pair {
                Pair.pair perf disp =>
                    if quit
                    then Monad.pure (Pair.pair (Pair.pair model true) List.empty)
                    else Monad.bind (step_batch a h model (List.append (List.reverse perf) rest))
                        (fn (stepped : Pair (Pair S Bool) (List Msg)) =>
                            Monad.pure (append_dispatch disp stepped)),
            },
    }

def append_dispatch {S : Type} {Msg : Type} (disp : List Msg)
    (stepped : Pair (Pair S Bool) (List Msg)) : Pair (Pair S Bool) (List Msg) :=
    match stepped {
        Pair.pair inner pending => Pair.pair inner (List.append pending (List.reverse disp)),
    }

/// Collect a batch's effects and dispatches without running the model fold.
/// `perf`/`disp` are reverse accumulators.
#[terminating]
def collect_cmds [Monad N] {E : Type} {Msg : Type} (h : Host N E Msg)
    (cmds : List (Command E Msg)) (perf : List Msg) (disp : List Msg) (quit : Bool)
    : N (Pair (Pair (List Msg) (List Msg)) Bool) :=
    match cmds {
        List.empty => Monad.pure (Pair.pair (Pair.pair perf disp) quit),
        List.cons cmd more =>
            match cmd {
                Command.none => collect_cmds h more perf disp quit,
                Command.quit => Monad.pure (Pair.pair (Pair.pair perf disp) true),
                Command.dispatch d => collect_cmds h more perf (List.cons d disp) quit,
                Command.perform effect =>
                    Monad.bind (Host.run_effect h effect)
                        (fn (mo : Option Msg) =>
                            match mo {
                                Option.some m => collect_cmds h more (List.cons m perf) disp quit,
                                Option.none => collect_cmds h more perf disp quit,
                            }),
                Command.after _ms _msg => collect_cmds h more perf disp quit,
                Command.focus _selector => collect_cmds h more perf disp quit,
                Command.after_render _effect => collect_cmds h more perf disp quit,
                Command.batch inner => collect_cmds h (List.append inner more) perf disp quit,
                Command.rtc_set_remote _key _desc => collect_cmds h more perf disp quit,
                Command.rtc_add_ice _key _ice => collect_cmds h more perf disp quit,
                Command.rtc_open_channel _key _label _retrans =>
                    collect_cmds h more perf disp quit,
                Command.rtc_send _key _label _data => collect_cmds h more perf disp quit,
                Command.ws_send _url _data => collect_cmds h more perf disp quit,
                Command.sound _fx => collect_cmds h more perf disp quit,
                Command.media _cmd => collect_cmds h more perf disp quit,
            },
    }

// ═══ Draining deferred dispatches ═══

#[terminating]
def run_result [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : Program S Msg E) (h : Host N E Msg) (inner : Pair S Bool) (pending : List Msg)
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
    (a : Program S Msg E) (h : Host N E Msg)
    (stepped : Pair (Pair S Bool) (List Msg)) : N (Pair S Bool) :=
    match stepped {
        Pair.pair inner pending => run_result a h inner pending
    }

#[terminating]
def run_pending [Monad N] {S : Type} {Msg : Type} {E : Type}
    (a : Program S Msg E) (h : Host N E Msg) (model : S) (pending : List Msg)
    : N (Pair S Bool) :=
    Monad.bind (step_batch a h model pending)
        (fn (stepped : Pair (Pair S Bool) (List Msg)) => run_stepped a h stepped)
