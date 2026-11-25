// Sound from an Oak app: `Command.beep`/`Command.hit` from an update, and
// `<audio>` transport control.
//
// `wasm/web/smoke/audio_smoke.mjs` installs the recording Web Audio stub
// (`stub_audio.mjs`) and then asserts:
//   * the first click opened exactly ONE `AudioContext`, resumed it, and
//     scheduled one oscillator through a gain into the destination;
//   * a later beep reuses that context (no second one);
//   * `Command.hit` schedules a buffer source with a lowpass filter;
//   * `Command.silence` takes the master gain to 0;
//   * the `<audio>` element the view mounted plays/pauses/seeks/volumes by
//     selector, and the autoplay block is reported as a message.
#![mote { name := "oak_sound", deps := [oak, oak_wasm, web_wasm, web_event] }]

use oak::typed {Oak.Node}
use oak::elements {Html.div, Html.span, Html.button, Html.audio, Html.id_, Html.src, Html.text, Html.attr, Html.bool_attr}
use oak::events {Html.on_click}
use oak::app {Command, Host, Program}
use web_wasm::audio {
    AudioCtx, Audio.beep, Audio.context, Audio.is_running, Audio.noise, Audio.resume,
    Audio.set_master,
}
// `Wave` is the pure vocabulary, owned by `web_event` (ambient through
// `web_wasm`'s re-export, but named explicitly so the import is checkable).
use web_event::sound {Wave, MediaCmd}
use web_wasm::media_element {MediaElement.play, MediaElement.pause, MediaElement.position_ms}
use oak_wasm::program {Runtime.dispatch, Runtime.mount, Runtime.tick}
use web_wasm::console {Console.log}

type Msg {
    beep,
    hit,
    silence,
    play_track,
    pause_track,
    report,
}

/// The model counts what happened, so the harness can read it off the DOM
/// (`#count`) as well as off the stub's call stream.
type Model {
    model (beeps : I64) (plays : I64)
}

def init : Model := Model.model 0i64 0i64

def update (m : Model) (msg : Msg) : Pair Model (Command Unit Msg) :=
    match msg {
        Msg.beep => Pair.pair (Model.model (m.beeps + 1i64) m.plays)
            (Command.beep Wave.square 440.0 0.4 80i64),
        Msg.hit => Pair.pair m (Command.hit 0.5 60i64 900.0),
        Msg.silence => Pair.pair m Command.silence,
        Msg.play_track => Pair.pair (Model.model m.beeps 1i64) (Command.media_cmd (MediaCmd.play "#track")),
        Msg.pause_track => Pair.pair (Model.model m.beeps 0i64) (Command.media_cmd (MediaCmd.pause "#track")),
        Msg.report => Pair.pair m Command.none,
    }

def view (m : Model) : Oak.Node Msg :=
    Html.div [Html.id_ "app"]
        [Html.span [Html.id_ "count"] [Html.text (I64.to_string m.beeps)],
            Html.audio [Html.id_ "track", Html.src "/song.mp3",
                Html.attr "preload" "none"] List.empty,
            Html.button [Html.id_ "beep", Html.on_click Msg.beep] [Html.text "beep"],
            Html.button [Html.id_ "hit", Html.on_click Msg.hit] [Html.text "hit"],
            Html.button [Html.id_ "silence", Html.on_click Msg.silence] [Html.text "off"],
            Html.button [Html.id_ "play", Html.on_click Msg.play_track] [Html.text "play"],
            Html.button [Html.id_ "pause", Html.on_click Msg.pause_track] [Html.text "pause"]]

def app : Program Model Msg Unit := Program.app init update view

def host : Host IO Unit Msg := Host.host (fn _effect => IO.pure Option.none)

#[export "c"]
def oak_mount : IO Unit := Runtime.mount app

#[export "c"]
def oak_dispatch_event (handler : I64) : IO Unit := Runtime.dispatch handler

#[export "c"]
def oak_tick : IO Unit := Runtime.tick app host

// ── the imperative API, driven directly by the smoke test ──────────────
//
// One export that exercises `web_wasm::audio` without Oak, so a break in
// either layer is attributable: it reports the context's state and the
// transport position, both of which the harness compares.

#[export "c"]
def direct_probe : IO Unit := do {
    let c <- Audio.context;
    let running <- Audio.is_running c;
    Console.log (String.concat "state=" (if running then "running" else "suspended"));
    let _ <- Audio.resume c;
    let running2 <- Audio.is_running c;
    Console.log (String.concat "after_resume=" (if running2 then "running" else "suspended"));
    let _ <- Audio.set_master c 0.25;
    let _ <- Audio.beep c Wave.sine 660.0 0.2 50i64;
    let _ <- Audio.noise c 0.1 20i64 400.0;
    let pos <- MediaElement.position_ms "#track";
    Console.log (String.concat "position_ms=" (I64.to_string pos));
    let _ <- MediaElement.play "#track";
    IO.pure unit
}

def main : IO Unit := IO.pure unit
