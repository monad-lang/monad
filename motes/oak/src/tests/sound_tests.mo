// The sound and media commands in the PURE fold. `oak::app` has no
// `AudioContext` and no DOM, so these are inert there -- and that is the
// property worth pinning: an app's `update` can return one, the pure fold
// still settles, and the same `update` is testable without a browser.
//
// The performers live in `oak_wasm` and are covered end to end by
// `wasm/web/smoke/audio_smoke.mjs`.

use lib::app {Command, Host, Program}
use lib::elements {Html.div, Html.text}
use lib::typed {Oak.Node}
use web_event::sound {MediaCmd, SoundFx, Wave}

type Msg {
    beep,
    hit,
    file,
    silence,
    media (cmd : MediaCmd),
}

def update (m : I64) (msg : Msg) : Pair I64 (Command Unit Msg) :=
    match msg {
        Msg.beep => Pair.pair (m + 1i64) (Command.beep Wave.sine 440.0 0.5 100i64),
        Msg.hit => Pair.pair (m + 1i64) (Command.hit 0.5 40i64 800.0),
        Msg.file => Pair.pair (m + 1i64) (Command.play_file "/hit.ogg" 0.9),
        Msg.silence => Pair.pair (m + 1i64) Command.silence,
        Msg.media cmd => Pair.pair (m + 1i64) (Command.media_cmd cmd),
    }

def view (m : I64) : Oak.Node Msg :=
    Html.div List.empty [Html.text (I64.to_string m)]

def app : Program I64 Msg Unit := Program.app 0i64 update view

def host : Host IO Unit Msg := Host.host (fn _e => IO.pure Option.none)

/// The helpers build the `SoundFx` their name promises.
#[test]
def test_beep_builds_a_beep : Bool :=
    match Command.beep Wave.square 880.0 0.25 50i64 {
        Command.sound fx =>
            match fx {
                SoundFx.beep wave freq gain duration_ms =>
                    I64.beq (Wave.code wave) 1i64
                        && F64.beq freq 880.0
                        && F64.beq gain 0.25
                        && I64.beq duration_ms 50i64,
                _ => false,
            },
        _ => false,
    }

#[test]
def test_silence_builds_silence : Bool :=
    match Command.silence {
        Command.sound fx => SoundFx.is_silence fx,
        _ => false,
    }

#[test]
def test_media_cmd_wraps_the_action : Bool :=
    match Command.media_cmd (MediaCmd.pause "#track") {
        Command.media cmd => (match cmd { MediaCmd.pause selector => String.beq selector "#track", _ => false }),
        _ => false,
    }

/// The pure fold settles and keeps the model: a `Command.sound` runs no
/// effect and produces no message.
#[test]
def test_sound_is_inert_in_the_pure_fold : IO Bool := do {
    let result <- Program.run_batch app host 0i64 [Msg.beep, Msg.hit, Msg.silence];
    match result {
        Pair.pair model quit => IO.pure (I64.beq model 3i64 && Bool.not quit),
    }
}

#[test]
def test_media_is_inert_in_the_pure_fold : IO Bool := do {
    let result <- Program.run_batch app host 0i64
        [Msg.media (MediaCmd.play "#a"), Msg.media (MediaCmd.seek "#a" 1000i64)];
    match result {
        Pair.pair model quit => IO.pure (I64.beq model 2i64 && Bool.not quit),
    }
}

/// Inside a `Command.batch`, a sound neither performs nor dispatches: the
/// batch folds the rest of its commands and leaves the queue empty.
#[test]
def test_sound_in_a_batch_queues_nothing : IO Bool := do {
    let batched : Command Unit Msg :=
        Command.batch [Command.beep Wave.sine 440.0 0.5 10i64, Command.silence];
    let prog : Program I64 Msg Unit :=
        Program.app 0i64 (fn (m : I64) (_msg : Msg) => Pair.pair (m + 1i64) batched) view;
    let result <- Program.run_batch prog host 0i64 [Msg.beep];
    match result {
        Pair.pair model quit => IO.pure (I64.beq model 1i64 && Bool.not quit),
    }
}
