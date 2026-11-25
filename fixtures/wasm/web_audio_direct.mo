// The imperative sound surface: file decoding and PCM playback.
//
// `audio_smoke.mjs` covers the Oak command path (`Command.beep`/`hit`); this
// fixture drives `web_wasm::audio` directly, which is what a game loop does:
//   * `probe_pcm` packs a `List F64` into a `Buf F32` and plays it as PCM at
//     a declared rate, proving the typed buffer crosses whole;
//   * `probe_decode` drives a fetch -> decode -> play pipeline.
//
// The reports are `Console.log` lines the harness asserts on, because an
// `#[export "c"]` def returns no value.
#![mote { name := "web_audio_direct", deps := [web_wasm, web_event] }]

use std::buf {Buf}
use std::bytebuf {ByteBuf.free}
use std::ref {Ref}
use web_wasm::audio {
    AudioCtx, Audio.context, Audio.decode_begin, Audio.decode_error, Audio.decode_poll,
    Audio.decode_sound, Audio.play_pcm, Audio.play_sound, Audio.set_master,
    Audio.sound_duration_ms,
}
use web_wasm::console {Console.log}
use web_wasm::fetch {Fetch.begin, Fetch.poll, Fetch.get_bytes}
use web_wasm::keep {Keep.load, Keep.save}
use web_wasm::types {RequestId}

/// Frames a `probe_pcm` run plays: a 440 Hz sine at 8 kHz, 0.1 s.
def pcm_frames : List F64 := [
    0.0, 0.3387, 0.6374, 0.8763, 1.0, 0.8763, 0.6374, 0.3387,
    0.0, -0.3387, -0.6374, -0.8763, -1.0, -0.8763, -0.6374, -0.3387
]

/// Pack the frames into a `Buf F32` and play them.
#[export "c"]
def probe_pcm : IO Unit := do {
    let c <- Audio.context;
    let n := List.length (Shared.get (Shared.of pcm_frames));
    let buf <- Buf.new_f32 n;
    let sb := Shared.of buf;
    let _ <- fill (Shared.get sb) 0i64 pcm_frames;
    let _ <- Audio.set_master c 1.0;
    let _ <- Audio.play_pcm c (Shared.of buf) 8000i64 0.5;
    Console.log (String.concat "pcm_frames=" (I64.to_string n));
    IO.pure unit
}

def fill (b : Buf F32) (i : I64) (rest : List F64) : IO Unit :=
    match rest {
        List.empty => IO.pure unit,
        List.cons x more => do {
            let _ <- Buf.set_f32 b i (F64.to_f32 x);
            fill b (I64.add i 1i64) more
        },
    }

// ── The decode pipeline ───────────────────────────────────────────────
//
// A fetch and a decode are both PROMISE-based, and a promise never settles
// inside one synchronous export: the event loop has to turn. So the probe is
// a small state machine driven by repeated calls, which is exactly the
// `*_begin`/`poll` protocol an app drives from its frame loop:
//
//   phase 0 -- begin the fetch
//   phase 1 -- poll it; on done, read the bytes and begin the decode
//   phase 2 -- poll the decode; on done, read the `Sound` and play it
//
// The state is created ONCE by `probe_init` and saved in the `Keep` export
// slot (how `oak_wasm`'s `Runtime.mount` saves its runtime). A top-level
// `def` whose body is `IO` is re-evaluated at each use, so
// `def slot := Ref.new ...` would hand every call a fresh slot and lose the
// request.

pub struct ProbeState {
    phase : I64 := 0,
    /// The in-flight fetch. `Shared` because each poll reads it.
    req : Option (Shared RequestId) := Option.none,
    /// The decode operation's host id.
    op : I64 := 0
}

#[export "c"]
def probe_init : IO Unit := do {
    let slot <- Ref.new ProbeState.mk;
    Keep.save slot
}

def probe_slot : IO (Ref ProbeState) := do {
    let cached <- Keep.load;
    // `Keep.load` is untyped: it returns whatever `Ref` was saved, and this
    // annotation pins the struct type.
    let slot : Ref ProbeState := cached;
    IO.pure slot
}

/// Fetch `/sfx.ogg`, decode it, play it, and report. Each call advances one
/// phase; the harness calls it until it prints a terminal line.
#[export "c"]
def probe_decode : IO Unit := do {
    let c <- Audio.context;
    let slot <- probe_slot;
    let st <- Ref.get slot;
    if I64.beq st.phase 0i64 then begin_fetch slot
    else if I64.beq st.phase 1i64 then poll_fetch c slot st
    else poll_decode c slot st
}

def begin_fetch (slot : Ref ProbeState) : IO Unit := do {
    let req <- Fetch.begin "/sfx.ogg" 0i64 "";
    let _ <- Ref.set slot { phase := 1i64, req := Option.some (Shared.of req), op := 0i64 };
    Console.log "decode:started"
}

def poll_fetch (c : AudioCtx) (slot : Ref ProbeState) (st : ProbeState) : IO Unit :=
    match st.req {
        Option.none => Console.log "decode:lost_request",
        Option.some req => do {
            let state <- Fetch.poll (Shared.get req);
            if I64.beq state 1i64 then begin_decode c slot req
            else if I64.beq state 2i64 then do {
                let _ <- Ref.set slot ProbeState.mk;
                Console.log "decode:fetch_failed"
            }
            else Console.log "decode:pending"
        }
    }

def begin_decode (c : AudioCtx) (slot : Ref ProbeState) (req : Shared RequestId) : IO Unit := do {
    let bytes <- Fetch.get_bytes req;
    match bytes {
        Option.none => do {
            let _ <- Ref.set slot ProbeState.mk;
            Console.log "decode:no_body"
        },
        Option.some buf => do {
            let op <- Audio.decode_begin c buf;
            let _ <- ByteBuf.free buf;
            let _ <- Ref.set slot { phase := 2i64, req := Option.none, op := op };
            Console.log "decode:decoding"
        }
    }
}

def poll_decode (c : AudioCtx) (slot : Ref ProbeState) (st : ProbeState) : IO Unit := do {
    let state <- Audio.decode_poll st.op;
    if I64.beq state 1i64 then do {
        let _ <- Ref.set slot ProbeState.mk;
        let found <- Audio.decode_sound st.op;
        match found {
            Option.none => Console.log "decode:no_sound",
            Option.some s => do {
                let ms <- Audio.sound_duration_ms s;
                Console.log (String.concat "decode:ok_ms=" (I64.to_string ms));
                let _ <- Audio.play_sound c s 0.8;
                IO.pure unit
            }
        }
    }
    else if I64.beq state 2i64 then do {
        let name <- Audio.decode_error st.op;
        let _ <- Ref.set slot ProbeState.mk;
        Console.log (String.concat "decode:err=" name)
    }
    else Console.log "decode:pending"
}

def main : IO Unit := IO.pure unit
