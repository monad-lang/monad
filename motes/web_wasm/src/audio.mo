/// Sound: Web Audio synthesis, PCM playback and file decoding.
///
/// One `AudioContext` per page serves every voice. `Audio.context` returns
/// its handle and reuses the page's existing one; a browser gives a page a
/// single practical context, so a second is not offered.
///
/// **Autoplay.** A context starts `suspended` and only `running` after a
/// user gesture. That is the browser's policy, not a Monad limitation, so
/// nothing here tries to defeat it: `Audio.context` does not resume, an app
/// resumes on a click (or lets `oak_wasm` do it), and `Audio.state` says
/// which state the page is actually in.
///
/// **Two kinds of sound.** A *synthesized* voice (`tone`, `noise`,
/// `play_pcm`) is described by parameters; a *decoded* one (`decode_begin`
/// -> `Sound`) came from a file. Both end at a graph node, and both are
/// fire-and-forget unless the returned `AudioNode` is kept to `Audio.stop`
/// it.
///
/// **Decoding is two-phase**, for the same reason `Fetch` is:
/// `decodeAudioData` resolves in a promise callback, and a promise callback
/// must not re-enter wasm while a Monad frame is on the stack.
///
/// The handles are structs with a readable `id`, the shape `gl.mo` uses,
/// because a program must be able to tell the null handle (0) from a live
/// one. `ffi.mo` names them, so they are declared here and re-exported.

use std::buf {Buf, Buf.length}
use std::bytebuf {ByteBuf}
// `Wave` and its host code are the PURE vocabulary in `web_event`, so an
// Oak `SoundFx` names the same type this module plays.
use web_event::sound {Wave, Wave.code}
use lib::ffi {
    audio_open_raw, audio_state_raw, audio_resume_raw, audio_now_us_raw,
    audio_sample_rate_raw, audio_set_master_raw, audio_tone_raw, audio_stop_raw,
    audio_noise_raw, audio_play_pcm_raw, audio_decode_begin_raw,
    audio_decode_poll_raw, audio_decode_sound_raw, audio_decode_error_raw,
    audio_play_sound_raw, audio_sound_duration_ms_raw,
}

// ─── Handles ─────────────────────────────────────────────────────────

/// A live `AudioContext`, as the host's table id. One per page is the
/// browser's practical limit, so `Audio.context` reuses an existing one.
pub struct AudioCtx {
    id : I64
}

/// A decoded sound: an `AudioBuffer` in the host's table. Playing it does
/// not consume it, so one `Sound` sustains many overlapping voices.
pub struct Sound {
    id : I64
}

/// A node in a context's graph (an oscillator, a gain, a buffer source).
/// Only a voice that must be stopped early needs the handle; a one-shot
/// `Audio.beep` drops it.
pub struct AudioNode {
    id : I64
}

/// All three are host ids: a frame names the same context and sound many
/// times, and a decode poll reads its operation once per poll.
pub instance Copy AudioCtx {
    def copy (c : AudioCtx) : Pair AudioCtx AudioCtx := Pair.pair c c
}

pub instance Copy Sound {
    def copy (s : Sound) : Pair Sound Sound := Pair.pair s s
}

pub instance Copy AudioNode {
    def copy (n : AudioNode) : Pair AudioNode AudioNode := Pair.pair n n
}

// ─── The context ─────────────────────────────────────────────────────

/// `AudioContext.state`, as the browser reports it.
pub type AudioState {
    /// Created but silent until a user gesture.
    suspended,
    running,
    /// `close()` was called; a new context is required.
    closed,
    /// Suspended by the OS (a backgrounded page on some platforms).
    interrupted
}

/// Open (or reuse) the page's context. The handle's id is 0 when the
/// browser has no Web Audio at all, which `Audio.supported` distinguishes
/// from "not resumed yet".
pub def Audio.context : IO AudioCtx := do {
    let id <- IO.mk audio_open_raw;
    IO.pure { id := id : AudioCtx }
}

/// Whether the browser has `AudioContext` at all (an exotic embedder may
/// not). Cheap enough to ask once at startup and keep in the model.
pub def Audio.supported : IO Bool := do {
    let c <- Audio.context;
    IO.pure (Bool.not (I64.beq c.id 0i64))
}

/// The context's state.
pub def Audio.state (c : AudioCtx) : IO AudioState := do {
    let raw <- IO.mk (audio_state_raw c.id);
    if I64.beq raw 1i64 then IO.pure AudioState.running
    else if I64.beq raw 2i64 then IO.pure AudioState.closed
    else if I64.beq raw 3i64 then IO.pure AudioState.interrupted
    else IO.pure AudioState.suspended
}

/// Whether the context is running: the one check a caller needs before it
/// decides a silent page is a bug.
pub def Audio.is_running (c : AudioCtx) : IO Bool := do {
    let s <- Audio.state c;
    IO.pure (match s { AudioState.running => true, _ => false })
}

/// Ask the browser to start the context. Call it from a user gesture (a
/// click handler's effect); outside one the browser may ignore it, which
/// `Audio.state` will then report as still `suspended`.
pub def Audio.resume (c : AudioCtx) : IO Bool := do {
    let ok <- IO.mk (audio_resume_raw c.id);
    IO.pure (I64.beq ok 1i64)
}

/// The context clock in seconds. Monotonic for the life of the context and
/// independent of wall time, so it is what a scheduled envelope measures
/// against.
pub def Audio.now (c : AudioCtx) : IO F64 := do {
    let us <- IO.mk (audio_now_us_raw c.id);
    IO.pure ((I64.to_f64 us) / 1000000.0)
}

/// The context's sample rate in Hz (48000 on most hardware). `play_pcm`
/// takes a buffer's OWN rate and the browser resamples, so this is for
/// callers that generate frames.
pub def Audio.sample_rate (c : AudioCtx) : IO I64 := IO.mk (audio_sample_rate_raw c.id)

/// The master gain every voice passes through: the one page-wide volume
/// (and mute) control. Values outside 0..1 are clamped at the boundary.
pub def Audio.set_master (c : AudioCtx) (gain : F64) : IO Unit :=
    IO.mk (audio_set_master_raw c.id gain)

// ─── Synthesized voices ──────────────────────────────────────────────

/// A short oscillator note: `freq` in Hz, `gain` its peak (0..1),
/// `duration_ms` how long it sounds, with a linear attack and release
/// (`attack_ms`, `release_ms`) so it neither clicks on nor off.
///
/// The voice schedules its own stop, so a one-shot needs nothing further.
/// Keep the returned `AudioNode` only to `Audio.stop` it early.
pub def Audio.tone (c : AudioCtx) (wave : Wave) (freq : F64) (gain : F64)
    (duration_ms : I64) (attack_ms : I64) (release_ms : I64) : IO AudioNode :=
    do {
        let id <- IO.mk (audio_tone_raw c.id (Wave.code wave) freq gain duration_ms attack_ms release_ms);
        IO.pure { id := id : AudioNode }
    }

/// The common case: a note with a 5 ms attack and a release over the last
/// third of its length.
pub def Audio.beep (c : AudioCtx) (wave : Wave) (freq : F64) (gain : F64)
    (duration_ms : I64) : IO AudioNode :=
    Audio.tone c wave freq gain duration_ms 5i64 (I64.div duration_ms 3i64)

/// A white-noise burst through an optional lowpass (`lowpass_hz` 0 = none):
/// a percussive hit, a whoosh, an explosion. The host caps the length at
/// two seconds, because a noise node materialises a whole buffer.
pub def Audio.noise (c : AudioCtx) (gain : F64) (duration_ms : I64)
    (lowpass_hz : F64) : IO AudioNode :=
    do {
        let id <- IO.mk (audio_noise_raw c.id gain duration_ms lowpass_hz);
        IO.pure { id := id : AudioNode }
    }

/// Play `frames` mono samples packed as `Buf F32` (each in -1..1) at
/// `sample_rate` Hz. The browser resamples to the context's rate, and the
/// frames are copied out of the buffer, so it may be freed when this
/// returns.
///
/// A `Shared (Buf F32)` because the same buffer is often played twice (a
/// loop) and because reading it does not consume it.
pub def Audio.play_pcm (c : AudioCtx) (frames : Shared (Buf F32)) (sample_rate : I64)
    (gain : F64) : IO AudioNode :=
    do {
        let id <- IO.mk (audio_play_pcm_raw c.id (Shared.get frames) sample_rate gain);
        IO.pure { id := id : AudioNode }
    }

/// Cut a voice off now. Safe on one that already stopped itself, so a
/// "stop the alarm" path needs no bookkeeping.
pub def Audio.stop (n : AudioNode) : IO Unit := IO.mk (audio_stop_raw n.id)

// ─── Decoded sounds ──────────────────────────────────────────────────

/// The `sound` handle a finished `decode_begin` produced, or `none` when
/// the decode has not finished or failed.
pub def Audio.decode_sound (op : I64) : IO (Option Sound) := do {
    let s <- IO.mk (audio_decode_sound_raw op);
    if I64.beq s 0i64
    then IO.pure Option.none
    else IO.pure (Option.some { id := s : Sound })
}

/// The decode state: 0 pending, 1 done, 2 failed. A caller that has no
/// frame loop of its own uses `Audio.decode` below instead.
pub def Audio.decode_poll (op : I64) : IO I64 := IO.mk (audio_decode_poll_raw op)

/// The `DOMException.name` a failed decode produced (empty otherwise).
pub def Audio.decode_error (op : I64) : IO String := IO.mk (audio_decode_error_raw op)

/// Start decoding an audio FILE from bytes the caller already has: the
/// body of a `Fetch` (`Fetch.read`), or a file a drop handler received.
/// Poll with `Audio.decode_poll`, then read the sound with
/// `Audio.decode_sound`.
///
/// The bytes are copied before the promise resolves, so `bytes` may be
/// freed once this returns.
pub def Audio.decode_begin (c : AudioCtx) (bytes : ByteBuf) : IO I64 :=
    IO.mk (audio_decode_begin_raw c.id bytes)

/// Decode and wait, for a caller with no frame loop: `Ok sound` when the
/// file decoded, `Err name` when it did not. `budget` bounds the polls;
/// see `Crypto.await_op` on why spinning starves a browser event loop, and
/// prefer `decode_begin` in a UI.
pub def Audio.decode (c : AudioCtx) (bytes : ByteBuf) (budget : I64) : IO (Result String Sound) := do {
    let op <- Audio.decode_begin c bytes;
    let state <- Audio.await (fn (_u : Unit) => Audio.decode_poll op) budget;
    if I64.beq state 1i64
    then do {
        let found <- Audio.decode_sound op;
        match found {
            Option.some s => IO.pure (Result.ok s),
            Option.none => IO.pure (Result.err "DecodeError")
        }
    }
    else if I64.beq state 2i64
    then do {
        let name <- Audio.decode_error op;
        IO.pure (Result.err name)
    }
    else IO.pure (Result.err "timeout")
}

/// Poll `probe` until it answers non-zero or `budget` runs out. Returns the
/// last answer (0 when the budget ran out while still pending).
///
/// A tight spin would starve the browser's event loop and the promise could
/// never settle, so this is deliberately a bounded loop for a non-UI
/// caller; a UI polls from its own animation frame instead.
#[partial]
def Audio.await (probe : Unit -> IO I64) (budget : I64) : IO I64 := do {
    let state <- probe unit;
    if Bool.not (I64.beq state 0i64) then IO.pure state
    else if Bool.not (I64.gt budget 0i64) then IO.pure 0i64
    else Audio.await probe (I64.sub budget 1i64)
}

/// Play a decoded sound whole. `gain` is its peak; keep the node to stop it
/// early.
pub def Audio.play_sound (c : AudioCtx) (s : Sound) (gain : F64) : IO AudioNode :=
    do {
        let id <- IO.mk (audio_play_sound_raw c.id s.id gain 0i64 0i64);
        IO.pure { id := id : AudioNode }
    }

/// Play a slice: from `offset_ms`, for `duration_ms`. Either 0 means "all of
/// it" (a zero duration is not a zero-length play), which is why this is
/// separate from `play_sound` rather than a parameterised twin.
pub def Audio.play_sound_slice (c : AudioCtx) (s : Sound) (gain : F64)
    (offset_ms : I64) (duration_ms : I64) : IO AudioNode :=
    do {
        let id <- IO.mk (audio_play_sound_raw c.id s.id gain offset_ms duration_ms);
        IO.pure { id := id : AudioNode }
    }

/// A sound's length in whole milliseconds (0 for an unknown handle).
pub def Audio.sound_duration_ms (s : Sound) : IO I64 :=
    IO.mk (audio_sound_duration_ms_raw s.id)
