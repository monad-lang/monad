/// The sound-effect vocabulary shared by the browser boundary and the view
/// layer: what an app asks the runtime to play, declared as DATA so an
/// `update` stays pure.
///
/// The split mirrors `WsEvent`'s: `web_wasm::audio` performs the calls,
/// `oak` names a `SoundFx` in `Command.sound`, and `oak_wasm` turns one
/// into the other. Nothing here is IO, nothing holds a handle, and nothing
/// needs `web_wasm` to compile -- which is what lets a pure `update` return
/// `Command.sound (SoundFx.beep 880.0)` and be testable on any target.
///
/// **Not the same as music.** This is a short synthesized or preloaded
/// sound: an SFX fired by a game tick. A long track the user scrubs is an
/// `<audio>` element, and `MediaCmd` below drives that one.

/// A short sound, described by what it is rather than how it is made.
pub type SoundFx {
    /// An oscillator note: `freq` in Hz, `gain` peak 0..1, and how long it
    /// sounds (`duration_ms`).
    beep (wave : Wave) (freq : F64) (gain : F64) (duration_ms : I64),
    /// A percussive hit: a white-noise burst through a lowpass
    /// (`lowpass_hz` 0 = unfiltered), `gain` peak, `duration_ms` long.
    hit (gain : F64) (duration_ms : I64) (lowpass_hz : F64),
    /// A sound decoded from a URL. The runtime fetches and decodes it on
    /// first use and plays it once ready, so `update` need not know whether
    /// the bytes are in memory yet.
    file (url : String) (gain : F64),
    /// Stop everything this app started (an "alarm off", a `quit`).
    silence
}

/// The waveform codes. Declared here, not in `web_wasm`, so a pure
/// `SoundFx.beep` names one; `web_wasm::audio`'s `Wave` is the same order
/// (`wasm/web/web_runtime.js`'s `OSC_TYPES`), which is the wire contract.
pub type Wave {
    sine,
    square,
    sawtooth,
    triangle
}

/// The `<audio>`/`<video>` transport action a view can ask for, addressed by
/// the element's selector. Declared as data for the same reason as
/// `SoundFx`: a `update` that returns `Command.media` stays pure.
pub type MediaCmd {
    /// Start playback. The runtime reports a policy block as a message when
    /// the command carries one (`play`), otherwise silently.
    play (selector : String),
    pause (selector : String),
    /// Seek to `ms` from the start.
    seek (selector : String) (ms : I64),
    /// `volume` 0..1.
    volume (selector : String) (volume : F64),
    mute (selector : String),
    unmute (selector : String),
    /// Loop (background music) or not.
    loop (selector : String)
}

/// Whether a `SoundFx` makes no sound (`silence`), so the runtime can skip
/// allocating a context for it.
pub def SoundFx.is_silence (fx : SoundFx) : Bool :=
    match fx {
        SoundFx.silence => true,
        _ => false
    }

/// The `Wave` code the host table indexes by. The order is the wire
/// contract, so this is the only place it is written down.
pub def Wave.code (w : Wave) : I64 :=
    match w {
        Wave.sine => 0i64,
        Wave.square => 1i64,
        Wave.sawtooth => 2i64,
        Wave.triangle => 3i64
    }
