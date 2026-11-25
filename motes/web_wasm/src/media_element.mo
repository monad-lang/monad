/// `<audio>` / `<video>` element control: play, pause, seek, volume and the
/// state an app needs to render a transport bar.
///
/// The ELEMENT is mounted by the view (`Html.audio`/`Html.video`), so every
/// call reaches it by SELECTOR, exactly as `Dom.focus` does:
///
/// ```monad
/// Html.audio [Html.id_ "player", Html.src "/song.mp3", Html.controls] []
/// // ... then, from an effect:
/// let _ <- MediaElement.play "#player";
/// ```
///
/// This is the *file* half of the audio surface: a long track that the
/// browser streams and the user scrubs. A short synthesized or decoded
/// sound is `web_wasm::audio` instead -- an `AudioContext` is the wrong tool
/// for a five-minute mp3 (it would decode the whole file into memory), and a
/// media element cannot mix a dozen overlapping SFX.
///
/// **Why a selector, not a handle.** A media element's state lives in the
/// DOM the view owns; a handle would have to be invalidated by every patch
/// that replaced the node. A selector re-resolves each call, so a re-render
/// cannot leave a stale handle behind. The cost is a lookup per call, which
/// is why this is for transport actions, not per-frame reads.
///
/// Every setter answers `false` when no element matched: a selector typo is
/// silent in the DOM, so the flag is the only signal a caller gets.
///
/// `Html.audio`'s `autoplay` attribute is deliberately NOT the mechanism: a
/// policy that blocks it fails silently. `MediaElement.play` reports the
/// block as `PlayOutcome.blocked` instead.

use lib::ffi {
    media_play_raw, media_pause_raw, media_seek_raw, media_set_volume_raw,
    media_set_muted_raw, media_set_loop_raw, media_info_raw, media_time_ms_raw,
    media_volume_raw,
}

/// How a `play` ended. The three cases are the ones a UI must distinguish:
/// playing, no such element, and the browser's autoplay policy.
pub type PlayOutcome {
    /// The element is playing.
    playing,
    /// No `<audio>`/`<video>` matched the selector.
    missing,
    /// The browser refused until a user gesture (a `NotAllowedError`). The
    /// fix is to start playback from a click handler, not to retry.
    blocked
}

/// The `HTMLMediaElement.readyState` codes, named.
pub type ReadyState {
    /// No information about the media at all.
    nothing,
    /// Enough to know the duration, not to render a frame.
    metadata,
    /// Renderable at the current position, but not enough to play on.
    current_data,
    /// Enough buffered to play through for a while.
    future_data,
    /// Enough for the current position and beyond.
    enough_data
}

/// One element's transport state, as one read. A view that renders a player
/// wants all of these together, so this is one snapshot rather than eight
/// calls whose answers could disagree.
pub struct MediaState {
    /// No `<audio>`/`<video>` matched; every other field is then a default.
    present : Bool := false,
    playing : Bool := false,
    ended : Bool := false,
    muted : Bool := false,
    looping : Bool := false,
    seeking : Bool := false,
    ready_state : ReadyState := ReadyState.nothing,
    /// `currentTime` in milliseconds.
    position_ms : I64 := 0,
    /// `duration` in milliseconds, or -1 while metadata has not arrived.
    duration_ms : I64 := -1,
    volume : F64 := 1.0
}

// The `which` selectors the host numbers (`media_info` in
// `wasm/web/web_runtime.js`). Each is one word read.
def info_paused : I64 := 0i64
def info_ended : I64 := 1i64
def info_ready : I64 := 2i64
def info_seeking : I64 := 3i64
def info_muted : I64 := 4i64
def info_looping : I64 := 5i64
def info_blocked : I64 := 7i64
def info_present : I64 := 8i64
def time_current : I64 := 0i64
def time_duration : I64 := 1i64

/// 1 = paused (the host reports `paused`, so this flips it: `playing`).
def is_set (v : I64) : Bool := I64.beq v 1i64

/// `readyState` 0..4 -> `ReadyState`. An unknown value reads `nothing`,
/// which is the safe answer for a state a new browser might add.
def ready_of (raw : I64) : ReadyState :=
    if I64.beq raw 1i64 then ReadyState.metadata
    else if I64.beq raw 2i64 then ReadyState.current_data
    else if I64.beq raw 3i64 then ReadyState.future_data
    else if I64.beq raw 4i64 then ReadyState.enough_data
    else ReadyState.nothing

/// Start playback. From a click handler's effect this always succeeds; from
/// a timer it may be `blocked` by the autoplay policy, which is a fact to
/// display (a "tap to play" affordance), not an error to retry.
pub def MediaElement.play (selector : String) : IO PlayOutcome := do {
    let r <- IO.mk (media_play_raw selector);
    if I64.beq r 1i64 then IO.pure PlayOutcome.playing
    else if I64.beq r 0i64 then IO.pure PlayOutcome.missing
    else IO.pure PlayOutcome.blocked
}

/// Pause (and, per the browser, remember the position).
pub def MediaElement.pause (selector : String) : IO Bool := do {
    let ok <- IO.mk (media_pause_raw selector);
    IO.pure (is_set ok)
}

/// Seek to `ms` from the start; the host clamps to the duration.
pub def MediaElement.seek (selector : String) (ms : I64) : IO Bool := do {
    let ok <- IO.mk (media_seek_raw selector ms);
    IO.pure (is_set ok)
}

/// `volume` in 0..1 (clamped). Independent of `muted`, as the browser's is.
pub def MediaElement.set_volume (selector : String) (volume : F64) : IO Bool := do {
    let ok <- IO.mk (media_set_volume_raw selector volume);
    IO.pure (is_set ok)
}

pub def MediaElement.set_muted (selector : String) (muted : Bool) : IO Bool := do {
    let ok <- IO.mk (media_set_muted_raw selector (if muted then 1i64 else 0i64));
    IO.pure (is_set ok)
}

/// Loop the media: what background music wants, where restarting from
/// `ended` would drift a frame each pass.
pub def MediaElement.set_loop (selector : String) (looping : Bool) : IO Bool := do {
    let ok <- IO.mk (media_set_loop_raw selector (if looping then 1i64 else 0i64));
    IO.pure (is_set ok)
}

/// Whether an `<audio>`/`<video>` matches the selector at all -- the check a
/// view's effect should make before it reports a transport failure.
pub def MediaElement.present (selector : String) : IO Bool := do {
    let found <- IO.mk (media_info_raw selector info_present);
    IO.pure (is_set found)
}

/// Whether the browser's autoplay policy is holding playback back: the
/// element was asked to play and was refused for want of a user gesture.
/// A UI should show a "tap to play" affordance rather than retrying.
pub def MediaElement.play_blocked (selector : String) : IO Bool := do {
    let blocked <- IO.mk (media_info_raw selector info_blocked);
    IO.pure (is_set blocked)
}

/// The whole transport state in one read.
pub def MediaElement.state (selector : String) : IO MediaState := do {
    let found <- IO.mk (media_info_raw selector info_present);
    if Bool.not (is_set found)
    then IO.pure { present := false, ready_state := ReadyState.nothing }
    else do {
        let ready <- IO.mk (media_info_raw selector info_ready);
        let paused <- IO.mk (media_info_raw selector info_paused);
        let ended <- IO.mk (media_info_raw selector info_ended);
        let seeking <- IO.mk (media_info_raw selector info_seeking);
        let muted <- IO.mk (media_info_raw selector info_muted);
        let looping <- IO.mk (media_info_raw selector info_looping);
        let position <- IO.mk (media_time_ms_raw selector time_current);
        let duration <- IO.mk (media_time_ms_raw selector time_duration);
        let volume <- IO.mk (media_volume_raw selector);
        let snapshot : MediaState :=
            { present := true,
                playing := Bool.not (is_set paused),
                ended := is_set ended,
                muted := is_set muted,
                looping := is_set looping,
                seeking := is_set seeking,
                ready_state := ready_of ready,
                position_ms := position,
                duration_ms := duration,
                volume := volume };
        IO.pure snapshot
    }
}

/// `currentTime` in milliseconds.
pub def MediaElement.position_ms (selector : String) : IO I64 :=
    IO.mk (media_time_ms_raw selector time_current)

/// `duration` in milliseconds, or -1 while metadata has not arrived (a
/// stream, or a file still loading). A caller rendering a scrub bar should
/// treat -1 as "not yet known", not as a zero-length clip.
pub def MediaElement.duration_ms (selector : String) : IO I64 :=
    IO.mk (media_time_ms_raw selector time_duration)

/// `volume` 0..1 (1 when no element matched).
pub def MediaElement.volume (selector : String) : IO F64 := IO.mk (media_volume_raw selector)
