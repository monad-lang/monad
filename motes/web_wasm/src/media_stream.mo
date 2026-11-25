/// Camera, microphone and screen capture: the `getUserMedia` family, and
/// getting a stream onto a `<video>` (or a peer connection).
///
/// `getUserMedia` is TWO-PHASE, because it is promise-based and a JS promise
/// callback must not re-enter wasm while a Monad frame is on the stack: the
/// same shape `Fetch`, `Clipboard` and `Crypto` use. `begin` starts the
/// browser's permission prompt and returns an op; the caller drives `poll`
/// from its own frame loop (0 pending, 1 done, 2 failed) and then reads the
/// stream with `result`.
///
/// A denied prompt is a normal answer, not a crash: `poll` answers 2 and
/// `MediaStream.error` gives the DOMException name -- `NotAllowedError` for a
/// refused permission, `NotFoundError` for a machine with no camera. A UI
/// should report it; it should not retry in a loop.
///
/// `MediaStream` is `#[opaque]` (see `lib::types`): it has no useful default
/// value, and the only ways to obtain one are `result` and the stream a
/// remote peer sends.
///
/// Constraints cross as the browser's own `MediaStreamConstraints` JSON text
/// rather than as a typed record. The shape is large, browser-dependent and
/// mostly used at its defaults (`{"audio": true, "video": {"width": 640}}`),
/// so a Monad record would freeze a moving target; the JSON is passed
/// straight through and the host does not parse it.

use lib::types {MediaStream, MediaStreamOp, Node}
use lib::ffi {
    media_get_begin_raw, media_poll_raw, media_stream_raw, media_error_raw,
    media_free_raw, media_free_op_raw, media_stream_of_raw, dom_set_src_object_raw,
}

// ─── Poll answers ────────────────────────────────────────────────────
//
// The same three numbers `Fetch`, `Clipboard` and `Crypto` answer with, and
// the same ones `wasm/web/web_runtime.js` writes.
pub def MediaStream.poll_pending : I64 := 0i64
pub def MediaStream.poll_done : I64 := 1i64
pub def MediaStream.poll_failed : I64 := 2i64

// ─── Obtaining a stream ──────────────────────────────────────────────

/// Start a `getUserMedia` request. `constraints` is the browser's
/// `MediaStreamConstraints` JSON text, passed through unchanged:
///
///     MediaStream.get_user_media_begin "{\"audio\": true, \"video\": true}"
///
/// The permission prompt starts here; the answer arrives through `poll`.
pub def MediaStream.get_user_media_begin (constraints : String) : IO MediaStreamOp :=
    IO.mk (media_get_begin_raw constraints 0i64)

/// A camera-and-microphone request with sensible defaults.
pub def MediaStream.request_av : IO MediaStreamOp :=
    MediaStream.get_user_media_begin "{\"audio\": true, \"video\": true}"

/// Camera only.
pub def MediaStream.request_video : IO MediaStreamOp :=
    MediaStream.get_user_media_begin "{\"audio\": false, \"video\": true}"

/// Microphone only.
pub def MediaStream.request_audio : IO MediaStreamOp :=
    MediaStream.get_user_media_begin "{\"audio\": true, \"video\": false}"

/// Screen capture through `getDisplayMedia`, with `options` as the browser's
/// `DisplayMediaStreamOptions` JSON text.
///
/// The `display` flag on the native is what picks the API: `displaySurface`
/// is a `getDisplayMedia` constraint and NOT a `getUserMedia` one, so routing
/// this through `get_user_media_begin` would ask for a camera instead and
/// open one when the app asked for a screen.
pub def MediaStream.get_display_media_begin (options : String) : IO MediaStreamOp :=
    IO.mk (media_get_begin_raw options 1i64)

/// Screen capture of a whole monitor, with sensible defaults. The browser
/// shows its own picker, and a refusal comes back through `poll`/`error` like
/// a camera denial.
pub def MediaStream.request_display : IO MediaStreamOp :=
    MediaStream.get_display_media_begin "{\"video\": {\"displaySurface\": \"monitor\"}}"

/// 0 pending, 1 done, 2 failed -- the fetch convention.
pub def MediaStream.poll (op : MediaStreamOp) : IO I64 := IO.mk (media_poll_raw op)

/// The stream the operation produced. Only meaningful once `poll` answered 1;
/// before that it is the null handle, which `attach` and `Rtc.add_stream`
/// both refuse.
pub def MediaStream.result (op : MediaStreamOp) : IO MediaStream := IO.mk (media_stream_raw op)

/// The DOMException name a failed request reported (`NotAllowedError`,
/// `NotFoundError`, `NotReadableError`, ...), or `""` when it has not failed.
pub def MediaStream.error (op : MediaStreamOp) : IO String := IO.mk (media_error_raw op)

/// Drive `poll` up to `max_ticks` times. See `Crypto.await_op`: a UI MUST
/// poll from its own frame loop instead, because a promise cannot settle
/// while an export is on the stack, so in a browser this can only time out.
/// It is for a one-shot command, or for an op that settled between exports.
#[terminating]
pub def MediaStream.await (op : MediaStreamOp) (max_ticks : I64) : IO I64 :=
    MediaStream.await_go op max_ticks 0i64

#[terminating]
def MediaStream.await_go (op : MediaStreamOp) (max_ticks : I64) (tick : I64) : IO I64 := do {
    let state <- MediaStream.poll op;
    if I64.beq state MediaStream.poll_pending
    then
        if I64.gt tick max_ticks
        then IO.pure state
        else MediaStream.await_go op max_ticks (I64.add tick 1i64)
    else IO.pure state
}

// ─── Displaying a stream ─────────────────────────────────────────────

/// Play `stream` in `video` (a `<video>` or `<audio>` node) by setting its
/// `srcObject`.
///
/// This is the ONLY object-property write in the web boundary, and it is
/// typed on purpose: it takes a node and a stream, never a property NAME, so
/// it cannot set an arbitrary JS property.
///
/// `Err` when the node is not a media element or the stream is the null
/// handle. Playback still needs the element's own `autoplay`/`play()`
/// affordance, which the browser gates on the same user gesture that granted
/// the stream.
pub def MediaStream.attach (stream : MediaStream) (video : Node) : IO (Result String Unit) := do {
    let ok <- IO.mk (dom_set_src_object_raw video stream);
    if I64.beq ok 0i64
    then IO.pure (Result.err "the node is not a <video>/<audio> element, or the stream is empty")
    else IO.pure (Result.ok unit)
}

/// Stop every track and release the stream's host slot, along with the op
/// that produced it. The camera light goes out here, so a UI that stops
/// showing a stream should call it rather than just dropping the handle.
pub def MediaStream.stop (stream : MediaStream) : IO Unit := do {
    let _ <- IO.mk (media_free_raw stream);
    IO.pure unit
}

/// The stream a `RtcEvent.track` id names, as a typed handle.
///
/// `RtcEvent.track` carries a bare `I64` because the pure layer must not name
/// a `web_wasm` handle type; this is the bridge back. The null handle comes
/// back for an id whose slot is gone (a stream already `stop`ped), which
/// `attach` and `Rtc.add_stream` both refuse, so a stale id is inert rather
/// than dangerous.
pub def MediaStream.of_track (id : I64) : IO MediaStream :=
    IO.mk (media_stream_of_raw id)

/// Release a finished operation's host slot, for a request that FAILED and so
/// produced no stream to `stop`. Without it a page that retries a refused
/// prompt would keep one record per attempt for its whole lifetime.
///
/// A successful op is reclaimed by `MediaStream.stop`, so calling this on one
/// is harmless but unnecessary.
pub def MediaStream.release (op : MediaStreamOp) : IO Unit := do {
    let _ <- IO.mk (media_free_op_raw op);
    IO.pure unit
}
