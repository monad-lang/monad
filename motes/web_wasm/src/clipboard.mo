/// Asynchronous `navigator.clipboard`, two-phase like `fetch`.
///
/// `readText`/`writeText` return promises, and a promise callback must not
/// re-enter wasm while a Monad frame is on the stack. `*_begin` starts the
/// operation and returns an opaque id; `poll` reports 0 pending / 1 done /
/// 2 error; `read`/`error` copy the result out. `*_result` folds that into a
/// `Result`.
///
/// Writing needs a transient user activation: start it from an effect that
/// runs close to a click (the next animation-frame tick is usually still
/// inside the activation window). Text only in v1.

use lib::types {ClipboardOp}
use lib::ffi {
  clipboard_available_raw, clipboard_read_begin_raw, clipboard_write_begin_raw,
  clipboard_poll_raw, clipboard_read_raw, clipboard_error_raw,
}

pub def Clipboard.available : IO Bool := do {
    let v <- IO.mk clipboard_available_raw;
    IO.pure (I64.beq v 1i64)
}

/// Start reading text from the clipboard.
pub def Clipboard.read_begin : IO ClipboardOp := IO.mk clipboard_read_begin_raw

/// Start writing text to the clipboard.
pub def Clipboard.write_begin (text : String) : IO ClipboardOp :=
    IO.mk (clipboard_write_begin_raw text)

/// 0 pending, 1 done, 2 error.
pub def Clipboard.poll (op : ClipboardOp) : IO I64 := IO.mk (clipboard_poll_raw op)

/// The text a completed read produced (empty otherwise).
pub def Clipboard.read (op : ClipboardOp) : IO String := IO.mk (clipboard_read_raw op)

/// The `DOMException.name` a failed operation produced (empty otherwise).
pub def Clipboard.error (op : ClipboardOp) : IO String := IO.mk (clipboard_error_raw op)

/// `Ok None` pending, `Ok (Some text)` done, `Err name` failed.
pub def Clipboard.read_result (op : ClipboardOp) : IO (Result String (Option String)) := do {
    let state <- Clipboard.poll op;
    if I64.beq state 1i64
    then do {
        let text <- Clipboard.read op;
        IO.pure (Result.ok (Option.some text))
    }
    else if I64.beq state 2i64
    then do {
        let name <- Clipboard.error op;
        IO.pure (Result.err name)
    }
    else IO.pure (Result.ok Option.none)
}

/// `Ok false` pending, `Ok true` done, `Err name` failed.
pub def Clipboard.write_result (op : ClipboardOp) : IO (Result String Bool) := do {
    let state <- Clipboard.poll op;
    if I64.beq state 1i64
    then IO.pure (Result.ok true)
    else if I64.beq state 2i64
    then do {
        let name <- Clipboard.error op;
        IO.pure (Result.err name)
    }
    else IO.pure (Result.ok false)
}
