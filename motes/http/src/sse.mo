/// Server-Sent Events — Layer 0, pure Monad.
///
/// The incremental half of the WHATWG SSE processing model: bytes go in,
/// complete events come out. The caller (moose consumers, the shuttle
/// harness) owns the transport; this file owns the line discipline:
///
/// - lines end at `\n`; one trailing `\r` is stripped, so both LF and CRLF
///   servers parse (a lone `\r` is NOT a terminator here -- the observed
///   OpenAI/Anthropic/Ollama wires are LF or CRLF, and half-splitting on a
///   bare CR is a body-reassembly question no caller has asked yet);
/// - a blank line (empty, or a bare `\r`) dispatches the event being built
///   and starts the next;
/// - `data:` appends its value to the event's data, pieces joined by `\n`;
/// - `event:` names the event; `:` starts a comment; anything else (`id`,
///   `retry`, unknown fields) is consumed and dropped;
/// - a field's value loses ONE leading space after its colon, and a line
///   with no colon is a field whose value is empty;
/// - a block with no `data` field dispatches nothing (spec: the data buffer
///   being empty means no event), and the event name resets with it.
///
/// `SseState.buf` holds every byte since the last dispatch, not just the
/// trailing partial line: an event is parsed only once its blank line
/// arrives, so `data: a\n` pushed alone is buffered whole and re-parsed
/// after the push that completes it.

use http::strings {Strings.drop_bytes, Strings.split_at_byte_opt, Strings.split_on}
use http::wire {Wire.take_bytes}
use http::types {
  Body, Headers, Headers.empty, Headers.set, HttpVersion, Response, Status.ok,
}
use std::list {List.intercalate}

pub struct SseState { buf : List U8 }

pub struct SseEvent { event : String, data : String }

/// A state with nothing buffered.
pub def Sse.init : SseState :=
  { buf := List.empty }

// ── encoding (server side) ──────────────────────────────────────────────

/// The `data:` lines for one event body; a multi-line value becomes one
/// `data:` line per line, as the spec requires.
pub def Sse.encode (data : String) : String :=
  String.concat_list (Sse.data_lines (Strings.split_on "\n" data))

#[terminating]
def Sse.data_lines (lines : List String) : List String :=
  match lines {
    List.empty => List.empty,
    List.cons line rest =>
      List.cons (String.concat "data: " (String.concat line "\n")) (Sse.data_lines rest)
  }

/// A named event followed by its data and the blank line that dispatches it.
pub def Sse.encode_event (name : String) (data : String) : String :=
  let event_line :=
    if String.is_empty name
    then ""
    else String.concat "event: " (String.concat name "\n") in
  String.concat event_line (String.concat (Sse.encode data) "\n")

pub def Sse.encode_comment (text : String) : String :=
  String.concat ": " (String.concat text "\n")

pub def Sse.encode_retry (ms : I64) : String :=
  String.concat "retry: " (String.concat (I64.to_string ms) "\n")

/// A body that pulls events from `source` and encodes them.
pub def Sse.body (source : Unit -> IO (Option SseEvent)) : Body :=
  Body.stream (fn (_ : Unit) => Sse.pull_event source)

def Sse.pull_event (source : Unit -> IO (Option SseEvent)) : IO (Option (List U8)) := do {
  let ev <- source Unit.unit;
  match ev {
    Option.none => IO.pure Option.none,
    Option.some e => IO.pure (Option.some (String.to_list (Sse.encode_event e.event e.data)))
  }
}

/// A 200 `text/event-stream` response whose body is the event source.
pub def Sse.response (source : Unit -> IO (Option SseEvent)) : Response :=
  let h1 := Headers.set "Content-Type" "text/event-stream" Headers.empty in
  let h2 := Headers.set "Cache-Control" "no-cache" h1 in
  let h3 := Headers.set "X-Accel-Buffering" "no" h2 in
  let res : Response :=
    { status := Status.ok, headers := h3, version := HttpVersion.http1_1, body := Sse.body source } in
  res

/// Feed `bytes` into the state machine: the new state and every event the
/// push completed, in the order the wire dispatched them.
pub def Sse.push (st : SseState) (bytes : List U8) : Pair SseState (List SseEvent) :=
  Sse.push_go (List.append st.buf bytes) List.empty

#[terminating]
def Sse.push_go (buf : List U8) (out : List SseEvent) : Pair SseState (List SseEvent) :=
  match Sse.scan_lines buf 0i64 0i64 true {
    Option.none =>
      let st : SseState := { buf := buf } in
      Pair.pair st (List.reverse out),
    Option.some pr =>
      match pr {
        Pair.pair block_end next_start =>
          match Sse.parse_block (Wire.take_bytes block_end buf) {
            Option.none => Sse.push_go (Strings.drop_bytes next_start buf) out,
            Option.some ev => Sse.push_go (Strings.drop_bytes next_start buf) (List.cons ev out)
          }
      }
  }

/// Find the first blank line in `bytes`. `Option.none` when no blank line is
/// fully buffered; `Option.some (block_end, next_start)` where `block_end` is
/// where the line's bytes begin (everything before it is the block to parse)
/// and `next_start` is the first byte after the line's `\n`. `blank` carries
/// "every byte of the current line so far has been `\r`", which is what makes
/// a bare-`\r` line blank without looking behind.
#[terminating]
def Sse.scan_lines (bytes : List U8) (idx : I64) (line_start : I64) (blank : Bool) : Option (Pair I64 I64) :=
  match bytes {
    List.empty => Option.none,
    List.cons x rest =>
      if x == 10u8
      then
        if blank
        then Option.some (Pair.pair line_start (I64.add idx 1i64))
        else Sse.scan_lines rest (I64.add idx 1i64) (I64.add idx 1i64) true
      else Sse.scan_lines rest (I64.add idx 1i64) line_start (Bool.and blank (x == 13u8))
  }

/// Parse one event block (its blank line excluded) into the event it
/// dispatches, or none when it carries no `data` field.
def Sse.parse_block (block : List U8) : Option SseEvent :=
  Sse.parse_lines block "" List.empty

#[terminating]
def Sse.parse_lines (block : List U8) (event : String) (data : List String) : Option SseEvent :=
  match block {
    List.empty => Sse.finish_event event data,
    List.cons _ _ =>
      match Sse.take_line block {
        Pair.pair line rest =>
          match Sse.apply_field (Sse.strip_cr line) event data {
            Pair.pair event2 data2 => Sse.parse_lines rest event2 data2
          }
      }
  }

/// The block's accumulated answer: an event when any `data` field was seen,
/// none otherwise. The trailing `\n` the spec's data buffer would end with
/// is the one `List.intercalate` never adds, so the join IS the spec's
/// strip-the-final-newline step.
def Sse.finish_event (event : String) (data : List String) : Option SseEvent :=
  match data {
    List.empty => Option.none,
    List.cons _ _ =>
      let joined : String := List.intercalate "\n" data in
      Option.some ({ event := event, data := joined } : SseEvent)
  }

/// Fold one field line into the accumulator. A line starting with `:` is a
/// comment; the split at the first other `:` is the field name/value
/// boundary, and a missing colon means the whole line names a field with an
/// empty value.
def Sse.apply_field (line : List U8) (event : String) (data : List String) : Pair String (List String) :=
  match line {
    List.empty => Pair.pair event data,
    List.cons c _ =>
      if c == 58u8
      then Pair.pair event data
      else
        match Strings.split_at_byte_opt 58u8 line {
          Option.none => Sse.apply_named line List.empty event data,
          Option.some sp =>
            match sp {
              Pair.pair name_b val_b => Sse.apply_named name_b (Sse.drop_leading_space val_b) event data
            }
        }
  }

/// Apply a named field. Only `data` and `event` change the accumulator;
/// everything a server sends for the caller's benefit (`id`, `retry`,
/// extensions) is consumed here and dropped.
def Sse.apply_named (name_b : List U8) (val_b : List U8) (event : String) (data : List String) : Pair String (List String) :=
  let name : String := String.from_list name_b in
  if name == "data"
  then
    let v : String := String.from_list val_b in
    Pair.pair event (List.append data (List.singleton v))
  else if name == "event"
  then
    let v : String := String.from_list val_b in
    Pair.pair v data
  else Pair.pair event data

/// Split at the first `\n`: the line before it (terminator excluded) and
/// every byte after it.
def Sse.take_line (bytes : List U8) : Pair (List U8) (List U8) :=
  Sse.take_line_go bytes List.empty

def Sse.take_line_go (bytes : List U8) (acc : List U8) : Pair (List U8) (List U8) :=
  match bytes {
    List.empty => Pair.pair (List.reverse acc) List.empty,
    List.cons x rest =>
      if x == 10u8
      then Pair.pair (List.reverse acc) rest
      else Sse.take_line_go rest (List.cons x acc)
  }

/// One trailing `\r`, gone -- the CRLF half of the line discipline.
def Sse.strip_cr (line : List U8) : List U8 :=
  match List.reverse line {
    List.empty => List.empty,
    List.cons x rest => if x == 13u8 then List.reverse rest else line
  }

/// One leading space after a field's colon, gone -- exactly one, so
/// `data:  x` carries " x" the way the spec says it does.
def Sse.drop_leading_space (bytes : List U8) : List U8 :=
  match bytes {
    List.empty => List.empty,
    List.cons x rest => if x == 32u8 then rest else bytes
  }
