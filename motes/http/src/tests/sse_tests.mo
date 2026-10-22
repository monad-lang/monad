/// SSE state machine tests — byte pushes in, events out.

use http::sse {
  Sse.encode, Sse.encode_comment, Sse.encode_event, Sse.encode_retry,
  Sse.init, Sse.push, Sse.response, SseEvent,
}
use http::types {Body.is_stream, Headers.get}

/// Push a whole string's bytes through a fresh state.
def feed (s : String) : List SseEvent :=
  match Sse.push Sse.init (String.to_list s) {
    Pair.pair _ evs => evs
  }

/// Push a first string, keep the state, push a second: the events of the
/// second push (which is where a split event must complete).
def feed_split (s1 : String) (s2 : String) : List SseEvent :=
  match Sse.push Sse.init (String.to_list s1) {
    Pair.pair st _ =>
      match Sse.push st (String.to_list s2) {
        Pair.pair _ evs => evs
      }
  }

/// The list is exactly one event, and it is `(event, data)`.
def one_event (evs : List SseEvent) (ev : String) (data : String) : Bool :=
  match evs {
    List.empty => false,
    List.cons e rest =>
      List.is_empty rest && e.event == ev && e.data == data
  }

/// The list is exactly two events, in order.
def two_events (evs : List SseEvent) (e1 : SseEvent) (e2 : SseEvent) : Bool :=
  match evs {
    List.cons a rest =>
      match rest {
        List.cons b rest2 =>
          List.is_empty rest2
            && a.event == e1.event && a.data == e1.data
            && b.event == e2.event && b.data == e2.data,
        List.empty => false
      },
    List.empty => false
  }

#[test]
def test_single_event : Bool :=
  one_event (feed "data: hello\n\n") "" "hello"

#[test]
def test_two_events_one_push : Bool :=
  two_events (feed "data: one\n\ndata: two\n\n")
    { event := "", data := "one" }
    { event := "", data := "two" }

#[test]
def test_event_split_mid_line : Bool :=
  one_event (feed_split "data: he" "llo\n\n") "" "hello"

#[test]
def test_event_split_at_blank_line : Bool :=
  one_event (feed_split "data: a\n" "\n") "" "a"

#[test]
def test_partial_line_emits_nothing : Bool :=
  match Sse.push Sse.init (String.to_list "data: partial") {
    Pair.pair _ evs => List.is_empty evs
  }

#[test]
def test_partial_line_completes_on_next_push : Bool :=
  one_event (feed_split "data: partial" "\n\n") "" "partial"

#[test]
def test_data_lines_join_with_newline : Bool :=
  one_event (feed "data: a\ndata: b\n\n") "" "a\nb"

#[test]
def test_empty_data_value_still_dispatches : Bool :=
  one_event (feed "data:\n\n") "" ""

#[test]
def test_field_without_colon_is_empty_value : Bool :=
  one_event (feed "data\n\n") "" ""

#[test]
def test_event_field_names_event : Bool :=
  one_event (feed "event: ping\ndata: x\n\n") "ping" "x"

#[test]
def test_dispatch_resets_event_name : Bool :=
  two_events (feed "event: a\ndata: 1\n\ndata: 2\n\n")
    { event := "a", data := "1" }
    { event := "", data := "2" }

#[test]
def test_block_without_data_dispatches_nothing : Bool :=
  match Sse.push Sse.init (String.to_list "event: ping\n\n") {
    Pair.pair _ evs => List.is_empty evs
  }

#[test]
def test_comment_line_ignored : Bool :=
  one_event (feed ": keep-alive\n\ndata: x\n\n") "" "x"

#[test]
def test_id_and_retry_ignored : Bool :=
  one_event (feed "id: 7\nretry: 100\ndata: x\n\n") "" "x"

#[test]
def test_crlf_line_endings : Bool :=
  one_event (feed "event: ping\r\ndata: x\r\n\r\n") "ping" "x"

#[test]
def test_one_space_stripped_after_colon : Bool :=
  one_event (feed "data:  two spaces\n\n") "" " two spaces"

#[test]
def test_leading_blank_line_resets_and_continues : Bool :=
  one_event (feed "\ndata: x\n\n") "" "x"

#[test]
def test_json_payload_roundtrip : Bool :=
  let wire := "data: {\"delta\":\"hi\"}\n\ndata: [DONE]\n\n" in
  two_events (feed wire)
    { event := "", data := "{\"delta\":\"hi\"}" }
    { event := "", data := "[DONE]" }

// ── encoding (server side) ──

#[test]
def test_encode_event : Bool :=
  String.beq (Sse.encode_event "msg" "hi") "event: msg\ndata: hi\n\n"

#[test]
def test_encode_multiline : Bool :=
  String.beq (Sse.encode "a\nb") "data: a\ndata: b\n"

#[test]
def test_encode_comment : Bool :=
  String.beq (Sse.encode_comment "ping") ": ping\n"

#[test]
def test_encode_retry : Bool :=
  String.beq (Sse.encode_retry 500i64) "retry: 500\n"

#[test]
def test_response_is_event_stream : Bool :=
  let res := Sse.response (fn (_ : Unit) => IO.pure Option.none) in
  let ct := match Headers.get "Content-Type" res.headers {
    Option.some v => v,
    Option.none => ""
  } in
  Bool.and (Body.is_stream res.body) (String.beq ct "text/event-stream")
