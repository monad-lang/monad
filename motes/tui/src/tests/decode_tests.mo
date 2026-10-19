// Phase 6 decode tests: feed wire strings to `Input.decode` and
// assert the events. The decoder is pure, so every case is a plain
// `==` on the decoded list against a literal one (the derived `BEq`
// on `Event`).
//
// The leftover half of `decode`'s result gets as much attention as the
// events: an incomplete sequence MUST come back whole (from its ESC),
// because the reader's contract is to prefix it to the next chunk.

use lib::types { Event, Key, MouseEvent, MouseButton }
use lib::input { Input.decode, Input.pending_escape }
use std::list { List.length }

def decoded_events (s : String) : List Event :=
    match Input.decode s {
        Pair.pair evs _ => evs
    }

def decoded_leftover (s : String) : String :=
    match Input.decode s {
        Pair.pair _ left => left
    }

/// Element-wise list equality: comparing `List Event` values with `==`
/// rides the generic `BEq (List A)` instance, whose dispatch is the
/// runtime bug `core.mo`'s hand-rolled `Screen` instance exists to
/// avoid -- so these tests compare one element at a time.
def events_be (a : List Event) (b : List Event) : Bool :=
    match a {
        empty => List.length b == 0,
        cons x xs =>
            match b {
                empty => false,
                cons y ys => x == y && events_be xs ys
            }
    }

// ==================== single bytes ====================

#[test]
def test_printable_char : Bool :=
    events_be (decoded_events "a") [Event.key (Key.char "a")]
    && decoded_leftover "a" == ""

#[test]
def test_enter_both_wires : Bool :=
    events_be (decoded_events "\r") [Event.key Key.enter]
    && events_be (decoded_events "\n") [Event.key Key.enter]

#[test]
def test_tab_and_backspace : Bool :=
    events_be (decoded_events "\t") [Event.key Key.tab]
    && events_be (decoded_events "\u{7f}") [Event.key Key.backspace]
    && events_be (decoded_events "\u{8}") [Event.key Key.backspace]

#[test]
def test_ctrl_bytes : Bool :=
    events_be (decoded_events "\u{1}") [Event.key (Key.ctrl "a")]
    && events_be (decoded_events "\u{3}") [Event.key (Key.ctrl "c")]
    && events_be (decoded_events "\u{1a}") [Event.key (Key.ctrl "z")]

#[test]
def test_nul_dropped : Bool :=
    events_be (decoded_events "\u{0}") []

#[test]
def test_utf8_char : Bool :=
    events_be (decoded_events "\u{e9}") [Event.key (Key.char "\u{e9}")]
    && events_be (decoded_events "\u{20ac}") [Event.key (Key.char "\u{20ac}")]

#[test]
def test_batch_of_plain_keys : Bool :=
    events_be (decoded_events "ab\t") [
        Event.key (Key.char "a"),
        Event.key (Key.char "b"),
        Event.key Key.tab
    ]

#[test]
def test_utf8_in_a_batch : Bool :=
    events_be (decoded_events "a\u{20ac}\t") [
        Event.key (Key.char "a"),
        Event.key (Key.char "\u{20ac}"),
        Event.key Key.tab
    ]

// ==================== escape sequences ====================

#[test]
def test_arrows : Bool :=
    events_be (decoded_events "\u{1b}[A") [Event.key Key.up]
    && events_be (decoded_events "\u{1b}[B") [Event.key Key.down]
    && events_be (decoded_events "\u{1b}[C") [Event.key Key.right]
    && events_be (decoded_events "\u{1b}[D") [Event.key Key.left]

#[test]
def test_home_end : Bool :=
    events_be (decoded_events "\u{1b}[H") [Event.key Key.home]
    && events_be (decoded_events "\u{1b}[F") [Event.key Key.end]

#[test]
def test_tilde_keypad : Bool :=
    events_be (decoded_events "\u{1b}[1~") [Event.key Key.home]
    && events_be (decoded_events "\u{1b}[2~") [Event.key Key.insert]
    && events_be (decoded_events "\u{1b}[3~") [Event.key Key.delete]
    && events_be (decoded_events "\u{1b}[4~") [Event.key Key.end]
    && events_be (decoded_events "\u{1b}[5~") [Event.key Key.page_up]
    && events_be (decoded_events "\u{1b}[6~") [Event.key Key.page_down]
    && events_be (decoded_events "\u{1b}[7~") [Event.key Key.home]
    && events_be (decoded_events "\u{1b}[8~") [Event.key Key.end]

#[test]
def test_tilde_function_keys : Bool :=
    events_be (decoded_events "\u{1b}[11~") [Event.key (Key.function_key 1)]
    && events_be (decoded_events "\u{1b}[15~") [Event.key (Key.function_key 5)]
    && events_be (decoded_events "\u{1b}[17~") [Event.key (Key.function_key 6)]
    && events_be (decoded_events "\u{1b}[21~") [Event.key (Key.function_key 10)]
    && events_be (decoded_events "\u{1b}[23~") [Event.key (Key.function_key 11)]
    && events_be (decoded_events "\u{1b}[24~") [Event.key (Key.function_key 12)]

#[test]
def test_ss3_function_keys : Bool :=
    events_be (decoded_events "\u{1b}OP") [Event.key (Key.function_key 1)]
    && events_be (decoded_events "\u{1b}OQ") [Event.key (Key.function_key 2)]
    && events_be (decoded_events "\u{1b}OR") [Event.key (Key.function_key 3)]
    && events_be (decoded_events "\u{1b}OS") [Event.key (Key.function_key 4)]

#[test]
def test_ss3_home_end : Bool :=
    events_be (decoded_events "\u{1b}OH") [Event.key Key.home]
    && events_be (decoded_events "\u{1b}OF") [Event.key Key.end]

#[test]
def test_modifier_params_ignored : Bool :=
    events_be (decoded_events "\u{1b}[1;5A") [Event.key Key.up]
    && events_be (decoded_events "\u{1b}[5;5~") [Event.key Key.page_up]

#[test]
def test_unknown_sequence_dropped : Bool :=
    events_be (decoded_events "\u{1b}[99;98u") []
    && decoded_leftover "\u{1b}[99;98u" == ""

#[test]
def test_alt_char : Bool :=
    events_be (decoded_events "\u{1b}a") [Event.key (Key.alt "a")]

#[test]
def test_esc_esc_emits_one_escape : Bool :=
    events_be (decoded_events "\u{1b}\u{1b}") [Event.key Key.escape]

// ==================== leftover: incomplete sequences ====================

#[test]
def test_lone_trailing_esc_kept : Bool :=
    events_be (decoded_events "\u{1b}") []
    && decoded_leftover "\u{1b}" == "\u{1b}"

#[test]
def test_partial_csi_kept_whole : Bool :=
    events_be (decoded_events "\u{1b}[") []
    && decoded_leftover "\u{1b}[" == "\u{1b}["
    && events_be (decoded_events "\u{1b}[<0;1") []
    && decoded_leftover "\u{1b}[<0;1" == "\u{1b}[<0;1"

#[test]
def test_partial_ss3_kept_whole : Bool :=
    events_be (decoded_events "\u{1b}O") []
    && decoded_leftover "\u{1b}O" == "\u{1b}O"

#[test]
def test_split_sequence_completes_next_call : Bool :=
    // First chunk leaves the whole prefix; the reader prepends it to
    // the next chunk and the sequence decodes as one.
    let left := decoded_leftover "\u{1b}[<0;1" in
    match Input.decode (left ++ ";2M") {
        Pair.pair evs _ => events_be evs [Event.mouse (MouseEvent.press MouseButton.left 1 0)]
    }

#[test]
def test_pending_escape_recognition : Bool :=
    Input.pending_escape "\u{1b}"
    && Bool.not (Input.pending_escape "\u{1b}[")
    && Bool.not (Input.pending_escape "")

// ==================== SGR mouse ====================

#[test]
def test_mouse_press : Bool :=
    // ESC [ < 0 ; 10 ; 5 M = left press, 1-based (col 10, row 5)
    events_be (decoded_events "\u{1b}[<0;10;5M") [
        Event.mouse (MouseEvent.press MouseButton.left 4 9)
    ]

#[test]
def test_mouse_release : Bool :=
    events_be (decoded_events "\u{1b}[<2;3;4m") [
        Event.mouse (MouseEvent.release MouseButton.right 3 2)
    ]

#[test]
def test_mouse_drag : Bool :=
    events_be (decoded_events "\u{1b}[<32;8;2M") [
        Event.mouse (MouseEvent.drag MouseButton.left 1 7)
    ]

#[test]
def test_mouse_middle_press : Bool :=
    events_be (decoded_events "\u{1b}[<1;1;1M") [
        Event.mouse (MouseEvent.press MouseButton.middle 0 0)
    ]

#[test]
def test_mouse_wheel : Bool :=
    events_be (decoded_events "\u{1b}[<64;80;24M") [
        Event.mouse (MouseEvent.scroll_up 23 79)
    ]
    && events_be (decoded_events "\u{1b}[<65;80;24M") [
        Event.mouse (MouseEvent.scroll_down 23 79)
    ]

#[test]
def test_mixed_batch : Bool :=
    events_be (decoded_events "a\u{1b}[D\u{1b}[<0;5;5M") [
        Event.key (Key.char "a"),
        Event.key Key.left,
        Event.mouse (MouseEvent.press MouseButton.left 4 4)
    ]

// ==================== bracketed paste ====================

#[test]
def test_paste_in_one_buffer : Bool :=
    events_be (decoded_events "\u{1b}[200~hello\u{1b}[201~") [Event.paste "hello"]

#[test]
def test_empty_paste : Bool :=
    events_be (decoded_events "\u{1b}[200~\u{1b}[201~") [Event.paste ""]

#[test]
def test_paste_content_is_literal : Bool :=
    events_be (decoded_events "\u{1b}[200~a\n\tb\u{1b}[A\u{1b}[201~") [Event.paste "a\n\tb\u{1b}[A"]

#[test]
def test_keys_around_a_paste : Bool :=
    events_be (decoded_events "x\u{1b}[200~hi\u{1b}[201~y")
        [Event.key (Key.char "x"), Event.paste "hi", Event.key (Key.char "y")]

#[test]
def test_incomplete_paste_is_the_whole_leftover : Bool :=
    let buf := "\u{1b}[200~half" in
    List.length (decoded_events buf) == 0 && decoded_leftover buf == buf

#[test]
def test_paste_split_across_calls : Bool :=
    let first := "\u{1b}[200~hal" in
    let rest := String.concat (decoded_leftover first) "lo\u{1b}[201~" in
    events_be (decoded_events rest) [Event.paste "hallo"]

#[test]
def test_pending_escape_false_during_a_paste : Bool :=
    Bool.not (Input.pending_escape (decoded_leftover "\u{1b}[200~\u{1b}"))
        && Bool.not (Input.pending_escape (decoded_leftover "\u{1b}[20"))
