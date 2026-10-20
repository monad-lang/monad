/// Tests for the text input state machine (`motes/tui/src/widgets/
/// input.mo`).
///
/// A separate file because the state machine's module is re-exported by
/// the mote's `lib.mo` (the same undiscoverable-`#[test]`-in-a-re-export
/// rule `std/src/process_tests.mo` records). Same mote, so the
/// package-private helpers stay reachable without widening any API.
///
/// `state_is` compares field by field rather than building a `Pair` and
/// comparing with `==`: generic `BEq (Pair A B)` dispatch is the
/// unreliable path this mote avoids throughout.

use lib::widgets::input {InputState, InputLine, input_state, handle_input_key, handle_input_multiline_key, input_line_move, input_lines, cursor_line, insert_text}
use lib::types {Key}

/// All three fields of `st` at once, compared directly.
def state_is (value : String) (cursor : I64) (placeholder : String) (st : InputState) : Bool :=
    st.value == value && st.cursor == cursor && st.placeholder == placeholder

/// `input_state value ph` with the cursor moved to `cursor`.
def at_cursor (value : String) (cursor : I64) (placeholder : String) : InputState :=
    let st : InputState := input_state value placeholder in
    { st with cursor := cursor }

#[test]
def test_input_state_builds_cursor_at_end : Bool :=
    state_is "ab" 2 "ph" (input_state "ab" "ph")

#[test]
def test_input_state_empty_value : Bool :=
    state_is "" 0 "Search" (input_state "" "Search")

#[test]
def test_input_insert_at_end : Bool :=
    state_is "abc" 3 "" (handle_input_key (Key.char "c") (input_state "ab" ""))

#[test]
def test_input_insert_in_middle : Bool :=
    state_is "abcd" 3 "" (handle_input_key (Key.char "bc") (at_cursor "ad" 1 ""))

#[test]
def test_input_insert_multibyte_advances_by_bytes : Bool :=
    state_is "aæd" 3 "" (handle_input_key (Key.char "æ") (at_cursor "ad" 1 ""))

#[test]
def test_backspace_deletes_a_whole_multibyte_char : Bool :=
    state_is "a" 1 "" (handle_input_key Key.backspace (at_cursor "aæ" 3 ""))

#[test]
def test_left_right_cross_a_multibyte_char_in_one_step : Bool :=
    let st : InputState := at_cursor "aæ" 3 "" in
    let left : InputState := handle_input_key Key.left st in
    let right : InputState := handle_input_key Key.right left in
    state_is "aæ" 1 "" left && state_is "aæ" 3 "" right

// ── multiline (Phase 11b, the input pass) ────────────────────────────────

#[partial]
def line_at (ls : List InputLine) (i : I64) : InputLine :=
    match ls {
        List.empty => { start := 0, len := 0 },
        List.cons h rest => if i < 1 then h else line_at rest (i - 1),
    }

#[test]
def test_input_lines_trailing_newline_makes_a_last_empty_line : Bool :=
    let ls : List InputLine := input_lines "a\n" 0 in
    line_at ls 1 == ({ start := 2, len := 0 } : InputLine)

#[test]
def test_alt_enter_inserts_a_newline : Bool :=
    state_is "a\n" 2 "" (handle_input_multiline_key (Key.alt "\r") (input_state "a" ""))

// "a\nb", cursor at the end (byte 3, line 2): up keeps the column (1)
// and lands on line 2's end byte (line one is a single char).
#[test]
def test_line_move_up_from_line_two : Bool :=
    state_is "a\nb" 1 "" (input_line_move (0 - 1) (at_cursor "a\nb" 3 ""))

#[test]
def test_line_move_down_clamps_at_the_last_line : Bool :=
    state_is "a" 1 "" (input_line_move 1 (at_cursor "a" 1 ""))

#[test]
def test_multiline_handler_passes_single_line_keys_through : Bool :=
    state_is "abx" 3 "" (handle_input_multiline_key (Key.char "x") (input_state "ab" ""))

#[test]
def test_input_backspace_at_start_is_noop : Bool :=
    state_is "ab" 0 "" (handle_input_key Key.backspace (at_cursor "ab" 0 ""))

#[test]
def test_input_backspace_in_middle : Bool :=
    state_is "acd" 1 "" (handle_input_key Key.backspace (at_cursor "abcd" 2 ""))

#[test]
def test_input_backspace_at_end : Bool :=
    state_is "a" 1 "" (handle_input_key Key.backspace (input_state "ab" ""))

#[test]
def test_input_backspace_on_empty_is_noop : Bool :=
    state_is "" 0 "" (handle_input_key Key.backspace (input_state "" ""))

#[test]
def test_input_left_moves_cursor : Bool :=
    state_is "ab" 1 "" (handle_input_key Key.left (at_cursor "ab" 2 ""))

#[test]
def test_input_left_clamps_at_zero : Bool :=
    state_is "ab" 0 "" (handle_input_key Key.left (at_cursor "ab" 0 ""))

#[test]
def test_input_right_clamps_at_length : Bool :=
    let st : InputState := input_state "ab" "" in
    state_is "ab" 2 "" (handle_input_key Key.right st)
    && state_is "ab" 2 "" (handle_input_key Key.right (handle_input_key Key.right st))

#[test]
def test_input_home_and_end : Bool :=
    state_is "abcd" 0 "" (handle_input_key Key.home (at_cursor "abcd" 2 ""))
    && state_is "abcd" 4 "" (handle_input_key Key.end (at_cursor "abcd" 2 ""))

#[test]
def test_input_home_and_end_on_empty_stay_zero : Bool :=
    state_is "" 0 "" (handle_input_key Key.end (input_state "" ""))
    && state_is "" 0 "" (handle_input_key Key.home (input_state "" ""))

#[test]
def test_input_ignores_keys_it_does_not_interpret : Bool :=
    let st : InputState := at_cursor "ab" 1 "ph" in
    state_is "ab" 1 "ph" (handle_input_key Key.enter st)
    && state_is "ab" 1 "ph" (handle_input_key (Key.ctrl "c") st)
    && state_is "ab" 1 "ph" (handle_input_key Key.up st)

#[test]
def test_input_key_sequence_builds_a_word : Bool :=
    let s0 : InputState := input_state "" "" in
    let s1 := handle_input_key (Key.char "h") s0 in
    let s2 := handle_input_key (Key.char "i") s1 in
    state_is "h" 1 "" (handle_input_key Key.backspace s2)

#[test]
def test_input_state_beq : Bool :=
    input_state "a" "p" == input_state "a" "p"
    && Bool.not (input_state "a" "p" == input_state "a" "q")
    && Bool.not (at_cursor "ab" 1 "p" == input_state "ab" "p")


// ==================== paste insertion ====================

#[test]
def test_insert_text_advances_by_length : Bool :=
    state_is "abc" 3 "p" (insert_text "abc" (input_state "" "p"))

#[test]
def test_insert_text_normalizes_newlines : Bool :=
    state_is "a\nb\nc" 5 "p" (insert_text "a\r\nb\rc" (input_state "" "p"))

#[test]
def test_insert_text_at_the_cursor : Bool :=
    let st1 := insert_text "bc" (at_cursor "ad" 1 "p") in
    state_is "abcd" 3 "p" st1
