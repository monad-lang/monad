/// Tests for the selection list state machine (`motes/tui/src/widgets/
/// list.mo`).
///
/// A separate file for the same re-export reason as `input_tests.mo`
/// next to it. `list_is` compares field by field: `items` through the
/// hand-rolled `string_list_beq` path (generic `BEq (List A)` dispatch
/// is the unreliable one), which `ListState`'s own `BEq` also uses.

use lib::widgets::list {ListState, list_state, handle_list_key, ListState.beq}
use lib::types {Key}

/// All three fields of `st` at once, compared through `ListState.beq`
/// (which walks `items` with the hand-rolled `string_list_beq` -- generic
/// `BEq (List A)` dispatch is the unreliable path this mote avoids).
def list_is (items : List String) (selected : I64) (offset : I64) (st : ListState) : Bool :=
    let want : ListState := { items := items, selected := selected, offset := offset } in
    ListState.beq st want

/// The ten-item list the scroll tests walk: `"i0"` .. `"i9"`.
def ten_items : List String := ["i0", "i1", "i2", "i3", "i4", "i5", "i6", "i7", "i8", "i9"]

#[test]
def test_list_state_starts_at_top : Bool :=
    list_is ["a", "b"] 0 0 (list_state ["a", "b"])

#[test]
def test_list_down_moves_selection : Bool :=
    list_is ["a", "b", "c"] 1 0 (handle_list_key 3 Key.down (list_state ["a", "b", "c"]))

#[test]
def test_list_down_clamps_at_last : Bool :=
    let st : ListState := list_state ["a", "b"] in
    let two : ListState := handle_list_key 3 Key.down (handle_list_key 3 Key.down st) in
    let three : ListState := handle_list_key 3 Key.down two in
    list_is ["a", "b"] 1 0 three && two == three

#[test]
def test_list_up_clamps_at_first : Bool :=
    list_is ["a", "b"] 0 0 (handle_list_key 3 Key.up (list_state ["a", "b"]))

#[test]
def test_list_down_scrolls_when_selection_leaves_window : Bool :=
    // height 3: selecting item 3 scrolls the window to offset 1.
    list_is ten_items 3 1
        (handle_list_key 3 Key.down
            (handle_list_key 3 Key.down
                (handle_list_key 3 Key.down (list_state ten_items))))

#[test]
def test_list_up_scrolls_back : Bool :=
    let st0 : ListState := { (list_state ten_items) with selected := 3, offset := 1 } in
    list_is ten_items 2 1 (handle_list_key 3 Key.up st0)
    && list_is ten_items 0 0
        (handle_list_key 3 Key.up (handle_list_key 3 Key.up (handle_list_key 3 Key.up st0)))

#[test]
def test_list_page_down_moves_a_window : Bool :=
    // height 2, from (selected 0, offset 0): one page lands on item 2
    // and scrolls the window to keep it visible.
    list_is ten_items 2 1 (handle_list_key 2 Key.page_down (list_state ten_items))

#[test]
def test_list_page_up_moves_a_window_back : Bool :=
    let st : ListState := { (list_state ten_items) with selected := 4, offset := 3 } in
    list_is ten_items 2 2 (handle_list_key 2 Key.page_up st)

#[test]
def test_list_page_down_clamps_at_last : Bool :=
    // one page from the second-to-last item: the +2 jump clamps to 9,
    // and the height-2 window scrolls to offset 8 to keep it visible.
    let st : ListState := { (list_state ten_items) with selected := 8, offset := 7 } in
    list_is ten_items 9 8 (handle_list_key 2 Key.page_down st)

#[test]
def test_list_home_jumps_to_top : Bool :=
    let st : ListState := { (list_state ten_items) with selected := 7, offset := 5 } in
    list_is ten_items 0 0 (handle_list_key 3 Key.home st)

#[test]
def test_list_end_jumps_to_bottom : Bool :=
    // height 3: the last item's window starts at 10 - 3 = 7.
    list_is ten_items 9 7 (handle_list_key 3 Key.end (list_state ten_items))

#[test]
def test_list_keys_are_noop_on_empty_list : Bool :=
    list_is [] 0 0 (handle_list_key 3 Key.down (list_state []))
    && list_is [] 0 0 (handle_list_key 3 Key.page_down (list_state []))
    && list_is [] 0 0 (handle_list_key 3 Key.end (list_state []))

#[test]
def test_list_ignores_keys_it_does_not_interpret : Bool :=
    // a plain annotated literal, not `{ (list_state ["a", "b"]) with ... }`:
    // a struct-update over a base call carrying an inline list literal
    // trips the host's checker-vs-lowerer match-queue divergence
    // (`MatchTraversalMismatch`), while this shape lowers fine.
    let st : ListState := { items := ["a", "b"], selected := 1, offset := 0 } in
    list_is ["a", "b"] 1 0 (handle_list_key 3 Key.enter st)
    && list_is ["a", "b"] 1 0 (handle_list_key 3 (Key.char "x") st)

#[test]
def test_list_state_beq : Bool :=
    // plain annotated literal for the same MatchTraversalMismatch reason
    // as the ignores-keys test above.
    let shifted : ListState := { items := ["a"], selected := 1, offset := 0 } in
    list_state ["a"] == list_state ["a"]
    && Bool.not (list_state ["a"] == list_state ["b"])
    && Bool.not (shifted == list_state ["a"])
