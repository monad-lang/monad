/// Pure diff tests for `Patch.diff`. The apply half is DOM-bound and is
/// covered end to end by `wasm/web/spa_smoke.mjs`.
use std::list {List.length}
use xml_html::html {Html.Attr, Html.Node}
use lib::patch {Patch}

def text (s : String) : Html.Node := Html.Node.node_text s

def element (tag : String) (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
    Html.Node.node_element tag attrs children

def first_patch (patches : List Patch) : Option Patch :=
    match patches {
        List.empty => Option.none,
        List.cons p _ => Option.some p,
    }

/// Element-wise path equality: generic `BEq` on lists is unreliable.
def same_path (a : List I64) (b : List I64) : Bool := match a {
    List.empty => match b {
        List.empty => true,
        List.cons _ _ => false,
    },
    List.cons x xs => match b {
        List.empty => false,
        List.cons y ys => I64.beq x y && same_path xs ys,
    },
}

#[test]
def test_identical_trees_produce_no_patches : Bool :=
    let n := element "div" [Html.Attr.attr "id" "a"] [text "x"] in
    List.is_empty (Patch.diff n n)

#[test]
def test_text_change_is_a_set_text_at_the_child_path : Bool :=
    let old := element "div" List.empty [text "a"] in
    let new := element "div" List.empty [text "b"] in
    match first_patch (Patch.diff old new) {
        Option.none => false,
        Option.some p => match p {
            Patch.set_text path content =>
                if Bool.not (String.beq content "b") then false
                else List.length (Patch.diff old new) == 1,
            _ => false,
        },
    }

#[test]
def test_attribute_add_is_a_set_attr_on_the_root : Bool :=
    let old := element "div" List.empty [text "x"] in
    let new := element "div" [Html.Attr.attr "id" "a"] [text "x"] in
    match first_patch (Patch.diff old new) {
        Option.none => false,
        Option.some p => match p {
            Patch.set_attr path name value =>
                if String.beq name "id" then String.beq value "a" else false,
            _ => false,
        },
    }

#[test]
def test_attribute_remove_is_a_remove_attr : Bool :=
    let old := element "div" [Html.Attr.attr "id" "a"] [text "x"] in
    let new := element "div" List.empty [text "x"] in
    match first_patch (Patch.diff old new) {
        Option.none => false,
        Option.some p => match p {
            Patch.remove_attr _path name => String.beq name "id",
            _ => false,
        },
    }

#[test]
def test_bool_attr_set_uses_an_empty_value : Bool :=
    let old := element "input" List.empty List.empty in
    let new := element "input" [Html.Attr.bool_attr "disabled"] List.empty in
    match first_patch (Patch.diff old new) {
        Option.none => false,
        Option.some p => match p {
            Patch.set_attr _path name value =>
                if String.beq name "disabled" then String.is_empty value else false,
            _ => false,
        },
    }

#[test]
def test_tag_change_replaces_the_whole_node : Bool :=
    let old := element "div" List.empty [text "x"] in
    let new := element "span" List.empty [text "x"] in
    match first_patch (Patch.diff old new) {
        Option.none => false,
        Option.some p => match p {
            Patch.replace path _node => List.length path == 1,
            _ => false,
        },
    }

#[test]
def test_child_count_change_replaces_the_parent : Bool :=
    let old := element "div" List.empty [text "x"] in
    let new := element "div" List.empty [text "x", text "y"] in
    match first_patch (Patch.diff old new) {
        Option.none => false,
        Option.some p => match p {
            Patch.replace _path _node => true,
            _ => false,
        },
    }

#[test]
def test_nested_element_diffs_use_the_child_path : Bool :=
    let old := element "div" List.empty [element "span" List.empty [text "a"]] in
    let new := element "div" List.empty [element "span" List.empty [text "b"]] in
    match first_patch (Patch.diff old new) {
        Option.none => false,
        Option.some p => match p {
            Patch.set_text path _content => List.length path == 3,
            _ => false,
        },
    }

// ─── drop_last: the parent path of a replace ────────────────
//
// Regression for `2026-10-25-oak-wasm-patch-drop-last-corrupts-nested-paths`:
// the old two-at-a-time walk was only correct for paths of length <= 2.

#[test]
def test_drop_last_empty : Bool := List.is_empty (Patch.drop_last List.empty)

#[test]
def test_drop_last_one : Bool := List.is_empty (Patch.drop_last [0i64])

#[test]
def test_drop_last_two : Bool := same_path (Patch.drop_last [0i64, 2i64]) [0i64]

#[test]
def test_drop_last_three : Bool :=
    same_path (Patch.drop_last [0i64, 1i64, 1i64]) [0i64, 1i64]

#[test]
def test_drop_last_four : Bool :=
    same_path (Patch.drop_last [0i64, 1i64, 2i64, 3i64]) [0i64, 1i64, 2i64]

#[test]
def test_drop_last_five : Bool :=
    same_path
        (Patch.drop_last [5i64, 4i64, 3i64, 2i64, 1i64])
        [5i64, 4i64, 3i64, 2i64]

/// The nested child-count change the e2e fixture exercises: the `ul` sits at
/// [0, 0, 1] (container -> root div -> section -> ul), so the apply half
/// must resolve [0, 0] as its parent.
#[test]
def test_nested_child_count_change_patches_at_depth_three : Bool :=
    let old := element "div" List.empty
        [ element "section" List.empty
            [element "p" List.empty [text "x"], element "ul" List.empty List.empty] ] in
    let new := element "div" List.empty
        [ element "section" List.empty
            [element "p" List.empty [text "x"], element "ul" List.empty [text "a", text "b"]] ] in
    match first_patch (Patch.diff old new) {
        Option.none => false,
        Option.some p => match p {
            Patch.replace path _node => same_path path [0i64, 0i64, 1i64],
            _ => false,
        },
    }

// ─── Keyed children ─────────────────────────────────────────

def keyed (k : String) (label : String) : Html.Node :=
    element "li" [Html.Attr.attr "data-oak-key" k] [text label]

def list_node (children : List Html.Node) : Html.Node :=
    element "ul" List.empty children

def patch_is_move (p : Patch) (from : List I64) (to : List I64) : Bool := match p {
    Patch.move f t => same_path f from && same_path t to,
    _ => false,
}

def patch_is_insert (p : Patch) (path : List I64) : Bool := match p {
    Patch.insert at _node => same_path at path,
    _ => false,
}

def patch_is_remove (p : Patch) (path : List I64) : Bool := match p {
    Patch.remove at => same_path at path,
    _ => false,
}

def patch_is_replace (p : Patch) (path : List I64) : Bool := match p {
    Patch.replace at _node => same_path at path,
    _ => false,
}

def patch_is_structural (p : Patch) : Bool := match p {
    Patch.insert _ _ => true,
    Patch.remove _ => true,
    Patch.move _ _ => true,
    _ => false,
}

#[terminating]
def no_structural (patches : List Patch) : Bool := match patches {
    List.empty => true,
    List.cons p rest => Bool.not (patch_is_structural p) && no_structural rest,
}

#[test]
def test_keyed_reorder_is_one_move : Bool :=
    let a := keyed "a" "A" in
    let b := keyed "b" "B" in
    let c := keyed "c" "C" in
    match Patch.diff (list_node [a, b, c]) (list_node [c, a, b]) {
        List.cons p rest =>
            patch_is_move p [0i64, 2i64] [0i64, 0i64] && List.is_empty rest,
        List.empty => false,
    }

#[test]
def test_keyed_remove_does_not_move_survivors : Bool :=
    let a := keyed "a" "A" in
    let b := keyed "b" "B" in
    match Patch.diff (list_node [a, b]) (list_node [b]) {
        List.cons p rest => patch_is_remove p [0i64, 0i64] && List.is_empty rest,
        List.empty => false,
    }

#[test]
def test_keyed_insert_at_end : Bool :=
    let a := keyed "a" "A" in
    let b := keyed "b" "B" in
    match Patch.diff (list_node [a]) (list_node [a, b]) {
        List.cons p rest => patch_is_insert p [0i64, 1i64] && List.is_empty rest,
        List.empty => false,
    }

#[test]
def test_keyed_removals_are_descending : Bool :=
    let a := keyed "a" "A" in
    let b := keyed "b" "B" in
    let c := keyed "c" "C" in
    let d := keyed "d" "D" in
    match Patch.diff (list_node [a, b, c, d]) (list_node [a, d]) {
        List.cons p1 rest1 => match rest1 {
            List.cons p2 rest2 =>
                patch_is_remove p1 [0i64, 2i64]
                    && patch_is_remove p2 [0i64, 1i64]
                    && List.is_empty rest2,
            List.empty => false,
        },
        List.empty => false,
    }

#[test]
def test_keyed_key_change_is_remove_then_insert : Bool :=
    let a := keyed "a" "A" in
    let z := keyed "z" "Z" in
    match Patch.diff (list_node [a]) (list_node [z]) {
        List.cons p1 rest1 => match rest1 {
            List.cons p2 rest2 =>
                patch_is_remove p1 [0i64, 0i64]
                    && patch_is_insert p2 [0i64, 0i64]
                    && List.is_empty rest2,
            List.empty => false,
        },
        List.empty => false,
    }

#[test]
def test_keyed_matched_tag_change_replaces_the_child : Bool :=
    let a := keyed "a" "A" in
    let b := element "div" [Html.Attr.attr "data-oak-key" "a"] [text "A"] in
    match Patch.diff (list_node [a]) (list_node [b]) {
        List.cons p rest => patch_is_replace p [0i64, 0i64] && List.is_empty rest,
        List.empty => false,
    }

#[test]
def test_keyed_to_empty_removes_in_descending_order : Bool :=
    let a := keyed "a" "A" in
    let b := keyed "b" "B" in
    match Patch.diff (list_node [a, b]) (list_node List.empty) {
        List.cons p1 rest1 => match rest1 {
            List.cons p2 rest2 =>
                patch_is_remove p1 [0i64, 1i64]
                    && patch_is_remove p2 [0i64, 0i64]
                    && List.is_empty rest2,
            List.empty => false,
        },
        List.empty => false,
    }

#[test]
def test_duplicate_keys_fall_back_to_positional : Bool :=
    let a1 := keyed "a" "A" in
    let a2 := keyed "a" "B" in
    let a3 := keyed "a" "C" in
    let a4 := keyed "a" "D" in
    no_structural (Patch.diff (list_node [a1, a2]) (list_node [a3, a4]))

#[test]
def test_unkeyed_list_stays_positional : Bool :=
    no_structural (Patch.diff (list_node [text "a", text "b"]) (list_node [text "a", text "c"]))

