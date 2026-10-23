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
