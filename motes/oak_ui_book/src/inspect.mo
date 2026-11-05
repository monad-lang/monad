// Pure inspection of a rendered story: an indented HTML listing, an
// accessibility lint and the events it listens to.
//
// All three walk the plain `Html.Node` tree a story lowers to, so they
// check exactly what the browser receives.

use std::list {List.length, List.intercalate}
use xml_html::html {Html.Node, Html.Attr, Html.to_string}
use oak::typed {Handler.prefix}

// ═══ Attributes ═══

#[terminating]
pub def Book.attr_value (attrs : List Html.Attr) (name : String) : Option String :=
    match attrs {
        List.empty => Option.none,
        List.cons a rest =>
            match a {
                Html.Attr.attr n v => if String.beq n name then Option.some v else Book.attr_value rest name,
                Html.Attr.bool_attr n => if String.beq n name then Option.some "" else Book.attr_value rest name,
            },
    }

def has_attr (attrs : List Html.Attr) (name : String) : Bool :=
    match Book.attr_value attrs name {
        Option.some _ => true,
        Option.none => false,
    }

def attr_or (attrs : List Html.Attr) (name : String) (default : String) : String :=
    match Book.attr_value attrs name {
        Option.some v => v,
        Option.none => default,
    }

// ═══ Pretty printing ═══

def indent (depth : I64) : String := String.repeat "  " depth

/// `<tag a="…">`, escaped by the real serializer.
def open_tag (tag : String) (attrs : List Html.Attr) : String :=
    let full : String := Html.to_string (Html.Node.node_element tag attrs List.empty) in
    let close_len : I64 := I64.add (String.length tag) 3 in
    String.slice full 0 (I64.sub (String.length full) close_len)

#[terminating]
def all_text (children : List Html.Node) : Bool :=
    match children {
        List.empty => true,
        List.cons c rest =>
            match c {
                Html.Node.node_text _ => all_text rest,
                _ => false,
            },
    }

#[terminating]
def pretty_lines (depth : I64) (n : Html.Node) : List String :=
    match n {
        Html.Node.node_element tag attrs children =>
            if all_text children
            then [String.concat (indent depth) (Html.to_string n)]
            else
                List.cons (String.concat (indent depth) (open_tag tag attrs))
                    (List.append (pretty_children (depth + 1) children)
                        [String.concat_list [indent depth, "</", tag, ">"]]),
        Html.Node.node_fragment children => pretty_children depth children,
        _ => [String.concat (indent depth) (Html.to_string n)],
    }

#[terminating]
def pretty_children (depth : I64) (children : List Html.Node) : List String :=
    match children {
        List.empty => List.empty,
        List.cons c rest => List.append (pretty_lines depth c) (pretty_children depth rest),
    }

/// The tree as indented HTML, one element per line; elements holding only
/// text stay on one line.
pub def Book.pretty_html (n : Html.Node) : String := List.intercalate "\n" (pretty_lines 0 n)

// ═══ Events ═══

#[terminating]
def event_names (attrs : List Html.Attr) : List String :=
    match attrs {
        List.empty => List.empty,
        List.cons a rest =>
            match a {
                Html.Attr.attr n _ =>
                    if String.starts_with Handler.prefix n
                    then List.cons (String.drop (String.length Handler.prefix) n) (event_names rest)
                    else event_names rest,
                Html.Attr.bool_attr _ => event_names rest,
            },
    }

/// Every `<tag> event` binding in document order (from a LOWERED tree,
/// whose listeners are `data-oak-on-*` attributes).
#[terminating]
pub def Book.listeners (n : Html.Node) : List String :=
    match n {
        Html.Node.node_element tag attrs children =>
            List.append (tag_events tag (event_names attrs)) (listeners_of children),
        Html.Node.node_void tag attrs => tag_events tag (event_names attrs),
        Html.Node.node_fragment children => listeners_of children,
        _ => List.empty,
    }

#[terminating]
def listeners_of (children : List Html.Node) : List String :=
    match children {
        List.empty => List.empty,
        List.cons c rest => List.append (Book.listeners c) (listeners_of rest),
    }

#[terminating]
def tag_events (tag : String) (events : List String) : List String :=
    match events {
        List.empty => List.empty,
        List.cons e rest => List.cons (String.concat_list ["<", tag, "> ", e]) (tag_events tag rest),
    }

// ═══ Accessibility lint ═══

/// Ids defined in the tree and ids a `<label for>` points at.
#[terminating]
def collect_ids (key : String) (n : Html.Node) : List String :=
    match n {
        Html.Node.node_element tag attrs children =>
            List.append (id_list key tag attrs) (collect_ids_of key children),
        Html.Node.node_void tag attrs => id_list key tag attrs,
        Html.Node.node_raw_text tag attrs _ => id_list key tag attrs,
        Html.Node.node_fragment children => collect_ids_of key children,
        _ => List.empty,
    }

def id_list (key : String) (tag : String) (attrs : List Html.Attr) : List String :=
    if String.beq key "for" && Bool.not (String.beq tag "label")
    then List.empty
    else
        match Book.attr_value attrs key {
            Option.some v => [v],
            Option.none => List.empty,
        }

#[terminating]
def collect_ids_of (key : String) (children : List Html.Node) : List String :=
    match children {
        List.empty => List.empty,
        List.cons c rest => List.append (collect_ids key c) (collect_ids_of key rest),
    }

#[terminating]
def member (xs : List String) (x : String) : Bool :=
    match xs {
        List.empty => false,
        List.cons y rest => if String.beq x y then true else member rest x,
    }

#[terminating]
def duplicates (xs : List String) (seen : List String) (acc : List String) : List String :=
    match xs {
        List.empty => acc,
        List.cons x rest =>
            if member seen x
            then duplicates rest seen (if member acc x then acc else List.cons x acc)
            else duplicates rest (List.cons x seen) acc,
    }

/// Visible text, skipping `aria-hidden` subtrees (icon glyphs).
#[terminating]
def text_of (n : Html.Node) : String :=
    match n {
        Html.Node.node_text t => String.trim t,
        Html.Node.node_element _ attrs children =>
            if String.beq (attr_or attrs "aria-hidden" "") "true" then "" else text_of_list children,
        Html.Node.node_fragment children => text_of_list children,
        _ => "",
    }

#[terminating]
def text_of_list (children : List Html.Node) : String :=
    match children {
        List.empty => "",
        List.cons c rest => String.concat (text_of c) (text_of_list rest),
    }

def named_by_attr (attrs : List Html.Attr) : Bool :=
    has_attr attrs "aria-label" || has_attr attrs "aria-labelledby" || has_attr attrs "title"

#[terminating]
def split_ids (s : String) (i : I64) (start : I64) : List String :=
    match String.get s i {
        Option.none =>
            if I64.lt start i then [String.slice s start (I64.sub i start)] else List.empty,
        Option.some b =>
            if U8.beq b 32u8
            then
                (if I64.lt start i
                    then List.cons (String.slice s start (I64.sub i start)) (split_ids s (i + 1) (i + 1))
                    else split_ids s (i + 1) (i + 1))
            else split_ids s (i + 1) start,
    }

#[terminating]
def missing_refs (attr_name : String) (refs : List String) (ids : List String) : List String :=
    match refs {
        List.empty => List.empty,
        List.cons r rest =>
            if member ids r
            then missing_refs attr_name rest ids
            else List.cons (String.concat_list [attr_name, " points at missing id \"", r, "\""])
                (missing_refs attr_name rest ids),
    }

def ref_findings (attrs : List Html.Attr) (ids : List String) (tag : String) : List String :=
    List.append (ref_check "aria-describedby" attrs ids)
        (List.append (ref_check "aria-labelledby" attrs ids)
            (List.append (ref_check "aria-controls" attrs ids)
                (if String.beq tag "label" then ref_check "for" attrs ids else List.empty)))

def ref_check (attr_name : String) (attrs : List Html.Attr) (ids : List String) : List String :=
    match Book.attr_value attrs attr_name {
        Option.some v => missing_refs attr_name (split_ids v 0 0) ids,
        Option.none => List.empty,
    }

def is_form_control (tag : String) (attrs : List Html.Attr) : Bool :=
    let kind : String := attr_or attrs "type" "text" in
    String.beq tag "select" || String.beq tag "textarea"
        || (String.beq tag "input" && Bool.not (member ["hidden", "submit", "button", "reset", "image"] kind))

/// Findings for one element; `in_label` is true under a `<label>`.
def element_findings (tag : String) (attrs : List Html.Attr) (children : List Html.Node) (in_label : Bool)
    (ids : List String) (label_targets : List String) : List String :=
    let named : Bool := named_by_attr attrs in
    let own : List String :=
        if String.beq tag "img" && Bool.not (has_attr attrs "alt") then ["<img> has no alt text"]
        else if String.beq tag "button" && Bool.not named && String.is_empty (text_of_list children)
        then ["<button> has no accessible name (text, aria-label or title)"]
        else if String.beq tag "a" && has_attr attrs "href" && Bool.not named && String.is_empty (text_of_list children)
        then ["<a> link has no accessible name"]
        else if is_form_control tag attrs && Bool.not named && Bool.not in_label
            && Bool.not (member label_targets (attr_or attrs "id" ""))
        then [String.concat_list ["<", tag, "> has no label (a <label for>, a wrapping <label> or aria-label)"]]
        else if String.beq (attr_or attrs "role" "") "dialog" && Bool.not named
        then ["role=\"dialog\" has no aria-label or aria-labelledby"]
        else List.empty in
    List.append own (ref_findings attrs ids tag)

#[terminating]
def lint (n : Html.Node) (in_label : Bool) (ids : List String) (label_targets : List String) : List String :=
    match n {
        Html.Node.node_element tag attrs children =>
            List.append (element_findings tag attrs children in_label ids label_targets)
                (lint_all children (in_label || String.beq tag "label") ids label_targets),
        Html.Node.node_void tag attrs => element_findings tag attrs List.empty in_label ids label_targets,
        Html.Node.node_fragment children => lint_all children in_label ids label_targets,
        _ => List.empty,
    }

#[terminating]
def lint_all (children : List Html.Node) (in_label : Bool) (ids : List String) (label_targets : List String)
    : List String :=
    match children {
        List.empty => List.empty,
        List.cons c rest => List.append (lint c in_label ids label_targets) (lint_all rest in_label ids label_targets),
    }

#[terminating]
def duplicate_findings (dups : List String) : List String :=
    match dups {
        List.empty => List.empty,
        List.cons d rest => List.cons (String.concat_list ["id \"", d, "\" is used more than once"]) (duplicate_findings rest),
    }

/// Accessibility problems a static tree can show: unlabelled controls,
/// nameless buttons and links, images without alt text, unlabelled
/// dialogs, ARIA/`for` references to missing ids, and duplicate ids.
pub def Book.a11y_lint (n : Html.Node) : List String :=
    let ids : List String := collect_ids "id" n in
    let label_targets : List String := collect_ids "for" n in
    List.append (lint n false ids label_targets) (duplicate_findings (duplicates ids List.empty List.empty))
