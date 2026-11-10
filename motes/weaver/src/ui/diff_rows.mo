/// Span rows for the approval dialog's hunk diff (weaver.md Phase 16): a
/// dim gutter, a colored marker, the row body tinted with reverse video, and
/// a changed pair's differing middle marked again. The text renderer
/// (`DiffHunks.render_text`) serves the transcript and dumb mode; this one
/// is only for the transient dialog.
use weaver::diff_hunks {Hunk, HunkLine, HunkKind}
use weaver::theme {LineClass, class_style}
use tui::types {TextStyle, TextSegment}
use tui::core {mk_text_segment, style_default}
use std::ansi {Color}

def seg (text : String) (style : TextStyle) : TextSegment :=
    mk_text_segment text style

def pad (n : I64) : String :=
    let s : String := I64.to_string n in
    let l : I64 := String.length s in
    if l < 2 then String.concat "  " s
    else if l < 3 then String.concat " " s
    else s

def gutter_style : TextStyle :=
    { style_default with dim := true }

def add_style : TextStyle :=
    let base : TextStyle := class_style LineClass.diff_plus in
    { base with reverse := true }

def remove_style : TextStyle :=
    let base : TextStyle := class_style LineClass.diff_minus in
    { base with reverse := true }

def context_style : TextStyle :=
    style_default

def marker_style (k : HunkKind) : TextStyle :=
    match k {
        HunkKind.hunk_add => class_style LineClass.diff_plus,
        HunkKind.hunk_remove => class_style LineClass.diff_minus,
        HunkKind.hunk_context => style_default,
    }

def marker (k : HunkKind) : String :=
    match k {
        HunkKind.hunk_add => "+ ",
        HunkKind.hunk_remove => "- ",
        HunkKind.hunk_context => "  ",
    }

def row_style (k : HunkKind) : TextStyle :=
    match k {
        HunkKind.hunk_add => add_style,
        HunkKind.hunk_remove => remove_style,
        HunkKind.hunk_context => context_style,
    }

// ── word-level highlight inside a changed pair ──────────────────────────

#[partial]
def prefix_at (a b : String) (i n : I64) : I64 :=
    if i > n - 1 then i
    else if String.slice a i 1 == String.slice b i 1 then prefix_at a b (i + 1) n
    else i

def common_prefix (a b : String) : I64 :=
    let n : I64 := if I64.lt (String.length a) (String.length b) then String.length a else String.length b in
    prefix_at a b 0 n

#[partial]
def suffix_at (a b : String) (i limit : I64) : I64 :=
    if i > limit then i
    else if String.slice a (String.length a - i) 1 == String.slice b (String.length b - i) 1
    then suffix_at a b (i + 1) limit
    else i

def common_suffix (a b : String) (budget : I64) : I64 :=
    let la : I64 := String.length a in
    let lb : I64 := String.length b in
    let limit : I64 := if I64.lt la lb then la else lb in
    let limit2 : I64 := if I64.lt budget limit then budget else limit in
    if I64.lt limit2 1 then 0 else suffix_at a b 1 limit2 - 1

/// `text` as prefix / changed middle / suffix; the middle is reversed.
def highlighted (text : String) (other : String) (base : TextStyle) : List TextSegment :=
    let n : I64 := String.length text in
    let p : I64 := common_prefix text other in
    let s : I64 := common_suffix text other (n - p) in
    let mid_len : I64 := n - p - s in
    let mid_style : TextStyle := { base with reverse := Bool.not base.reverse } in
    let head : List TextSegment := if p < 1 then List.empty else [seg (String.slice text 0 p) base] in
    let mid : List TextSegment := if mid_len < 1 then List.empty else [seg (String.slice text p mid_len) mid_style] in
    let tail : List TextSegment := if s < 1 then List.empty else [seg (String.slice text (p + mid_len) s) base] in
    List.append head (List.append mid tail)

// ── one line, and one hunk ──────────────────────────────────────────────

def body_spans (l : HunkLine) (other : Option String) (base : TextStyle) : List TextSegment :=
    match other {
        Option.none => [seg l.text base],
        Option.some o => highlighted l.text o base,
    }

def line_row (l : HunkLine) (other : Option String) : List TextSegment :=
    let gutter : TextSegment := seg (String.concat_list [pad l.old_no, " ", pad l.new_no, " | "]) gutter_style in
    let mark : TextSegment := seg (marker l.kind) (marker_style l.kind) in
    let body : List TextSegment := body_spans l other (row_style l.kind) in
    List.append (List.cons gutter (List.cons mark List.empty)) body

def pair_kind (a b : HunkKind) : Bool :=
    match a {
        HunkKind.hunk_remove => match b { HunkKind.hunk_add => true, _ => false },
        HunkKind.hunk_add => match b { HunkKind.hunk_remove => true, _ => false },
        HunkKind.hunk_context => false,
    }

#[partial]
def lines_rows (ls : List HunkLine) : List (List TextSegment) :=
    match ls {
        List.empty => List.empty,
        List.cons l rest => match rest {
            List.empty => [line_row l Option.none],
            List.cons r rrest =>
                if pair_kind l.kind r.kind
                then List.cons (line_row l (Option.some r.text))
                    (List.cons (line_row r (Option.some l.text)) (lines_rows rrest))
                else List.cons (line_row l Option.none) (lines_rows rest),
        },
    }

def header_row (h : Hunk) : List TextSegment :=
    let header : String := String.concat_list ["@@ -", I64.to_string h.old_start, ",", I64.to_string h.old_count,
        " +", I64.to_string h.new_start, ",", I64.to_string h.new_count, " @@"] in
    [seg header (class_style LineClass.diff_hunk)]

#[partial]
def hunk_rows (hs : List Hunk) (acc : List (List TextSegment)) : List (List TextSegment) :=
    match hs {
        List.empty => List.reverse acc,
        List.cons h rest =>
            let rows : List (List TextSegment) := List.append [header_row h] (lines_rows h.lines) in
            hunk_rows rest (List.append (List.reverse rows) acc),
    }

/// The dialog body's span rows, one list per rendered line.
pub def DiffRows.of_hunks (hs : List Hunk) : List (List TextSegment) :=
    hunk_rows hs List.empty
