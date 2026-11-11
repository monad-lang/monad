/// Span rows for the approval dialog's hunk diff (weaver.md Phase 16): a
/// dim gutter, a colored marker, the row body tinted with reverse video, and
/// a changed pair's differing middle marked again. The text renderer
/// (`DiffHunks.render_text`) serves the transcript and dumb mode; this one
/// is only for the transient dialog.
///
/// `colors` follows the rest of the palette: `NO_COLOR`/`--no-color` yields
/// plain spans (the marker's `+`/`-` still distinguishes rows).
use weaver::diff_hunks {Hunk, HunkLine, HunkKind}
use weaver::theme {LineClass, class_style}
use tui::types {TextStyle, TextSegment}
use tui::core {mk_text_segment, style_default}

def seg (text : String) (style : TextStyle) : TextSegment :=
    mk_text_segment text style

def pad (n : I64) : String :=
    let s : String := I64.to_string n in
    let l : I64 := String.length s in
    if l < 2 then String.concat "  " s
    else if l < 3 then String.concat " " s
    else s

def gutter_style (colors : Bool) : TextStyle :=
    if colors then { style_default with dim := true } else style_default

def base_style (colors : Bool) (k : HunkKind) : TextStyle :=
    if Bool.not colors
    then style_default
    else match k {
        HunkKind.hunk_add => class_style LineClass.diff_plus,
        HunkKind.hunk_remove => class_style LineClass.diff_minus,
        HunkKind.hunk_context => style_default,
    }

def row_style (colors : Bool) (k : HunkKind) : TextStyle :=
    let base : TextStyle := base_style colors k in
    if Bool.and colors (Bool.not (kind_is_context k))
    then { base with reverse := true }
    else base

def kind_is_context (k : HunkKind) : Bool :=
    match k { HunkKind.hunk_context => true, _ => false }

def marker_style (colors : Bool) (k : HunkKind) : TextStyle :=
    base_style colors k

def marker (k : HunkKind) : String :=
    match k {
        HunkKind.hunk_add => "+ ",
        HunkKind.hunk_remove => "- ",
        HunkKind.hunk_context => "  ",
    }

// ── word-level highlight inside a changed pair ──────────────────────────

#[partial]
def ascii_bytes (bs : List U8) : Bool :=
    match bs {
        List.empty => true,
        List.cons b rest => if I64.lt (U8.to_i64 b) 128 then ascii_bytes rest else false,
    }

def is_ascii (s : String) : Bool :=
    ascii_bytes (String.to_list s)

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

/// `text` as prefix / changed middle / suffix; the middle is reversed when
/// colors are on. Non-ASCII text is left whole: the byte probes above and
/// the byte slices below would otherwise split a character and render an
/// empty body.
def highlighted (colors : Bool) (text : String) (other : String) (base : TextStyle) : List TextSegment :=
    if Bool.not (Bool.and (is_ascii text) (is_ascii other))
    then [seg text base]
    else
        let n : I64 := String.length text in
        let p : I64 := common_prefix text other in
        let s : I64 := common_suffix text other (n - p) in
        let mid_len : I64 := n - p - s in
        let mid_style : TextStyle := if colors then { base with reverse := Bool.not base.reverse } else base in
        let head : List TextSegment := if p < 1 then List.empty else [seg (String.slice text 0 p) base] in
        let mid : List TextSegment := if mid_len < 1 then List.empty else [seg (String.slice text p mid_len) mid_style] in
        let tail : List TextSegment := if s < 1 then List.empty else [seg (String.slice text (p + mid_len) s) base] in
        List.append head (List.append mid tail)

// ── one line, and one hunk ──────────────────────────────────────────────

def body_spans (colors : Bool) (l : HunkLine) (other : Option String) (base : TextStyle) : List TextSegment :=
    match other {
        Option.none => [seg l.text base],
        Option.some o => highlighted colors l.text o base,
    }

def line_row (colors : Bool) (l : HunkLine) (other : Option String) : List TextSegment :=
    let gutter : TextSegment := seg (String.concat_list [pad l.old_no, " ", pad l.new_no, " | "]) (gutter_style colors) in
    let mark : TextSegment := seg (marker l.kind) (marker_style colors l.kind) in
    let body : List TextSegment := body_spans colors l other (row_style colors l.kind) in
    List.append (List.cons gutter (List.cons mark List.empty)) body

def pair_kind (a b : HunkKind) : Bool :=
    match a {
        HunkKind.hunk_remove => match b { HunkKind.hunk_add => true, _ => false },
        HunkKind.hunk_add => match b { HunkKind.hunk_remove => true, _ => false },
        HunkKind.hunk_context => false,
    }

#[partial]
def lines_rows (colors : Bool) (ls : List HunkLine) : List (List TextSegment) :=
    match ls {
        List.empty => List.empty,
        List.cons l rest => match rest {
            List.empty => [line_row colors l Option.none],
            List.cons r rrest =>
                if pair_kind l.kind r.kind
                then List.cons (line_row colors l (Option.some r.text))
                    (List.cons (line_row colors r (Option.some l.text)) (lines_rows colors rrest))
                else List.cons (line_row colors l Option.none) (lines_rows colors rest),
        },
    }

def header_row (colors : Bool) (h : Hunk) : List TextSegment :=
    let header : String := String.concat_list ["@@ -", I64.to_string h.old_start, ",", I64.to_string h.old_count,
        " +", I64.to_string h.new_start, ",", I64.to_string h.new_count, " @@"] in
    [seg header (if colors then class_style LineClass.diff_hunk else style_default)]

#[partial]
def hunk_rows (colors : Bool) (hs : List Hunk) (acc : List (List TextSegment)) : List (List TextSegment) :=
    match hs {
        List.empty => List.reverse acc,
        List.cons h rest =>
            let rows : List (List TextSegment) := List.append [header_row colors h] (lines_rows colors h.lines) in
            hunk_rows colors rest (List.append (List.reverse rows) acc),
    }

/// The dialog body's span rows, one list per rendered line.
pub def DiffRows.of_hunks (colors : Bool) (hs : List Hunk) : List (List TextSegment) :=
    hunk_rows colors hs List.empty
