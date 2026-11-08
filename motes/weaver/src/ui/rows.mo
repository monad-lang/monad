/// Display rows: a transcript line (or any text) wrapped to a width and
/// styled, plus the widgets that paint one row with or without a selected
/// cell span. Every panel that shows wrapped text -- the transcript, the
/// live stream, dialog bodies -- builds its rows here.
use weaver::theme {
    theme_tline_style_with, theme_thinking_style_with, theme_markdown_span_style_with,
    theme_split_lines,
}
use markdown::parse {Markdown.parse}
use markdown::render {Markdown.to_lines, Markdown.to_plain_lines, Markdown.StyledLine, Markdown.StyledSpan}
use weaver::store {TLine, TLineKind}
use tui::types {LayoutSize, TextStyle, TextSegment}
use tui::core {style_default, mk_text_segment}
use tui::widget {Widget, SizedWidget, label, spans, sized, with_style}
use tui::render {wrap_text}
use tui::text {Text.width, Text.slice_cols, Text.padded_slice_cols, Text.width_spans, Text.wrap_spans, Text.slice_spans}

/// One display row: wrapped text plus the style of its ORIGINAL logical
/// line (a continuation row must not be reclassified by a prefix it
/// happens to start with).
pub struct DisplayRow {
    text : String,
    style : TextStyle,
    /// Empty for an ordinary row (painted as one label); a Markdown row
    /// carries its inline segments so bold/code/link styling survives
    /// wrapping and selection.
    spans : List TextSegment,
}

pub def Rows.plain (style : TextStyle) (text : String) : DisplayRow :=
    let r : DisplayRow := { text := text, style := style, spans := List.empty } in
    r

pub def Rows.of_spans (style : TextStyle) (ss : List TextSegment) : DisplayRow :=
    let text : String := String.concat_all (List.map (fn (s : TextSegment) => s.text) ss) in
    let r : DisplayRow := { text := text, style := style, spans := ss } in
    r

#[partial]
pub def Rows.length (rs : List DisplayRow) : I64 :=
    match rs {
        List.empty => 0,
        List.cons _ rest => 1 + Rows.length rest,
    }

#[partial]
pub def Rows.drop (n : I64) (rs : List DisplayRow) : List DisplayRow :=
    if n < 1 then rs
    else match rs {
        List.empty => rs,
        List.cons _ rest => Rows.drop (n - 1) rest,
    }

/// The first `n` rows.
#[partial]
pub def Rows.take (n : I64) (rs : List DisplayRow) : List DisplayRow :=
    if n < 1 then List.empty
    else match rs {
        List.empty => List.empty,
        List.cons r rest => List.cons r (Rows.take (n - 1) rest),
    }

/// The last `n` rows.
pub def Rows.take_last (n : I64) (rs : List DisplayRow) : List DisplayRow :=
    if n < 1 then List.empty
    else
        let cut : I64 := Rows.length rs - n in
        Rows.drop (if cut < 0 then 0 else cut) rs

#[partial]
pub def Rows.at (rs : List DisplayRow) (i : I64) : Option DisplayRow :=
    match rs {
        List.empty => Option.none,
        List.cons r rest => if i < 1 then Option.some r else Rows.at rest (i - 1),
    }

/// The display bound for one logical line. The stored transcript keeps the
/// full text; only rendering truncates, so one enormous assistant message
/// cannot make every repaint (and every row-count walk) arbitrarily large.
/// The dialog preview has its own, stricter cap.
pub def Rows.cap_bytes : I64 := 262144

/// A block larger than this renders as plain text: the parser's work on one
/// huge paragraph is quadratic, and a 28 KB plan/paste is not worth a
/// multi-second repaint. Normal messages still get Markdown.
pub def Rows.markdown_max_bytes : I64 := 16384

/// A UTF-8-safe prefix: `String.slice` answers "" when its end offset is a
/// continuation byte, so back off up to three bytes rather than render a
/// blank line.
#[partial]
def cap_utf8 (s : String) (max : I64) (back : I64) : String :=
    if I64.gt back 3 then ""
    else if I64.lt (max - back) 1 then ""
    else
        let x : String := String.slice s 0 (max - back) in
        if String.is_empty x then cap_utf8 s max (back + 1) else x

/// A tail slice that never starts mid-UTF-8, for the same reason.
#[partial]
def tail_safe (text : String) (start : I64) (back : I64) : String :=
    let n : I64 := String.length text in
    if I64.gt back 3 then ""
    else if I64.lt (n - start - back) 1 then ""
    else
        let s : String := String.slice text (start + back) (n - start - back) in
        if String.is_empty s then tail_safe text start (back + 1) else s

/// At most the last `cap` bytes of `text`, cut on a character boundary.
pub def Rows.tail_bytes (text : String) (cap : I64) : String :=
    let n : I64 := String.length text in
    if I64.gt n cap then tail_safe text (n - cap) 0 else text

/// `text` split on its newlines and wrapped, every row in `style`. An
/// empty text is one empty row.
#[partial]
pub def Rows.wrap (style : TextStyle) (width : I64) (text : String) : List DisplayRow :=
    let w : I64 := if width < 1 then 1 else width in
    if String.is_empty text
    then List.singleton (Rows.plain style "")
    else
        List.flatten (List.map (fn (part : String) =>
            List.map (fn (t : String) => Rows.plain style t) (wrap_text w part)) (theme_split_lines text))

#[partial]
def plain_line_list (width : I64) (lines : List String) : List DisplayRow :=
    match lines {
        List.empty => List.empty,
        List.cons l rest => List.append (Rows.wrap style_default width l) (plain_line_list width rest),
    }

def md_span (colors : Bool) (s : Markdown.StyledSpan) : TextSegment :=
    mk_text_segment s.text (theme_markdown_span_style_with colors s.style)

#[partial]
def md_rows_go (colors : Bool) (width : I64) (lines : List Markdown.StyledLine) : List DisplayRow :=
    match lines {
        List.empty => List.empty,
        List.cons l rest =>
            let ss : List TextSegment := List.map (md_span colors) l.spans in
            let wrapped : List (List TextSegment) := Text.wrap_spans width ss in
            let rows : List DisplayRow := List.map (fn (row : List TextSegment) => Rows.of_spans style_default row) wrapped in
            List.append rows (md_rows_go colors width rest),
    }

/// A Markdown block: parsed once, wrapped with span-aware wrapping. With
/// colors off the same AST flattens to plain lines, so a `--no-color` run
/// shows the same text without the styling.
pub def Rows.markdown (colors : Bool) (width : I64) (text : String) : List DisplayRow :=
    if I64.gt (String.length text) Rows.markdown_max_bytes
    then plain_line_list width (theme_split_lines text)
    else Rows.markdown_full colors width text

/// `Rows.markdown` with no size fallback, for a document rendered once
/// and kept (a dialog body), not a transcript block re-rendered per frame.
pub def Rows.markdown_full (colors : Bool) (width : I64) (text : String) : List DisplayRow :=
    let doc := Markdown.parse text in
    if colors
    then md_rows_go colors width (Markdown.to_lines doc)
    else plain_line_list width (Markdown.to_plain_lines doc)

/// One transcript line, split on its own newlines and wrapped. The kind
/// wins over the text: a Markdown block is rendered as Markdown, a
/// thinking row keeps the thinking style, and a plain row falls back to
/// the prefix classification (user wins first).
pub def Rows.of_line (colors : Bool) (width : I64) (line : TLine) : List DisplayRow :=
    let style : TextStyle :=
        match line.kind {
            TLineKind.line_thinking => theme_thinking_style_with colors,
            TLineKind.line_markdown => style_default,
            _ => theme_tline_style_with colors line.user line.text,
        } in
    let n : I64 := String.length line.text in
    let truncated : Bool := I64.lt Rows.cap_bytes n in
    let text : String := if truncated then cap_utf8 line.text Rows.cap_bytes 0 else line.text in
    let rows : List DisplayRow :=
        match line.kind {
            TLineKind.line_markdown => Rows.markdown colors width text,
            _ => Rows.wrap style width text,
        } in
    if truncated
    then List.append rows [Rows.plain style "[truncated for display -- full text is in the session history]"]
    else rows

pub def Rows.count_line (colors : Bool) (width : I64) (line : TLine) : I64 :=
    Rows.length (Rows.of_line colors width line)

#[partial]
pub def Rows.count_lines (colors : Bool) (width : I64) (lines : List TLine) : I64 :=
    match lines {
        List.empty => 0,
        List.cons l rest => Rows.count_line colors width l + Rows.count_lines colors width rest,
    }

/// One row as a one-cell-high widget.
pub def Rows.widget (r : DisplayRow) : SizedWidget :=
    let base : Widget :=
        match r.spans {
            List.empty => label r.text,
            List.cons _ _ => spans r.spans,
        } in
    sized (LayoutSize.fixed 1) (with_style r.style base)

def part (w : I64) (style : TextStyle) (body : Widget) : List SizedWidget :=
    if w < 1 then List.empty
    else List.singleton (sized (LayoutSize.fixed w) (with_style style body))

def joined (r : DisplayRow) (parts : List SizedWidget) : SizedWidget :=
    match parts {
        List.empty => Rows.widget r,
        List.cons _ _ => sized (LayoutSize.fixed 1) (Widget.row parts),
    }

/// A span-row selection: head/mid/tail spans, the middle reversed in place.
def selected_span_row (r : DisplayRow) (a : I64) (b : I64) : SizedWidget :=
    let total : I64 := Text.width r.text in
    let mw : I64 := if b < a then 0 else b - a in
    let head : List TextSegment := Text.slice_spans r.spans 0 a in
    let mid0 : List TextSegment := Text.slice_spans r.spans a b in
    let tail : List TextSegment := Text.slice_spans r.spans b total in
    let midw : I64 := Text.width_spans mid0 in
    let pad : I64 := if mw < midw then 0 else mw - midw in
    let mid : List TextSegment :=
        List.append (List.map (fn (s : TextSegment) => mk_text_segment s.text { s.style with reverse := true }) mid0)
            (if pad < 1 then List.empty else [mk_text_segment (String.repeat " " pad) { r.style with reverse := true }]) in
    joined r (List.append (part (Text.width_spans head) r.style (spans head))
        (List.append (part mw r.style (spans mid)) (part (Text.width_spans tail) r.style (spans tail))))

/// A plain-row selection stays text-based so it keeps its exact padding.
def selected_plain_row (r : DisplayRow) (a : I64) (b : I64) : SizedWidget :=
    let total : I64 := Text.width r.text in
    let head : String := Text.slice_cols r.text 0 a in
    let mid : String := Text.padded_slice_cols r.text a b in
    let tail : String := Text.slice_cols r.text b total in
    let mw : I64 := if b < a then 0 else b - a in
    let sel : TextStyle := { r.style with reverse := true } in
    joined r (List.append (part (Text.width head) r.style (label head))
        (List.append (part mw sel (label mid)) (part (Text.width tail) r.style (label tail))))

/// One row split into head / selected middle / tail, so the selection is
/// reverse video on exactly the half-open cell span `cols`. Fixed widths
/// come from `Text.width`, never from byte length.
pub def Rows.widget_selected (r : DisplayRow) (cols : Option (Pair I64 I64)) : SizedWidget :=
    match cols {
        Option.none => Rows.widget r,
        Option.some pr => match pr {
            Pair.pair a b => match r.spans {
                List.cons _ _ => selected_span_row r a b,
                List.empty => selected_plain_row r a b,
            },
        },
    }
