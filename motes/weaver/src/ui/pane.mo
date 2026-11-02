/// The transcript pane: the loaded window into the session's transcript,
/// its wrapped-rows cache, the scroll position (in display rows above the
/// pinned bottom), the mouse selection, the scrollbar and its drag, and
/// the "load older pages" intent. A component -- `PaneModel`, `PaneMsg`,
/// `Pane.update`, `Pane.view` -- over a `PaneView` geometry the parent
/// computes (the pane does not know about the banner, the live rows or
/// the input box; they only change its height).
///
/// Page reads are the parent's IO: `Pane.page_wanted` names the range,
/// `Pane.page_requested` marks it in flight, `Pane.page_loaded` /
/// `Pane.page_failed` fold the answer.
use weaver::theme {theme_line_style_with, theme_border_style_with, theme_scrollbar_thumb_style_with}
use weaver::store {
    TLine, Transcript, TranscriptPage, Store.page_lines,
    Transcript.next_block, Transcript.append, Transcript.slice,
    Transcript.with_page, Transcript.drop_page,
}
use tui::types {LayoutSize, TextStyle}
use tui::core {clamp}
use tui::widget {Widget, SizedWidget, label, sized, with_style}
use tui::text {Text.slice_cols, Text.snap_span}
use std::list {List.intercalate}
use weaver::ui::rows {
    DisplayRow, Rows.plain, Rows.of_line, Rows.count_line, Rows.count_lines,
    Rows.length, Rows.drop, Rows.take, Rows.at, Rows.widget_selected,
}

/// Where the pane sits and what it may use. `top`/`left` are the content's
/// first screen row/column; the scrollbar is the cell right of the content
/// (`left + width`) and exists only when `bar` is set.
pub struct PaneView {
    colors : Bool,
    width : I64,
    height : I64,
    top : I64,
    left : I64,
    bar : Bool,
}

/// What the cached rows were computed for; any change rebuilds them.
pub struct PaneKey {
    total : I64,
    tail_start : I64,
    page_start : I64,
    width : I64,
    height : I64,
    colors : Bool,
    scroll : I64,
    details : Bool,
}

pub struct TextSelection {
    anchor_row : I64,
    anchor_col : I64,
    focus_row : I64,
    focus_col : I64,
    moved : Bool
}

pub struct PaneModel {
    /// The last `Store.tail_lines` lines plus at most one older page.
    transcript : Transcript,
    /// WRAPPED DISPLAY ROWS above the pinned bottom; 0 = pinned to the
    /// latest output. A row unit (not a logical line) is what makes every
    /// row of a message taller than the panel reachable.
    scroll : I64 := 0,
    /// The loaded window's wrapped row count; `scroll` clamps against it.
    row_total : I64 := 0,
    /// Where the pointer grabbed the scrollbar thumb (rows below its top);
    /// none when no bar drag is in progress. Kept out of `sel` so a bar
    /// drag never becomes a text selection.
    bar_grab : Option I64 := Option.none,
    /// A page read is in flight.
    page_pending : Bool := false,
    /// The rows last painted, and the state they were computed for.
    /// Wrapping a long line every tick was the TUI's allocation hot spot.
    rows : List DisplayRow := List.empty,
    key : Option PaneKey := Option.none,
    /// The mouse selection over DISPLAY rows (cleared whenever the rows
    /// rebuild: scroll, append, page load, resize).
    sel : Option TextSelection := Option.none,
    /// Ctrl+O: show detail lines (tool output, completed thinking).
    details : Bool := false,
    /// The user is scrolling UP: prefetch older pages even when the
    /// clamped scroll cannot move any further. Cleared by a down scroll.
    want_older : Bool := false,
    /// Home: keep loading pages and stay pinned to the loaded top until
    /// the transcript's first line is loaded.
    want_top : Bool := false,
}

pub type PaneMsg {
    /// Rows toward older output (negative: toward the latest).
    scroll (delta : I64),
    /// Home: the loaded top, then older pages until the first line.
    top,
    /// End: back to the live tail, releasing the loaded page.
    repin,
    /// Left-button mouse reports at screen cells.
    press (row : I64) (col : I64),
    drag (row : I64) (col : I64),
    release (row : I64) (col : I64),
    toggle_details,
    clear_selection,
}

pub def Pane.make (tr : Transcript) : PaneModel :=
    let p : PaneModel := { transcript := tr, scroll := 0, row_total := 0, bar_grab := Option.none, page_pending := false,
                           rows := List.empty, key := Option.none, sel := Option.none, details := false,
                           want_older := false, want_top := false } in
    p

/// A session switch: the new transcript, pinned, with no paging intent.
pub def Pane.reset (p : PaneModel) (tr : Transcript) : PaneModel :=
    { p with transcript := tr, scroll := 0, bar_grab := Option.none, page_pending := false, key := Option.none,
        want_older := false, want_top := false }

/// One message; the copied text of a finished selection rides along (a
/// pure update cannot write the clipboard).
pub def Pane.update (v : PaneView) (p : PaneModel) (msg : PaneMsg) : Pair PaneModel (Option String) :=
    match msg {
        PaneMsg.scroll delta => Pair.pair (scroll_by v p delta) Option.none,
        PaneMsg.top => Pair.pair (Pane.refresh v { p with want_top := true, want_older := true, scroll := 999999 }) Option.none,
        PaneMsg.repin =>
            let tr : Transcript := Transcript.drop_page p.transcript in
            Pair.pair (Pane.refresh v { p with transcript := tr, scroll := 0, want_older := false, want_top := false, key := Option.none }) Option.none,
        PaneMsg.press r c =>
            if Pane.bar_hit v p r c then Pair.pair (bar_press v p r) Option.none
            else Pair.pair (begin_selection v p r c) Option.none,
        PaneMsg.drag r c => match p.bar_grab {
            Option.some grab => Pair.pair (Pane.scroll_to v p (bar_scroll_for v p r grab)) Option.none,
            Option.none => Pair.pair (drag_selection v p r c) Option.none,
        },
        PaneMsg.release r c => match p.bar_grab {
            Option.some _ => Pair.pair { p with bar_grab := Option.none } Option.none,
            Option.none =>
                let dragged : PaneModel := drag_selection v p r c in
                Pair.pair { dragged with sel := Option.none } (Pane.selection_text v dragged),
        },
        PaneMsg.toggle_details => Pair.pair (Pane.refresh v { p with details := Bool.not p.details }) Option.none,
        PaneMsg.clear_selection => Pair.pair { p with sel := Option.none } Option.none,
    }

/// A resize or a turn end abandons an in-progress bar drag.
pub def Pane.end_drag (p : PaneModel) : PaneModel :=
    { p with bar_grab := Option.none }

/// Scrolling UP sets `want_older`, which keeps prefetching even when the
/// clamped scroll can no longer move; any down scroll drops it (and a
/// pending Home). The clamp runs in `refresh` against the FRESHLY counted
/// rows -- the cached `row_total` can lag a transcript/page swap.
def scroll_by (v : PaneView) (p : PaneModel) (delta : I64) : PaneModel :=
    let p1 : PaneModel :=
        if delta > 0 then { p with want_older := true }
        else if delta < 0 then { p with want_older := false, want_top := false }
        else p in
    Pane.refresh v { p1 with scroll := p1.scroll + delta }

pub def Pane.scroll_to (v : PaneView) (p : PaneModel) (target : I64) : PaneModel :=
    Pane.refresh v { p with scroll := scroll_clamp target p.row_total v.height }

/// A new block of transcript lines: the blank separator row in front
/// (skipped on an empty transcript), and a scrolled view HELD in place --
/// the scroll grows by the block's WRAPPED ROW count, so the visible rows
/// do not slide. A pinned view (scroll 0) keeps riding the tail.
#[partial]
pub def Pane.append_block (v : PaneView) (p : PaneModel) (lines : List TLine) : PaneModel :=
    let block : List TLine := Transcript.next_block p.transcript lines in
    let tr2 : Transcript := Transcript.append p.transcript block in
    // Only a SCROLLED view needs the block's row count: for one huge
    // message the extra wrap was a visible freeze. Lines the tail cap
    // drops were above the bottom-anchored window, so they never move it.
    let p2 : PaneModel :=
        if p.scroll > 0
        then
            let shown : List TLine := shown_lines p.details block in
            let added : I64 := Rows.count_lines v.colors v.width shown in
            { p with transcript := tr2, scroll := p.scroll + added }
        else { p with transcript := tr2, scroll := 0 } in
    Pane.refresh v p2

/// A gapless append (the Ctrl+C hint): no separator row, and no scroll
/// adjustment -- the line joins the tail like any other output.
#[partial]
pub def Pane.append_lines (v : PaneView) (p : PaneModel) (lines : List TLine) : PaneModel :=
    Pane.refresh v { p with transcript := Transcript.append p.transcript lines }

// ── paging ──────────────────────────────────────────────────────────────

/// The loaded window: the loaded page (if any) through the tail.
pub struct LoadedWindow {
    start : I64,
    lines : List TLine
}

pub def Pane.loaded_window (t : Transcript) : LoadedWindow :=
    let start : I64 := match t.page {
        Option.some pg => pg.start,
        Option.none => t.tail_start,
    } in
    let n : I64 := t.total - start in
    let lw : LoadedWindow := { start := start, lines := Transcript.slice t start (if n < 0 then 0 else n) } in
    lw

/// Detail lines still count in the transcript's total; hiding them only
/// changes the rows and the scroll range.
#[partial]
def shown_lines (show : Bool) (ls : List TLine) : List TLine :=
    if show then ls
    else match ls {
        List.empty => List.empty,
        List.cons l rest =>
            if l.detail then shown_lines show rest
            else List.cons l (shown_lines show rest),
    }

pub def Pane.loaded_shown (p : PaneModel) : LoadedWindow :=
    let lw : LoadedWindow := Pane.loaded_window p.transcript in
    let lw2 : LoadedWindow := { start := lw.start, lines := shown_lines p.details lw.lines } in
    lw2

/// Rows nearer than this to the loaded top trigger the next page: the
/// load lands BEFORE the user reaches the boundary, and since the view is
/// anchored to the bottom, content arriving above it does not move it.
pub def Pane.prefetch_rows : I64 := 32

/// The loaded top is (nearly) on screen and older lines exist on disk.
/// `want_top` keeps loading until the true first line, even while pinned
/// at the loaded top. An untouched view (scroll 0, no up intent) never
/// prefetches, so opening a session does not read its history.
pub def Pane.needs_page (p : PaneModel) (w : Window) : Bool :=
    let lw : LoadedWindow := Pane.loaded_window p.transcript in
    if Bool.not (0 < lw.start) then false
    else if p.want_top then true
    else if Bool.not (Bool.or p.want_older (0 < p.scroll)) then false
    else w.start <= Pane.prefetch_rows

/// The range to load: one page ending at the top of the tail, or above
/// the loaded page.
pub def Pane.page_request (p : PaneModel) : Option (Pair I64 I64) :=
    let upto : I64 := match p.transcript.page {
        Option.none => p.transcript.tail_start,
        Option.some pg => pg.start,
    } in
    let req_start : I64 := if upto - Store.page_lines < 0 then 0 else upto - Store.page_lines in
    if Bool.not (req_start < upto)
    then Option.none
    else Option.some (Pair.pair req_start (upto - req_start))

/// The `(start, count)` the pane wants read now: none while a read is in
/// flight or when the window does not reach the loaded top.
pub def Pane.page_wanted (v : PaneView) (p : PaneModel) : Option (Pair I64 I64) :=
    if p.page_pending then Option.none
    else if Pane.needs_page p (Pane.window v p) then Pane.page_request p
    else Option.none

pub def Pane.page_requested (p : PaneModel) : PaneModel :=
    { p with page_pending := true }

/// An older page landed. Pages arrive ABOVE a bottom-anchored view, so
/// the visible content does not move -- except for Home, which stays
/// pinned to the loaded top until the first line is loaded. The bool is
/// false when the same page came back (no progress: stop asking).
pub def Pane.page_loaded (v : PaneView) (p : PaneModel) (pg : TranscriptPage) : Pair PaneModel Bool :=
    let progressed : Bool := Bool.not (same_page p.transcript.page pg) in
    let p1 : PaneModel := { p with transcript := Transcript.with_page p.transcript pg, page_pending := false, key := Option.none } in
    let p2 : PaneModel := if p1.want_top then Pane.refresh v { p1 with scroll := 999999 } else Pane.refresh v p1 in
    let p3 : PaneModel := if pg.start == 0 then { p2 with want_top := false } else p2 in
    if progressed then Pair.pair p3 true
    else Pair.pair (Pane.page_failed p3 "page read made no progress") false

/// A page read failed: the indicator row shows the error while the window
/// still cannot be covered.
pub def Pane.page_failed (p : PaneModel) (e : String) : PaneModel :=
    let tr0 : Transcript := p.transcript in
    let tr : Transcript := { tr0 with page_error := Option.some e } in
    { p with transcript := tr, page_pending := false, key := Option.none }

#[partial]
def tline_count (ls : List TLine) : I64 :=
    match ls {
        List.empty => 0,
        List.cons _ rest => 1 + tline_count rest,
    }

/// The same page served twice means the store cannot cover the window (a
/// short block file, or a window taller than one page).
def same_page (old : Option TranscriptPage) (pg : TranscriptPage) : Bool :=
    match old {
        Option.none => false,
        Option.some q => Bool.and (q.start == pg.start) (tline_count q.lines == tline_count pg.lines),
    }

// ── rows and the window ─────────────────────────────────────────────────

/// The whole loaded window's row count: the scroll clamp's `len`. The
/// unloaded prefix contributes NO rows (a row per unloaded LINE made the
/// space disagree with the loaded one, and scrolling moved through
/// phantom rows).
pub def Pane.row_total_of (v : PaneView) (p : PaneModel) : I64 :=
    let lw : LoadedWindow := Pane.loaded_shown p in
    Rows.count_lines v.colors v.width lw.lines

/// The absolute line containing display row `row`. Hidden detail lines
/// still COUNT as lines, so the indicator's "N lines above" is the true
/// transcript position.
#[partial]
def first_line_at_row_go (colors : Bool) (width : I64) (show : Bool) (lines : List TLine) (abs : I64) (off : I64) (target : I64) : I64 :=
    match lines {
        List.empty => abs,
        List.cons l rest =>
            let n : I64 := if Bool.and (Bool.not show) l.detail then 0 else Rows.count_line colors width l in
            if target < off + n
            then abs
            else first_line_at_row_go colors width show rest (abs + 1) (off + n) target,
    }

pub def Pane.first_line_at_row (v : PaneView) (p : PaneModel) (row : I64) : I64 :=
    let lw : LoadedWindow := Pane.loaded_window p.transcript in
    if row < 0
    then lw.start
    else first_line_at_row_go v.colors v.width p.details lw.lines lw.start 0 row

/// The absolute ROW window shown. `eff` is the clamped scroll; a scrolled
/// pane spends ONE row on the indicator, so the content window is
/// `height - 1` rows ending `eff` rows above the bottom. `start` is
/// relative to the LOADED window; `first_line` is the absolute line at
/// its top, for the indicator.
pub struct Window {
    start : I64,
    count : I64,
    eff : I64,
    first_line : I64,
}

pub def Pane.window (v : PaneView) (p : PaneModel) : Window :=
    let total : I64 := p.row_total in
    let eff : I64 := scroll_clamp p.scroll total v.height in
    let h : I64 := if eff > 0 then v.height - 1 else v.height in
    let endp : I64 := total - eff in
    let start : I64 := if endp - h < 0 then 0 else endp - h in
    let count : I64 := if endp - start < 0 then 0 else endp - start in
    let w : Window := { start := start, count := count, eff := eff, first_line := Pane.first_line_at_row v p start } in
    w

/// The top scroll still allows: at most `len - (height - 1)`, never less
/// than 0 -- so the transcript's FIRST line is reachable at max scroll.
#[partial]
def scroll_clamp (scroll : I64) (len : I64) (height : I64) : I64 :=
    let headroom : I64 := if height < 1 then 0 else len - (height - 1) in
    let room : I64 := if headroom < 0 then 0 else headroom in
    if scroll > room then room
    else if scroll < 0 then 0
    else scroll

/// Collect `count` display rows starting at relative row `start`. The
/// drop is per ROW, so a window can start inside a tall line.
#[partial]
def collect_rows_go (colors : Bool) (width : I64) (lines : List TLine) (off : I64) (start : I64) (count : I64) (acc : List DisplayRow) : List DisplayRow :=
    if count < 1 then acc
    else match lines {
        List.empty => acc,
        List.cons l rest =>
            let rows : List DisplayRow := Rows.of_line colors width l in
            let n : I64 := Rows.length rows in
            let line_end : I64 := off + n in
            if Bool.not (start < line_end)
            then collect_rows_go colors width rest line_end start count acc
            else
                let skip : I64 := if start < off then 0 else start - off in
                let avail : I64 := n - skip in
                let take : I64 := if count < avail then count else avail in
                let picked : List DisplayRow := Rows.take take (Rows.drop skip rows) in
                collect_rows_go colors width rest line_end start (count - take) (List.append acc picked),
    }

/// The rows shown, top to bottom; when scrolled, the indicator row is
/// prepended and spends one content row.
pub def Pane.visible_rows (v : PaneView) (p : PaneModel) : List DisplayRow :=
    let w : Window := Pane.window v p in
    let lw : LoadedWindow := Pane.loaded_shown p in
    let content : List DisplayRow := collect_rows_go v.colors v.width lw.lines 0 w.start w.count List.empty in
    if w.eff > 0
    then
        let text : String := indicator p w in
        List.cons (Rows.plain (theme_line_style_with v.colors text) text) content
    else content

/// A page-read failure replaces the line count while the window still
/// cannot be covered (otherwise the count is the truth).
def indicator (p : PaneModel) (w : Window) : String :=
    match p.transcript.page_error {
        Option.some e => if Pane.needs_page p w then String.concat "page load failed: " e else Pane.indicator_text w.first_line,
        Option.none => Pane.indicator_text w.first_line,
    }

/// `N lines above -- PgDn for latest`; `n` counts the lines STILL above
/// the window's top.
pub def Pane.indicator_text (n : I64) : String :=
    let lines_word : String := if n == 1 then "line above -- PgDn for latest" else "lines above -- PgDn for latest" in
    String.concat (String.concat (I64.to_string n) " ") lines_word

pub def Pane.key_of (v : PaneView) (p : PaneModel) : PaneKey :=
    let pstart : I64 := match p.transcript.page { Option.some pg => pg.start, Option.none => 0 - 1 } in
    let k : PaneKey := { total := p.transcript.total, tail_start := p.transcript.tail_start, page_start := pstart,
                         width := v.width, height := v.height, colors := v.colors, scroll := p.scroll, details := p.details } in
    k

def key_eq (a : PaneKey) (b : PaneKey) : Bool :=
    a.total == b.total && a.tail_start == b.tail_start && a.page_start == b.page_start
        && a.width == b.width && a.height == b.height && a.colors == b.colors
        && a.scroll == b.scroll && a.details == b.details

/// Recompute the rows only when the transcript, the geometry or the
/// scroll actually moved. A rebuild drops the selection: its row indices
/// no longer name the same text.
pub def Pane.refresh (v : PaneView) (p : PaneModel) : PaneModel :=
    let k : PaneKey := Pane.key_of v p in
    match p.key {
        Option.some k0 => if key_eq k k0 then p else rebuild v p k,
        Option.none => rebuild v p k,
    }

def rebuild (v : PaneView) (p : PaneModel) (k : PaneKey) : PaneModel :=
    let rt : I64 := Pane.row_total_of v p in
    let p2 : PaneModel := { p with row_total := rt, scroll := scroll_clamp p.scroll rt v.height, sel := Option.none, rows := List.empty, key := Option.some k } in
    { p2 with rows := Pane.visible_rows v p2 }

// ── mouse selection ─────────────────────────────────────────────────────
// Coordinates are DISPLAY rows (the painted list, indicator included) and
// CELL columns inside the content.

/// The display cell under a mouse report, when it lies inside the pane.
/// `clamp_it` is the drag rule (clamp to the nearest edge); a press must
/// land inside.
#[partial]
def point_in (v : PaneView) (p : PaneModel) (row : I64) (col : I64) (clamp_it : Bool) : Option (Pair I64 I64) :=
    let n : I64 := Rows.length p.rows in
    let w : I64 := v.width in
    let r0 : I64 := row - v.top in
    let c0 : I64 := col - v.left in
    if Bool.or (n < 1) (w < 1)
    then Option.none
    else if clamp_it
    then Option.some (Pair.pair (clamp r0 0 (n - 1)) (clamp c0 0 (w - 1)))
    else if Bool.and (Bool.not (r0 < 0)) (Bool.and (r0 < n) (Bool.and (Bool.not (c0 < 0)) (c0 < w)))
    then Option.some (Pair.pair r0 c0)
    else Option.none

/// A press outside the content clears any prior selection.
def begin_selection (v : PaneView) (p : PaneModel) (row : I64) (col : I64) : PaneModel :=
    match point_in v p row col false {
        Option.none => { p with sel := Option.none },
        Option.some pr => match pr {
            Pair.pair r c =>
                let s : TextSelection := { anchor_row := r, anchor_col := c, focus_row := r, focus_col := c, moved := false } in
                { p with sel := Option.some s },
        },
    }

def drag_selection (v : PaneView) (p : PaneModel) (row : I64) (col : I64) : PaneModel :=
    match p.sel {
        Option.none => p,
        Option.some s => match point_in v p row col true {
            Option.none => p,
            Option.some pr => match pr {
                Pair.pair r c =>
                    let moved : Bool := Bool.or s.moved
                        (Bool.or (Bool.not (r == s.anchor_row)) (Bool.not (c == s.anchor_col))) in
                    let s2 : TextSelection := { s with focus_row := r, focus_col := c, moved := moved } in
                    { p with sel := Option.some s2 },
            },
        },
    }

#[terminating]
def trim_end_spaces (s : String) : String :=
    if String.is_empty s
    then s
    else
        let n : I64 := String.length s in
        if String.slice s (n - 1) 1 == " " then trim_end_spaces (String.slice s 0 (n - 1)) else s

/// The selection normalized to reading order, `right` INCLUSIVE.
struct SelSpan {
    top : I64,
    bottom : I64,
    left : I64,
    right : I64
}

def sel_span (s : TextSelection) : SelSpan :=
    let forward : Bool := Bool.or (s.anchor_row < s.focus_row)
        (Bool.and (s.anchor_row == s.focus_row) (Bool.not (s.focus_col < s.anchor_col))) in
    let top : I64 := if forward then s.anchor_row else s.focus_row in
    let bottom : I64 := if forward then s.focus_row else s.anchor_row in
    let left : I64 := if forward then s.anchor_col else s.focus_col in
    let right : I64 := if forward then s.focus_col else s.anchor_col in
    { top := top, bottom := bottom, left := left, right := right }

#[partial]
def selection_text_go (rows : List DisplayRow) (idx : I64) (sp : SelSpan) (width : I64) (acc : List String) : List String :=
    if sp.bottom < idx then List.reverse acc
    else match rows {
        List.empty => List.reverse acc,
        List.cons r rest =>
            if idx < sp.top
            then selection_text_go rest (idx + 1) sp width acc
            else
                let a : I64 := if idx == sp.top then sp.left else 0 in
                let b : I64 := if idx == sp.bottom then sp.right + 1 else width in
                let piece : String := trim_end_spaces (Text.slice_cols r.text a b) in
                selection_text_go rest (idx + 1) sp width (List.cons piece acc),
    }

/// The selected text, or none for a plain click (no drag) or an empty
/// selection. Rows join with newlines; trailing padding is trimmed, so
/// dragging past the end of a line does not copy blanks.
pub def Pane.selection_text (v : PaneView) (p : PaneModel) : Option String :=
    match p.sel {
        Option.none => Option.none,
        Option.some s =>
            if Bool.not s.moved
            then Option.none
            else
                let pieces : List String := selection_text_go p.rows 0 (sel_span s) v.width List.empty in
                let joined : String := List.intercalate "\n" pieces in
                if String.is_empty joined then Option.none else Option.some joined,
    }

/// The half-open cell span to highlight on display row `idx`.
pub def Pane.selection_cols (v : PaneView) (p : PaneModel) (idx : I64) : Option (Pair I64 I64) :=
    match p.sel {
        Option.none => Option.none,
        Option.some s =>
            let sp : SelSpan := sel_span s in
            if Bool.or (idx < sp.top) (sp.bottom < idx)
            then Option.none
            else match Rows.at p.rows idx {
                Option.none => Option.none,
                Option.some r =>
                    let a : I64 := if idx == sp.top then sp.left else 0 in
                    let b : I64 := if idx == sp.bottom then sp.right + 1 else v.width in
                    match Text.snap_span r.text a b {
                        Pair.pair sa sb => Option.some (Pair.pair sa sb),
                    },
            },
    }

pub def Pane.selecting (p : PaneModel) : Bool :=
    match p.sel {
        Option.some _ => true,
        Option.none => false,
    }

// ── the scrollbar ───────────────────────────────────────────────────────
// It covers only the pane's own rows, never the live rows under it.

pub def Pane.bar_visible (v : PaneView) (p : PaneModel) : Bool :=
    Bool.and v.bar (Bool.and (I64.lt 1 v.height) (I64.lt v.height p.row_total))

def bar_room (v : PaneView) (p : PaneModel) : I64 :=
    if I64.lt p.row_total (v.height - 1) then 0 else p.row_total - (v.height - 1)

/// `(top, length)` in pane-relative rows; none when not scrollable.
pub def Pane.thumb (v : PaneView) (p : PaneModel) : Option (Pair I64 I64) :=
    if Bool.not (Pane.bar_visible v p)
    then Option.none
    else
        let h : I64 := v.height in
        let total : I64 := if I64.lt p.row_total 1 then 1 else p.row_total in
        let w : Window := Pane.window v p in
        let eff : I64 := w.eff in
        let vh : I64 := if I64.gt eff 0 then h - 1 else h in
        let len0 : I64 := (vh * h) / total in
        let len : I64 := if I64.lt len0 1 then 1 else if I64.gt len0 h then h else len0 in
        let room : I64 := bar_room v p in
        if I64.lt room 1
        then Option.some (Pair.pair (h - len) len)
        else
            let span : I64 := h - len in
            let off : I64 := if I64.lt span 1 then 0 else (eff * span) / room in
            Option.some (Pair.pair (span - off) len)

pub def Pane.bar_hit (v : PaneView) (p : PaneModel) (row : I64) (col : I64) : Bool :=
    Bool.and (I64.beq col (v.left + v.width))
        (Bool.and (Pane.bar_visible v p)
            (Bool.and (Bool.not (I64.lt row v.top)) (I64.lt row (v.top + v.height))))

/// Where a pointer row puts the scroll for a grab offset.
def bar_scroll_for (v : PaneView) (p : PaneModel) (row : I64) (grab : I64) : I64 :=
    match Pane.thumb v p {
        Option.none => p.scroll,
        Option.some pr => match pr {
            Pair.pair _ len =>
                let span : I64 := v.height - len in
                let target_top : I64 := clamp (row - v.top - grab) 0 span in
                if I64.lt span 1
                then 0
                else (span - target_top) * bar_room v p / span,
        },
    }

/// A press on the thumb grabs it where it was hit; one on the track
/// centres the thumb there. Either way the drag continues from it.
def bar_press (v : PaneView) (p : PaneModel) (row : I64) : PaneModel :=
    match Pane.thumb v p {
        Option.none => p,
        Option.some pr => match pr {
            Pair.pair top len =>
                let rel : I64 := row - v.top in
                let in_thumb : Bool := Bool.and (Bool.not (I64.lt rel top)) (I64.lt rel (top + len)) in
                let grab : I64 := if in_thumb then rel - top else len / 2 in
                Pane.scroll_to v { p with bar_grab := Option.some grab, sel := Option.none } (bar_scroll_for v p row grab),
        },
    }

#[partial]
def bar_rows (colors : Bool) (i : I64) (h : I64) (top : I64) (len : I64) : List SizedWidget :=
    if I64.lt (h - 1) i
    then List.empty
    else
        let thumb : Bool := Bool.and (Bool.not (I64.lt i top)) (I64.lt i (top + len)) in
        let glyph : String := if thumb then "█" else "│" in
        let style : TextStyle :=
            if thumb then theme_scrollbar_thumb_style_with colors
            else theme_border_style_with colors in
        List.cons (sized (LayoutSize.fixed 1) (with_style style (label glyph)))
            (bar_rows colors (i + 1) h top len)

/// The bar's column: exactly `height` rows, or empty when not scrollable.
pub def Pane.bar_view (v : PaneView) (p : PaneModel) : Widget :=
    match Pane.thumb v p {
        Option.none => Widget.column List.empty,
        Option.some pr => match pr {
            Pair.pair top len => Widget.column (bar_rows v.colors 0 v.height top len),
        },
    }

// ── view ────────────────────────────────────────────────────────────────

#[partial]
def row_widgets_go (v : PaneView) (p : PaneModel) (rows : List DisplayRow) (i : I64) : List SizedWidget :=
    match rows {
        List.empty => List.empty,
        List.cons r rest => List.cons (Rows.widget_selected r (Pane.selection_cols v p i)) (row_widgets_go v p rest (i + 1)),
    }

/// The cached rows, the selection highlighted.
pub def Pane.row_widgets (v : PaneView) (p : PaneModel) : List SizedWidget :=
    row_widgets_go v p p.rows 0
