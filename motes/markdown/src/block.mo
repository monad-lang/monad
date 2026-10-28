/// The block pass: CommonMark's line-oriented block structure.
///
/// The state is an immutable stack of open blocks, INNERMOST FIRST, with the
/// document root at the bottom. Each open block owns its children in reverse;
/// closing the innermost block is therefore one pop plus one `cons` into the
/// new head (its parent), and the whole document is reversed exactly once.
///
/// Per line, in cmark's order:
///   1. match the open containers outermost to innermost, consuming their
///      prefixes; the first failure ends the matched run;
///   2. lazy continuation -- a non-blank line that starts no block continues
///      an open paragraph without closing the containers around it;
///   3. close the unmatched containers (innermost first);
///   4. start new blocks in CommonMark's precedence, then add the line.
///
/// Paragraphs, headings and table cells keep SOURCE text in this pass: inline
/// parsing runs afterwards (`parse.mo`), when every link reference definition
/// in the document is known.
///
/// HTML blocks (Phase 2) and GFM tables (Phase 4) slot into `accepts_line`,
/// `starts_block` and `finalize_open`.
use init::string {}
use parsec::core {is_empty}
use lib::options {Markdown.Options}
use lib::scan {
    Markdown.Cursor, Markdown.char_width, Markdown.is_blank,
}
use lib::block_html {Markdown.html_block_ends, Markdown.html_block_start}
use lib::inline {Markdown.unescape}
use lib::types {Markdown.Align, Markdown.ListKind, Markdown.RawBlock, Markdown.RawItem}

open Markdown.RawBlock {
    raw_paragraph, raw_heading, raw_thematic_break, raw_code_block,
    raw_block_quote, raw_list, raw_table, raw_html_block,
}
open Markdown.ListKind {list_bullet, list_ordered}

// ─── Open blocks ───

type Markdown.OpenBlock {
    open_doc (blocks : List Markdown.RawBlock),
    open_blockquote (blocks : List Markdown.RawBlock),
    open_list (kind : Markdown.ListKind) (loose : Bool) (items : List Markdown.RawItem) (last_blank : Bool),
    open_item (content_indent : I64) (checked : Option Bool) (blocks : List Markdown.RawBlock) (ends_blank : Bool) (between_blank : Bool),
    open_paragraph (lines : List String),
    open_fence (info : Option String) (fence_char : U8) (fence_len : I64) (indent : I64) (lines : List String),
    open_indented_code (lines : List String),
    open_html (html_type : I64) (lines : List String),
    open_table (aligns : List Markdown.Align) (head : List String) (rows : List (List String))
}

struct Markdown.BlockState {
    stack : List Markdown.OpenBlock,
    opts : Markdown.Options
}

/// What closing an open block produces.
type Markdown.Finalized {
    fin_block (block : Markdown.RawBlock),
    fin_item (item : Markdown.RawItem) (ends_blank : Bool) (between_blank : Bool),
    fin_none,
    fin_document
}

/// What `open_new` did with a line: built a whole block (ATX heading,
/// thematic break, setext), opened a block that takes this line, or nothing.
type Markdown.Started {
    started_consumed (state : Markdown.BlockState),
    // opened and the line is consumed by the opener itself (a fence line)
    started_opened (state : Markdown.BlockState),
    started_line (state : Markdown.BlockState) (cursor : Markdown.Cursor),
    // `opened` says whether any container was opened on the way, which is what
    // tells cmark's lazy rule apart ("container == last_matched").
    started_none (state : Markdown.BlockState) (cursor : Markdown.Cursor) (opened : Bool)
}

/// The result of matching a line against the open containers.
struct Markdown.MatchResult {
    matched : List Markdown.OpenBlock,
    unmatched : List Markdown.OpenBlock,
    cursor : Markdown.Cursor
}

def Markdown.mk_state (stack : List Markdown.OpenBlock) (opts : Markdown.Options) : Markdown.BlockState :=
    let s : Markdown.BlockState := { stack := stack, opts := opts } in s

def Markdown.with_stack (stack : List Markdown.OpenBlock) (state : Markdown.BlockState) : Markdown.BlockState :=
    let s : Markdown.BlockState := { stack := stack, opts := state.opts } in s

def Markdown.mk_match
    (matched : List Markdown.OpenBlock) (unmatched : List Markdown.OpenBlock) (cursor : Markdown.Cursor)
    : Markdown.MatchResult :=
    let m : Markdown.MatchResult :=
        { matched := matched, unmatched := unmatched, cursor := cursor } in m

def Markdown.stack_len_go (stack : List Markdown.OpenBlock) (n : I64) : I64 :=
    match stack {
        List.empty => n,
        List.cons _ rest => Markdown.stack_len_go rest (I64.add n 1i64)
    }

def Markdown.stack_len (stack : List Markdown.OpenBlock) : I64 :=
    Markdown.stack_len_go stack 0i64

// ─── Small string helpers ───

/// The byte length of `s` with trailing spaces and tabs removed.
#[partial]
def Markdown.trim_end_go (s : String) (i : I64) (end : I64) : Pair I64 I64 :=
    if is_empty s
    then Pair.pair i end
    else
        match String.get s 0 {
            Option.some b =>
                let w : I64 := Markdown.char_width s in
                if Bool.or (U8.beq b 32u8) (U8.beq b 9u8)
                then Markdown.trim_end_go (String.drop w s) (I64.add i w) end
                else Markdown.trim_end_go (String.drop w s) (I64.add i w) (I64.add i w),
            Option.none => Pair.pair i end
        }

pub def Markdown.trim_end (s : String) : String :=
    match Markdown.trim_end_go s 0i64 0i64 {
        Pair.pair _ end => String.slice s 0 end
    }

/// Whether the trailing (non-space) character is a space or tab.
pub def Markdown.ends_with_space (s : String) : Bool :=
    match Markdown.trim_end_go s 0i64 0i64 {
        Pair.pair len end => I64.lt end len
    }

#[partial]
def Markdown.contains_byte_go (s : String) (b : U8) : Bool :=
    if is_empty s
    then false
    else
        match String.get s 0 {
            Option.some x =>
                if U8.beq x b
                then true
                else Markdown.contains_byte_go (String.drop (Markdown.char_width s) s) b,
            Option.none => false
        }

pub def Markdown.contains_byte (s : String) (b : U8) : Bool :=
    Markdown.contains_byte_go s b

/// Join lines with `\n` between them (no trailing newline).
#[partial]
def Markdown.interleave_rev (lines : List String) (acc : List String) : List String :=
    match lines {
        List.empty => acc,
        List.cons l rest =>
            match rest {
                List.empty => List.cons l acc,
                List.cons _ _ => Markdown.interleave_rev rest (List.cons "\n" (List.cons l acc))
            }
    }

pub def Markdown.join_plain (lines : List String) : String :=
    String.concat_list (List.reverse (Markdown.interleave_rev lines List.empty))

/// Join lines, each terminated by `\n` (what a code block literal is).
#[partial]
def Markdown.terminated_rev (lines : List String) (acc : List String) : List String :=
    match lines {
        List.empty => acc,
        List.cons l rest => Markdown.terminated_rev rest (List.cons (String.concat l "\n") acc)
    }

pub def Markdown.join_terminated (lines : List String) : String :=
    String.concat_list (List.reverse (Markdown.terminated_rev lines List.empty))

// ─── Runs and markers ───

/// Count a run of `b` at the cursor, returning the count and the cursor after.
#[partial]
def Markdown.count_run (b : U8) (c : Markdown.Cursor) (n : I64) : Pair I64 Markdown.Cursor :=
    match Markdown.Cursor.peek c {
        Option.some x =>
            if U8.beq x b
            then Markdown.count_run b (Markdown.Cursor.step c) (I64.add n 1i64)
            else Pair.pair n c,
        Option.none => Pair.pair n c
    }

/// Consume at most one space or tab.
def Markdown.Cursor.skip_one_space (c : Markdown.Cursor) : Markdown.Cursor :=
    match Markdown.Cursor.peek c {
        Option.some b =>
            if Bool.or (U8.beq b 32u8) (U8.beq b 9u8)
            then Markdown.Cursor.step c
            else c,
        Option.none => c
    }

/// Consume up to `n` leading whitespace characters (a fenced code block
/// strips at most its opener's indent from a content line).
#[partial]
def Markdown.Cursor.strip_up_to (n : I64) (c : Markdown.Cursor) : Markdown.Cursor :=
    if I64.lt n 1i64
    then c
    else
        match Markdown.Cursor.peek c {
            Option.some b =>
                if Bool.or (U8.beq b 32u8) (U8.beq b 9u8)
                then Markdown.Cursor.strip_up_to (I64.sub n 1i64) (Markdown.Cursor.step c)
                else c,
            Option.none => c
        }

def Markdown.Cursor.byte (c : Markdown.Cursor) : U8 :=
    match Markdown.Cursor.peek c {
        Option.some b => b,
        Option.none => 0u8
    }

// ─── ATX headings ───

pub struct Markdown.Atx {
    level : I64,
    text : String
}

def Markdown.atx_content (after_marks : Markdown.Cursor) : String :=
    Markdown.trim_end (Markdown.strip_closing_hashes (Markdown.trim_end after_marks.text))

#[partial]
def Markdown.trailing_hashes (s : String) (i : I64) (run_start : I64) : Pair I64 I64 :=
    if is_empty s
    then Pair.pair (I64.sub i run_start) run_start
    else
        match String.get s 0 {
            Option.some b =>
                let w : I64 := Markdown.char_width s in
                if U8.beq b 35u8
                then Markdown.trailing_hashes (String.drop w s) (I64.add i w) run_start
                else Markdown.trailing_hashes (String.drop w s) (I64.add i w) (I64.add i w),
            Option.none => Pair.pair (I64.sub i run_start) run_start
        }

/// Remove a trailing `#` run, leaving the string alone when the run is not
/// preceded by a space and does not start the content.
#[partial]
pub def Markdown.strip_closing_hashes (s : String) : String :=
    match Markdown.trailing_hashes s 0i64 0i64 {
        Pair.pair hashes run_start =>
            if I64.lt hashes 1i64
            then s
            else
                let before : String := String.slice s 0 run_start in
                if Bool.or (String.beq before "") (Markdown.ends_with_space before)
                then before
                else s
    }

pub def Markdown.try_atx (c : Markdown.Cursor) (base : I64) : Option Markdown.Atx :=
    if I64.gt (I64.sub c.column base) 3i64
    then Option.none
    else
        match Markdown.count_run 35u8 c 0i64 {
            Pair.pair n after =>
                if Bool.or (I64.lt n 1i64) (I64.lt 6i64 n)
                then Option.none
                else
                    match Markdown.Cursor.peek after {
                        Option.none =>
                            let h : Markdown.Atx := { level := n, text := "" } in
                            Option.some h,
                        Option.some b =>
                            if Bool.or (U8.beq b 32u8) (U8.beq b 9u8)
                            then
                                let h : Markdown.Atx :=
                                    { level := n,
                                      text := Markdown.atx_content (Markdown.Cursor.skip_spaces after) } in
                                Option.some h
                            else Option.none
                    }
        }

// ─── Fenced code ───

pub struct Markdown.FenceStart {
    info : Option String,
    fence_char : U8,
    fence_len : I64,
    indent : I64
}

pub def Markdown.try_fence (c : Markdown.Cursor) (base : I64) : Option Markdown.FenceStart :=
    if I64.gt (I64.sub c.column base) 3i64
    then Option.none
    else
        match Markdown.Cursor.peek c {
            Option.some b =>
                if Bool.or (U8.beq b 96u8) (U8.beq b 126u8)
                then
                    match Markdown.count_run b c 0i64 {
                        Pair.pair n after =>
                            if I64.lt n 3i64
                            then Option.none
                            else
                                let info_cursor : Markdown.Cursor := Markdown.Cursor.skip_spaces after in
                                let info_text : String :=
                                    Markdown.unescape
                                        (Markdown.trim_end (Markdown.Cursor.materialize info_cursor)) in
                                if Bool.and (U8.beq b 96u8) (Markdown.contains_byte info_text 96u8)
                                then Option.none
                                else
                                    let info : Option String :=
                                        if String.beq info_text "" then Option.none else Option.some info_text in
                                    let f : Markdown.FenceStart :=
                                        { info := info, fence_char := b, fence_len := n, indent := c.column } in
                                    Option.some f
                    }
                else Option.none,
            Option.none => Option.none
        }

/// A closing fence: at most three columns of indent from `c`, the same
/// character, at least as long as the opener, and nothing after it but spaces
/// and tabs.
pub def Markdown.is_closing_fence_at (c : Markdown.Cursor) (fence_char : U8) (fence_len : I64) : Bool :=
    let started : Markdown.Cursor := Markdown.Cursor.skip_spaces c in
    if I64.gt (I64.sub started.column c.column) 3i64
    then false
    else
        match Markdown.count_run fence_char started 0i64 {
            Pair.pair n after => Bool.and (Bool.not (I64.lt n fence_len)) (Markdown.Cursor.blank after)
        }

// ─── Thematic breaks ───

#[partial]
def Markdown.thematic_go (b : U8) (c : Markdown.Cursor) (n : I64) : Bool :=
    match Markdown.Cursor.peek c {
        Option.some x =>
            if U8.beq x b
            then Markdown.thematic_go b (Markdown.Cursor.step c) (I64.add n 1i64)
            else if Bool.or (U8.beq x 32u8) (U8.beq x 9u8)
            then Markdown.thematic_go b (Markdown.Cursor.step c) n
            else false,
        Option.none => Bool.not (I64.lt n 3i64)
    }

pub def Markdown.is_thematic (c : Markdown.Cursor) (base : I64) : Bool :=
    if I64.gt (I64.sub c.column base) 3i64
    then false
    else
        match Markdown.Cursor.peek c {
            Option.some b =>
                if Bool.or (Bool.or (U8.beq b 42u8) (U8.beq b 45u8)) (U8.beq b 95u8)
                then Markdown.thematic_go b c 0i64
                else false,
            Option.none => false
        }

// ─── Setext underlines ───

pub def Markdown.try_setext (c : Markdown.Cursor) (base : I64) : Option I64 :=
    if I64.gt (I64.sub c.column base) 3i64
    then Option.none
    else
        match Markdown.Cursor.peek c {
            Option.some b =>
                if Bool.or (U8.beq b 61u8) (U8.beq b 45u8)
                then
                    match Markdown.count_run b c 0i64 {
                        Pair.pair _ after =>
                            if Markdown.Cursor.blank after
                            then (if U8.beq b 61u8 then Option.some 1i64 else Option.some 2i64)
                            else Option.none
                    }
                else Option.none,
            Option.none => Option.none
        }

// ─── Block quotes ───

pub def Markdown.is_blockquote (c : Markdown.Cursor) (base : I64) : Bool :=
    if I64.gt (I64.sub c.column base) 3i64
    then false
    else U8.beq (Markdown.Cursor.byte c) 62u8

/// Consume a `>` marker and one optional space.
pub def Markdown.consume_blockquote (c : Markdown.Cursor) : Markdown.Cursor :=
    Markdown.Cursor.skip_one_space (Markdown.Cursor.step c)

// ─── List items ───

pub struct Markdown.ListStart {
    kind : Markdown.ListKind,
    content_indent : I64,
    content : Markdown.Cursor
}

/// Digits at the head: (value, digit count).
#[partial]
def Markdown.take_ordered_number (c : Markdown.Cursor) (acc : I64) (n : I64) : Pair I64 I64 :=
    if Bool.not (I64.lt n 9i64)
    then Pair.pair acc n
    else
        match Markdown.Cursor.peek c {
            Option.some b =>
                if Bool.and (U8.lt 47u8 b) (U8.lt b 58u8)
                then
                    let d : I64 := Markdown.digit_of b in
                    Markdown.take_ordered_number (Markdown.Cursor.step c) (I64.add (I64.mul acc 10i64) d) (I64.add n 1i64)
                else Pair.pair acc n,
            Option.none => Pair.pair acc n
        }

def Markdown.digit_of (b : U8) : I64 :=
    if U8.beq b 48u8 then 0i64
    else if U8.beq b 49u8 then 1i64
    else if U8.beq b 50u8 then 2i64
    else if U8.beq b 51u8 then 3i64
    else if U8.beq b 52u8 then 4i64
    else if U8.beq b 53u8 then 5i64
    else if U8.beq b 54u8 then 6i64
    else if U8.beq b 55u8 then 7i64
    else if U8.beq b 56u8 then 8i64
    else 9i64

/// A list marker at `c` (the first non-space column).
///
/// `in_paragraph` applies the interruption rules: an empty item and an
/// ordered list not starting at 1 cannot interrupt a paragraph.
pub def Markdown.try_list_item (c : Markdown.Cursor) (in_paragraph : Bool) (base : I64) : Option Markdown.ListStart :=
    if I64.gt (I64.sub c.column base) 3i64
    then Option.none
    else
        match Markdown.Cursor.peek c {
            Option.none => Option.none,
            Option.some b =>
                if Bool.or (Bool.or (U8.beq b 45u8) (U8.beq b 43u8)) (U8.beq b 42u8)
                then
                    Markdown.finish_list_item c (list_bullet (String.slice c.text 0 1i64)) 1i64
                        in_paragraph Option.none
                else if Bool.and (U8.lt 47u8 b) (U8.lt b 58u8)
                then
                    match Markdown.take_ordered_number c 0i64 0i64 {
                        Pair.pair start digits =>
                            let delim : Markdown.Cursor := Markdown.Cursor.step_many digits c in
                            match Markdown.Cursor.peek delim {
                                Option.some d =>
                                    if Bool.or (U8.beq d 46u8) (U8.beq d 41u8)
                                    then
                                        let kind : Markdown.ListKind :=
                                            list_ordered start (String.slice delim.text 0 1i64) in
                                        Markdown.finish_list_item c kind (I64.add digits 1i64)
                                            in_paragraph (Option.some start)
                                    else Option.none,
                                Option.none => Option.none
                            }
                    }
                else Option.none
        }

/// Shared tail of list-marker parsing. `ordered_start` is `none` for bullets.
def Markdown.finish_list_item
    (c : Markdown.Cursor) (kind : Markdown.ListKind) (marker_len : I64)
    (in_paragraph : Bool) (ordered_start : Option I64) : Option Markdown.ListStart :=
    let after_marker : Markdown.Cursor := Markdown.Cursor.step_many marker_len c in
    let space_end : Markdown.Cursor := Markdown.Cursor.skip_spaces after_marker in
    let marker_end : I64 := I64.add c.column marker_len in
    let padding_raw : I64 := I64.sub space_end.column marker_end in
    let blank_item : Bool := Markdown.Cursor.blank space_end in
    let ordered_ok : Bool :=
        match ordered_start {
            Option.some start => I64.beq start 1i64,
            Option.none => true
        } in
    let interrupts : Bool :=
        Bool.and in_paragraph (Bool.or (Bool.not ordered_ok) blank_item) in
    let separator_ok : Bool :=
        if blank_item
        then true
        else Bool.or (U8.beq (Markdown.Cursor.byte after_marker) 32u8)
                (U8.beq (Markdown.Cursor.byte after_marker) 9u8) in
    if Bool.or interrupts (Bool.not separator_ok)
    then Option.none
    else
        let padding : I64 :=
            if Bool.or (I64.lt 4i64 padding_raw) blank_item then 1i64 else padding_raw in
        let content_indent : I64 := I64.add marker_end padding in
        let content : Markdown.Cursor :=
            Markdown.Cursor.step_many (I64.sub content_indent c.column) c in
        let start : Markdown.ListStart :=
            { kind := kind, content_indent := content_indent, content := content } in
        Option.some start

// ─── Container matching ───

/// Whether `b` accepts the line at `c`, and at which cursor. Leaves always
/// accept here: their continuation is decided by the tip dispatch.
#[partial]
def Markdown.accepts_line (b : Markdown.OpenBlock) (has_child : Bool) (c : Markdown.Cursor) : Option Markdown.Cursor :=
    match b {
        open_doc _ => Option.some c,
        open_blockquote _ =>
            if Markdown.Cursor.blank c
            then Option.some c
            else
                let started : Markdown.Cursor := Markdown.Cursor.skip_spaces c in
                if Markdown.is_blockquote started c.column
                then Option.some (Markdown.consume_blockquote started)
                else Option.none,
        open_list _ _ _ _ => Option.some c,
        open_item content_indent _ blocks _ _ => Markdown.accepts_item content_indent blocks has_child c,
        open_paragraph _ =>
            if Markdown.Cursor.blank c then Option.none else Option.some c,
        open_html html_type _ =>
            if Markdown.Cursor.blank c
            then (if I64.lt html_type 6i64 then Option.some c else Option.none)
            else Option.some c,
        _ => Option.some c
    }

/// A list item accepts a line when its first non-space column reaches the
/// content indent (consume exactly up to it), or when the line is blank and
/// the item already has content.
def Markdown.accepts_item
    (content_indent : I64) (blocks : List Markdown.RawBlock) (has_child : Bool) (c : Markdown.Cursor)
    : Option Markdown.Cursor :=
    let first : Markdown.Cursor := Markdown.Cursor.skip_spaces c in
    if Bool.not (I64.lt first.column content_indent)
    then Option.some (Markdown.Cursor.step_many (I64.sub content_indent c.column) c)
    else if Bool.and (Markdown.Cursor.blank c)
            (Bool.or (Bool.not (List.is_empty blocks)) has_child)
    then Option.some first
    else Option.none

#[partial]
def Markdown.match_walk
    (rest : List Markdown.OpenBlock) (matched : List Markdown.OpenBlock) (c : Markdown.Cursor)
    : Markdown.MatchResult :=
    match rest {
        List.empty => Markdown.mk_match (List.reverse matched) List.empty c,
        List.cons b tail =>
            match Markdown.accepts_line b (Bool.not (List.is_empty tail)) c {
                Option.some c2 => Markdown.match_walk tail (List.cons b matched) c2,
                Option.none => Markdown.mk_match (List.reverse matched) (List.reverse (List.cons b tail)) c
            }
    }

pub def Markdown.match_containers (stack : List Markdown.OpenBlock) (c : Markdown.Cursor) : Markdown.MatchResult :=
    Markdown.match_walk (List.reverse stack) List.empty c

// ─── Closing ───

#[partial]
def Markdown.drop_blank_head (lines : List String) : List String :=
    match lines {
        List.empty => lines,
        List.cons l rest => if Markdown.is_blank l then Markdown.drop_blank_head rest else lines
    }

def Markdown.finalize_open (b : Markdown.OpenBlock) : Markdown.Finalized :=
    match b {
        open_doc _ => Markdown.Finalized.fin_document,
        open_blockquote blocks => Markdown.Finalized.fin_block (raw_block_quote (List.reverse blocks)),
        open_list kind loose items _ =>
            Markdown.Finalized.fin_block (raw_list kind (Bool.not loose) (List.reverse items)),
        open_item _ checked blocks ends between =>
            Markdown.Finalized.fin_item (Markdown.mk_raw_item checked (List.reverse blocks)) ends between,
        open_paragraph lines =>
            match lines {
                List.empty => Markdown.Finalized.fin_none,
                List.cons _ _ => Markdown.Finalized.fin_block (raw_paragraph (List.reverse lines))
            },
        open_fence info _ _ _ lines =>
            Markdown.Finalized.fin_block (raw_code_block info (Markdown.join_terminated (List.reverse lines))),
        open_indented_code lines =>
            match Markdown.drop_blank_head lines {
                List.empty => Markdown.Finalized.fin_none,
                List.cons _ _ =>
                    Markdown.Finalized.fin_block
                        (raw_code_block Option.none
                            (Markdown.join_terminated (List.reverse (Markdown.drop_blank_head lines))))
            },
        open_html _ lines => Markdown.Finalized.fin_block (raw_html_block (Markdown.join_plain (List.reverse lines))),
        open_table aligns head rows =>
            Markdown.Finalized.fin_block (raw_table aligns (List.reverse head) (List.reverse rows))
    }

def Markdown.mk_raw_item (checked : Option Bool) (blocks : List Markdown.RawBlock) : Markdown.RawItem :=
    let i : Markdown.RawItem := { checked := checked, blocks := blocks } in i

/// Put a finished block into the current stack head, which is its parent.
#[partial]
def Markdown.push_into (b : Markdown.RawBlock) (state : Markdown.BlockState) : Markdown.BlockState :=
    match state.stack {
        List.empty => state,
        List.cons parent tail =>
            match parent {
                open_doc blocks =>
                    Markdown.with_stack (List.cons (Markdown.OpenBlock.open_doc (List.cons b blocks)) tail) state,
                open_blockquote blocks =>
                    Markdown.with_stack (List.cons (Markdown.OpenBlock.open_blockquote (List.cons b blocks)) tail) state,
                open_item indent checked blocks ends between =>
                    Markdown.with_stack
                        (List.cons (Markdown.OpenBlock.open_item indent checked (List.cons b blocks) ends between) tail)
                        state,
                _ => state
            }
    }

/// Close one item into its list, folding blank-line state into looseness.
#[partial]
def Markdown.push_item_into
    (item : Markdown.RawItem) (ends_blank : Bool) (between_blank : Bool)
    (state : Markdown.BlockState) : Markdown.BlockState :=
    match state.stack {
        List.empty => state,
        List.cons parent tail =>
            match parent {
                open_list kind loose items last_blank =>
                    Markdown.with_stack
                        (List.cons
                            (Markdown.OpenBlock.open_list kind
                                (Bool.or loose between_blank)
                                (List.cons item items)
                                ends_blank)
                            tail)
                        state,
                _ => state
            }
    }

#[partial]
def Markdown.close_tip (state : Markdown.BlockState) : Markdown.BlockState :=
    match state.stack {
        List.empty => state,
        List.cons top rest =>
            match Markdown.finalize_open top {
                Markdown.Finalized.fin_block b => Markdown.push_into b (Markdown.with_stack rest state),
                Markdown.Finalized.fin_item i ends between =>
                    Markdown.push_item_into i ends between (Markdown.with_stack rest state),
                Markdown.Finalized.fin_none => Markdown.with_stack rest state,
                Markdown.Finalized.fin_document => state
            }
    }

#[partial]
def Markdown.close_all (state : Markdown.BlockState) : Markdown.BlockState :=
    if I64.lt (Markdown.stack_len state.stack) 2i64
    then state
    else Markdown.close_all (Markdown.close_tip state)

#[partial]
def Markdown.close_unmatched (state : Markdown.BlockState) (unmatched : List Markdown.OpenBlock) : Markdown.BlockState :=
    match unmatched {
        List.empty => state,
        List.cons _ rest => Markdown.close_unmatched (Markdown.close_tip state) rest
    }

pub def Markdown.finish (state : Markdown.BlockState) : List Markdown.RawBlock :=
    let done : Markdown.BlockState := Markdown.close_all state in
    match done.stack {
        List.empty => List.empty,
        List.cons top _ =>
            match top {
                open_doc blocks => List.reverse blocks,
                _ => List.empty
            }
    }

// ─── Opening ───

def Markdown.open_leaf (b : Markdown.OpenBlock) (state : Markdown.BlockState) : Markdown.BlockState :=
    let s : Markdown.BlockState := { stack := List.cons b state.stack, opts := state.opts } in s

def Markdown.replace_tip (b : Markdown.OpenBlock) (state : Markdown.BlockState) : Markdown.BlockState :=
    match state.stack {
        List.empty => state,
        List.cons _ rest => Markdown.with_stack (List.cons b rest) state
    }

pub def Markdown.same_list_kind (a b : Markdown.ListKind) : Bool :=
    match a {
        list_bullet m1 => match b {
            list_bullet m2 => String.beq m1 m2,
            list_ordered _ _ => false
        },
        list_ordered _ d1 => match b {
            list_ordered _ d2 => String.beq d1 d2,
            list_bullet _ => false
        }
    }

/// A list is not a valid parent for a block: close it before starting one.
#[partial]
def Markdown.close_list_tip (state : Markdown.BlockState) : Markdown.BlockState :=
    match state.stack {
        List.empty => state,
        List.cons top _ =>
            match top {
                open_list _ _ _ _ => Markdown.close_tip state,
                _ => state
            }
    }

/// Open the list a new item belongs to: reuse the tip when it already is a
/// list with the same marker and delimiter, else start one. A list whose
/// previous item ended with a blank line becomes loose.
def Markdown.open_list_for (start : Markdown.ListStart) (state : Markdown.BlockState) : Markdown.BlockState :=
    match state.stack {
        List.empty => state,
        List.cons top rest =>
            match top {
                open_list kind loose items last_blank =>
                    if Markdown.same_list_kind kind start.kind
                    then
                        Markdown.with_stack
                            (List.cons (Markdown.OpenBlock.open_list kind (Bool.or loose last_blank) items false) rest)
                            state
                    else
                        Markdown.open_leaf (Markdown.OpenBlock.open_list start.kind false List.empty false)
                            (Markdown.close_list_tip state),
                _ => Markdown.open_leaf (Markdown.OpenBlock.open_list start.kind false List.empty false) state
            }
    }

def Markdown.open_item_for (start : Markdown.ListStart) (state : Markdown.BlockState) : Markdown.BlockState :=
    Markdown.open_leaf
        (Markdown.OpenBlock.open_item start.content_indent Option.none List.empty false false)
        state

/// A new sibling block ends an open paragraph: cmark re-parents the new
/// block, which has the same effect.
#[partial]
def Markdown.close_paragraph_tip (state : Markdown.BlockState) : Markdown.BlockState :=
    if Markdown.tip_is_paragraph state then Markdown.close_tip state else state

def Markdown.tip_is_paragraph (state : Markdown.BlockState) : Bool :=
    match state.stack {
        List.empty => false,
        List.cons top _ =>
            match top {
                open_paragraph _ => true,
                _ => false
            }
    }

def Markdown.tip_is_code_or_html (state : Markdown.BlockState) : Bool :=
    match state.stack {
        List.empty => false,
        List.cons top _ =>
            match top {
                open_fence _ _ _ _ _ => true,
                open_indented_code _ => true,
                open_html _ _ => true,
                _ => false
            }
    }

def Markdown.tip_paragraph_lines (state : Markdown.BlockState) : List String :=
    match state.stack {
        List.empty => List.empty,
        List.cons top _ =>
            match top {
                open_paragraph lines => lines,
                _ => List.empty
            }
    }

/// CommonMark's block-start precedence, as cmark's `open_new_blocks`: block
/// quote, ATX heading, fenced code, HTML block, setext underline, thematic
/// break, list item, indented code. Returns what to do with the line.
///
/// `maybe_lazy` is whether the deepest open block (before any closing) is a
/// paragraph: an indented code block and a type-7 HTML block may not open in
/// that case.
#[partial]
def Markdown.open_new
    (state : Markdown.BlockState) (c : Markdown.Cursor) (all_matched : Bool) (maybe_lazy : Bool)
    : Markdown.Started :=
    if Markdown.Cursor.blank c
    then Markdown.Started.started_none state c false
    else
        let base : I64 := c.column in
        let first : Markdown.Cursor := Markdown.Cursor.skip_spaces c in
        let prepared : Markdown.BlockState := Markdown.close_paragraph_tip state in
        if Markdown.is_blockquote first base
        then
            Markdown.mark_opened
                (Markdown.open_new
                    (Markdown.open_leaf (Markdown.OpenBlock.open_blockquote List.empty) prepared)
                    (Markdown.consume_blockquote first) all_matched maybe_lazy)
        else
            match Markdown.try_atx first base {
                Option.some h =>
                    Markdown.Started.started_consumed
                        (Markdown.push_into (raw_heading h.level [h.text]) prepared),
                Option.none =>
                    match Markdown.try_fence first base {
                        Option.some f =>
                            Markdown.Started.started_opened
                                (Markdown.open_leaf
                                    (Markdown.OpenBlock.open_fence f.info f.fence_char f.fence_len f.indent
                                        List.empty)
                                    prepared),
                        Option.none =>
                            match Markdown.html_block_start first base
                                    (Bool.or maybe_lazy (Markdown.tip_is_paragraph state)) {
                                Option.some html_type =>
                                    Markdown.Started.started_line
                                        (Markdown.open_leaf
                                            (Markdown.OpenBlock.open_html html_type List.empty)
                                            prepared)
                                        c,
                                Option.none =>
                                    if Markdown.tip_is_paragraph state then
                                        match Markdown.try_setext first base {
                                            Option.some level =>
                                                Markdown.Started.started_consumed
                                                    (Markdown.to_heading level
                                                        (Markdown.tip_paragraph_lines state) state),
                                            Option.none =>
                                                Markdown.open_new_after_setext state first base c all_matched maybe_lazy
                                        }
                                    else Markdown.open_new_after_setext state first base c all_matched maybe_lazy
                            }
                    }
            }

#[partial]
def Markdown.open_new_after_setext
    (state : Markdown.BlockState) (first : Markdown.Cursor) (base : I64) (c : Markdown.Cursor)
    (all_matched : Bool) (maybe_lazy : Bool) : Markdown.Started :=
    if Markdown.is_thematic first base
    then
        Markdown.Started.started_consumed
            (Markdown.push_into raw_thematic_break
                (Markdown.close_list_tip (Markdown.close_paragraph_tip state)))
    else
        match Markdown.try_list_item first (Markdown.tip_is_paragraph state) base {
            Option.some ls =>
                Markdown.mark_opened
                    (Markdown.open_new
                        (Markdown.open_item_for ls (Markdown.open_list_for ls (Markdown.close_paragraph_tip state)))
                        ls.content all_matched false),
            Option.none =>
                if Bool.and (Bool.not maybe_lazy) (I64.lt 3i64 (I64.sub first.column base))
                then
                    Markdown.Started.started_line
                        (Markdown.open_leaf (Markdown.OpenBlock.open_indented_code List.empty)
                            (Markdown.close_list_tip (Markdown.close_paragraph_tip state)))
                        c
                else Markdown.Started.started_none state c false
        }

def Markdown.mark_opened (r : Markdown.Started) : Markdown.Started :=
    match r {
        Markdown.Started.started_consumed st => Markdown.Started.started_consumed st,
        Markdown.Started.started_opened st => Markdown.Started.started_opened st,
        Markdown.Started.started_line st c => Markdown.Started.started_line st c,
        Markdown.Started.started_none st c _ => Markdown.Started.started_none st c true
    }

// ─── Per-line driver ───

#[partial]
def Markdown.line_for_fence
    (state : Markdown.BlockState) (info : Option String) (fence_char : U8) (fence_len : I64)
    (indent : I64) (lines : List String) (c : Markdown.Cursor) : Markdown.BlockState :=
    if Markdown.is_closing_fence_at c fence_char fence_len
    then Markdown.close_tip state
    else
        let cleared : Markdown.Cursor := Markdown.Cursor.strip_up_to indent c in
        Markdown.replace_tip
            (Markdown.OpenBlock.open_fence info fence_char fence_len indent
                (List.cons (Markdown.Cursor.materialize cleared) lines))
            state

#[partial]
def Markdown.line_for_indented (state : Markdown.BlockState) (lines : List String) (c : Markdown.Cursor) : Markdown.BlockState :=
    if Markdown.Cursor.blank c
    then Markdown.replace_tip (Markdown.OpenBlock.open_indented_code (List.cons "" lines)) state
    else if I64.lt 3i64 (I64.sub (Markdown.Cursor.first_nonspace_column c) c.column)
    then
        let content : Markdown.Cursor := Markdown.Cursor.step_many 4i64 c in
        Markdown.replace_tip
            (Markdown.OpenBlock.open_indented_code (List.cons (Markdown.Cursor.materialize content) lines))
            state
    else Markdown.add_content (Markdown.close_tip state) c

/// An HTML block line: the content keeps the container's own indentation,
/// and types 1-5 close on their terminator line.
#[partial]
def Markdown.line_for_html
    (state : Markdown.BlockState) (html_type : I64) (lines : List String) (c : Markdown.Cursor)
    : Markdown.BlockState :=
    let line : String := Markdown.Cursor.materialize c in
    let next : Markdown.BlockState :=
        Markdown.replace_tip (Markdown.OpenBlock.open_html html_type (List.cons line lines)) state in
    if Markdown.html_block_ends html_type line
    then Markdown.close_tip next
    else next

def Markdown.append_paragraph_line (line : String) (state : Markdown.BlockState) : Markdown.BlockState :=
    match state.stack {
        List.empty => state,
        List.cons top rest =>
            match top {
                open_paragraph lines =>
                    Markdown.with_stack (List.cons (Markdown.OpenBlock.open_paragraph (List.cons line lines)) rest) state,
                _ => state
            }
    }

pub def Markdown.to_heading (level : I64) (lines : List String) (state : Markdown.BlockState) : Markdown.BlockState :=
    match state.stack {
        List.empty => state,
        List.cons _ rest =>
            Markdown.push_into (raw_heading level (List.reverse lines)) (Markdown.with_stack rest state)
    }

/// Fold a blank line into the innermost open list item.
#[partial]
def Markdown.mark_blank_stack (stack : List Markdown.OpenBlock) : List Markdown.OpenBlock :=
    match stack {
        List.empty => stack,
        List.cons top rest =>
            match top {
                open_item indent checked blocks _ between =>
                    List.cons
                        (Markdown.OpenBlock.open_item indent checked blocks true
                            (Bool.or between (Bool.not (List.is_empty blocks))))
                        rest,
                open_doc _ => stack,
                open_list _ _ _ _ => stack,
                _ => List.cons top (Markdown.mark_blank_stack rest)
            }
    }

#[partial]
def Markdown.mark_blank (state : Markdown.BlockState) : Markdown.BlockState :=
    Markdown.with_stack (Markdown.mark_blank_stack state.stack) state

/// A blank line: closes the open paragraph, keeps containers open, and marks
/// the innermost item.
#[partial]
def Markdown.blank_line (state : Markdown.BlockState) : Markdown.BlockState :=
    match state.stack {
        List.empty => state,
        List.cons top rest =>
            match top {
                open_paragraph _ => Markdown.mark_blank (Markdown.close_tip state),
                open_fence info fence_char fence_len indent lines =>
                    Markdown.replace_tip
                        (Markdown.OpenBlock.open_fence info fence_char fence_len indent (List.cons "" lines))
                        state,
                open_indented_code lines =>
                    Markdown.replace_tip (Markdown.OpenBlock.open_indented_code (List.cons "" lines)) state,
                open_html html_type lines =>
                    if I64.lt html_type 6i64
                    then Markdown.replace_tip (Markdown.OpenBlock.open_html html_type (List.cons "" lines)) state
                    else Markdown.mark_blank (Markdown.close_tip state),
                open_doc _ => state,
                _ => Markdown.mark_blank state
            }
    }

/// cmark's `add_text_to_container`: the line becomes content of the tip, or a
/// new paragraph when the tip is a container.
#[partial]
def Markdown.add_content (state : Markdown.BlockState) (c : Markdown.Cursor) : Markdown.BlockState :=
    if Markdown.Cursor.blank c
    then Markdown.blank_line state
    else
        match state.stack {
            List.empty => state,
            List.cons top rest =>
                match top {
                    open_fence info fence_char fence_len indent lines =>
                        Markdown.line_for_fence state info fence_char fence_len indent lines c,
                    open_indented_code lines => Markdown.line_for_indented state lines c,
                    open_html html_type lines => Markdown.line_for_html state html_type lines c,
                    open_paragraph lines =>
                        Markdown.append_paragraph_line
                            (Markdown.Cursor.materialize (Markdown.Cursor.skip_spaces c)) state,
                    _ =>
                        let first : Markdown.Cursor := Markdown.Cursor.skip_spaces c in
                        Markdown.open_leaf
                            (Markdown.OpenBlock.open_paragraph [Markdown.Cursor.materialize first])
                            state
                }
        }

#[partial]
def Markdown.incorporate_line (state : Markdown.BlockState) (line : String) : Markdown.BlockState :=
    let m : Markdown.MatchResult :=
        Markdown.match_containers state.stack (Markdown.Cursor.start line) in
    let all_matched : Bool := List.is_empty m.unmatched in
    let maybe_lazy : Bool := Markdown.tip_is_paragraph state in
    let closed : Markdown.BlockState := Markdown.close_unmatched state m.unmatched in
    if Markdown.tip_is_code_or_html closed
    then Markdown.add_content closed m.cursor
    else
        match Markdown.open_new closed m.cursor all_matched maybe_lazy {
            Markdown.Started.started_consumed consumed => consumed,
            Markdown.Started.started_opened opened => opened,
            Markdown.Started.started_line opened cursor => Markdown.add_content opened cursor,
            Markdown.Started.started_none opened_state opened_cursor opened_container =>
                if Bool.and (Bool.not opened_container)
                        (Bool.and (Bool.not all_matched)
                            (Bool.and (Bool.not (Markdown.Cursor.blank m.cursor)) maybe_lazy))
                then
                    let first : Markdown.Cursor := Markdown.Cursor.skip_spaces m.cursor in
                    Markdown.append_paragraph_line (Markdown.Cursor.materialize first) state
                else Markdown.add_content opened_state opened_cursor
        }

#[partial]
def Markdown.incorporate_lines (state : Markdown.BlockState) (lines : List String) : Markdown.BlockState :=
    match lines {
        List.empty => state,
        List.cons line rest => Markdown.incorporate_lines (Markdown.incorporate_line state line) rest
    }

/// Parse `lines` into a raw block list.
pub def Markdown.block_parse (opts : Markdown.Options) (lines : List String) : List Markdown.RawBlock :=
    let start : Markdown.BlockState :=
        Markdown.mk_state [Markdown.OpenBlock.open_doc List.empty] opts in
    Markdown.finish (Markdown.incorporate_lines start lines)
