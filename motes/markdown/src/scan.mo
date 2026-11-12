/// Scanning primitives shared by the block and inline passes.
///
/// The cost model is the reason this module exists. `String.get s i` is O(1)
/// only at `i == 0` on the compiled backend (every other index pays a
/// `strlen` for the bounds check), `String.slice` copies, and `String.drop`
/// walks to the cut. So every scan here works on a SUFFIX and peeks at index
/// 0; the only length-taking reads are on a slice of at most four bytes.
///
/// Codepoint decoding and encoding live in the `unicode` mote
/// (`Unicode.codepoint_at`, `Unicode.utf8_of_codepoint`).
use init::string {}
use parsec::core {is_empty}
use parsec::combinators {utf8_char_width}

// ─── UTF-8 ───

/// The width in bytes of the character at the head of `s`, at least 1, so a
/// malformed byte can never stall a scan.
pub def Markdown.char_width (s : String) : I64 :=
    let w : I64 := utf8_char_width s in
    if I64.lt w 1i64 then 1i64 else w

// ─── Lines ───

/// The byte length of the first line of `s`, excluding its terminating `\n`.
#[partial]
def Markdown.line_length_go (s : String) (n : I64) : I64 :=
    if is_empty s
    then n
    else
        match String.get s 0 {
            Option.some b =>
                if Bool.or (U8.beq b 10u8) (U8.beq b 13u8)
                then n
                else
                    let w : I64 := Markdown.char_width s in
                    Markdown.line_length_go (String.drop w s) (I64.add n w),
            Option.none => n
        }

pub def Markdown.line_length (s : String) : I64 :=
    Markdown.line_length_go s 0i64

#[partial]
def Markdown.split_lines_go (s : String) (acc : List String) : List String :=
    if is_empty s
    then List.reverse acc
    else
        let len : I64 := Markdown.line_length s in
        let line : String := String.slice s 0 len in
        let after : String := String.drop len s in
        let rest : String :=
            if is_empty after
            then ""
            else if String.starts_with "\r\n" after
            then String.drop 2i64 after
            else String.drop 1i64 after in
        Markdown.split_lines_go rest (List.cons line acc)

/// Split a source string into lines: one leading BOM is dropped, `\n`, `\r`
/// and `\r\n` all end a line, and a final line ending does not produce a
/// trailing empty line. Empty input has no lines.
pub def Markdown.split_lines (src : String) : List String :=
    let s : String := if String.starts_with "\u{feff}" src then String.drop 3i64 src else src in
    Markdown.split_lines_go s List.empty

/// A line of only spaces and tabs.
#[partial]
pub def Markdown.is_blank (line : String) : Bool :=
    if is_empty line
    then true
    else
        match String.get line 0 {
            Option.some b =>
                if Bool.or (U8.beq b 32u8) (U8.beq b 9u8)
                then Markdown.is_blank (String.drop 1i64 line)
                else false,
            Option.none => true
        }

/// How many leading spaces a line has (tabs are not counted: use a `Cursor`
/// when tab stops matter).
#[partial]
def Markdown.leading_spaces_go (line : String) (n : I64) : I64 :=
    if is_empty line
    then n
    else
        match String.get line 0 {
            Option.some b =>
                if U8.beq b 32u8
                then Markdown.leading_spaces_go (String.drop 1i64 line) (I64.add n 1i64)
                else n,
            Option.none => n
        }

pub def Markdown.leading_spaces (line : String) : I64 :=
    Markdown.leading_spaces_go line 0i64

// ─── Cursor ───
//
// A suffix plus the virtual column, with the columns of a partially consumed
// tab held in `tabs`. Tab stops are relative to the CURRENT column, never to
// column 0, which is what the Tabs section of the spec pins.

pub struct Markdown.Cursor {
    text : String,
    column : I64,
    tabs : I64
}

def Markdown.mk_cursor (text : String) (column : I64) (tabs : I64) : Markdown.Cursor :=
    let c : Markdown.Cursor := { text := text, column := column, tabs := tabs } in c

pub def Markdown.Cursor.start (s : String) : Markdown.Cursor :=
    Markdown.mk_cursor s 0i64 0i64

/// The byte at the cursor's virtual position. A partially consumed tab reads
/// as a space.
pub def Markdown.Cursor.peek (c : Markdown.Cursor) : Option U8 :=
    if I64.lt 0i64 c.tabs
    then Option.some 32u8
    else String.get c.text 0

pub def Markdown.Cursor.at_end (c : Markdown.Cursor) : Bool :=
    Bool.and (I64.beq c.tabs 0i64) (is_empty c.text)

/// Consume one virtual column. A tab consumes to the next multiple of four.
pub def Markdown.Cursor.step (c : Markdown.Cursor) : Markdown.Cursor :=
    if I64.lt 0i64 c.tabs
    then Markdown.mk_cursor c.text (I64.add c.column 1i64) (I64.sub c.tabs 1i64)
    else
        match String.get c.text 0 {
            Option.none => c,
            Option.some b =>
                if U8.beq b 9u8
                then
                    let next : I64 := I64.add c.column (I64.sub 4i64 (I64.sub c.column (I64.mul 4i64 (I64.div c.column 4i64)))) in
                    Markdown.mk_cursor (String.drop 1i64 c.text) (I64.add c.column 1i64)
                        (I64.sub next (I64.add c.column 1i64))
                else Markdown.mk_cursor (String.drop (Markdown.char_width c.text) c.text)
                    (I64.add c.column 1i64) 0i64
        }

#[partial]
pub def Markdown.Cursor.step_many (n : I64) (c : Markdown.Cursor) : Markdown.Cursor :=
    if I64.lt n 1i64 then c else Markdown.Cursor.step_many (I64.sub n 1i64) (Markdown.Cursor.step c)

/// The cursor's text with any residual tab columns spelled as spaces.
pub def Markdown.Cursor.materialize (c : Markdown.Cursor) : String :=
    if I64.lt 0i64 c.tabs
    then String.concat (String.repeat " " c.tabs) c.text
    else c.text

/// Consume spaces and tabs. A tab's remaining columns read back as spaces
/// (see `peek`), so both spellings are tested here.
#[partial]
pub def Markdown.Cursor.skip_spaces (c : Markdown.Cursor) : Markdown.Cursor :=
    match Markdown.Cursor.peek c {
        Option.some b => if Bool.or (U8.beq b 32u8) (U8.beq b 9u8) then Markdown.Cursor.skip_spaces (Markdown.Cursor.step c) else c,
        Option.none => c
    }

/// Consume everything left on the line.
#[partial]
pub def Markdown.Cursor.skip_rest (c : Markdown.Cursor) : Markdown.Cursor :=
    if Markdown.Cursor.at_end c then c else Markdown.Cursor.skip_rest (Markdown.Cursor.step c)

/// The cursor's virtual column after skipping spaces and tabs.
pub def Markdown.Cursor.first_nonspace_column (c : Markdown.Cursor) : I64 :=
    let skipped : Markdown.Cursor := Markdown.Cursor.skip_spaces c in
    skipped.column

/// Whether the line has nothing but spaces and tabs from the cursor on.
pub def Markdown.Cursor.blank (c : Markdown.Cursor) : Bool :=
    Markdown.Cursor.at_end (Markdown.Cursor.skip_spaces c)

/// The first `n` elements of `xs`.
#[partial]
pub def Markdown.list_take (n : I64) (xs : List A) : List A :=
    if I64.lt n 1i64
    then List.empty
    else
        match xs {
            List.empty => List.empty,
            List.cons x rest => List.cons x (Markdown.list_take (I64.sub n 1i64) rest)
        }

/// `xs` without its first `n` elements.
#[partial]
pub def Markdown.list_drop (n : I64) (xs : List A) : List A :=
    if I64.lt n 1i64
    then xs
    else
        match xs {
            List.empty => List.empty,
            List.cons _ rest => Markdown.list_drop (I64.sub n 1i64) rest
        }
