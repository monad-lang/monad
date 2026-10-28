/// Scanning primitives shared by the block and inline passes.
///
/// The cost model is the reason this module exists. `String.get s i` is O(1)
/// only at `i == 0` on the compiled backend (every other index pays a
/// `strlen` for the bounds check), `String.slice` copies, and `String.drop`
/// walks to the cut. So every scan here works on a SUFFIX and peeks at index
/// 0; the only length-taking reads are on a slice of at most four bytes.
///
/// Codepoints are `U32`, not `I64`: `init` exposes no `U8.to_i64` or
/// `U32.to_i64`, so decoding stays in `U32` arithmetic and the Unicode tables
/// are generated over `U32`.
use init::string {}
use parsec::core {is_empty}
use parsec::combinators {utf8_char_width}

// ─── UTF-8 ───

/// The width in bytes of the character at the head of `s`, at least 1, so a
/// malformed byte can never stall a scan.
pub def Markdown.char_width (s : String) : I64 :=
    let w : I64 := utf8_char_width s in
    if I64.lt w 1i64 then 1i64 else w

/// A continuation byte's six payload bits, or 0 when the byte is not one.
def Markdown.cont_bits (head : String) (i : I64) : U32 :=
    match String.get head i {
        Option.some b =>
            if U8.lt b 128u8 then 0u32
            else if U8.lt b 192u8 then U32.sub (U8.to_u32 b) 128u32
            else 0u32,
        Option.none => 0u32
    }

/// Decode the codepoint at the head of `s`. Malformed input yields a
/// best-effort value rather than an error: CommonMark has no invalid input,
/// and every consumer only classifies.
pub def Markdown.codepoint_at (s : String) : Option U32 :=
    match String.get s 0 {
        Option.none => Option.none,
        Option.some b0 =>
            if U8.lt b0 128u8
            then Option.some (U8.to_u32 b0)
            else
                let w : I64 := Markdown.char_width s in
                let head : String := String.slice s 0 w in
                let b : U32 := U8.to_u32 b0 in
                let c1 : U32 := Markdown.cont_bits head 1i64 in
                if I64.beq w 1i64
                then Option.some b
                else if I64.beq w 2i64
                then Option.some (U32.or (U32.shl (U32.and b 31u32) 6u32) c1)
                else if I64.beq w 3i64
                then Option.some
                        (U32.or (U32.or (U32.shl (U32.and b 15u32) 12u32) (U32.shl c1 6u32))
                            (Markdown.cont_bits head 2i64))
                else Option.some
                        (U32.or
                            (U32.or (U32.shl (U32.and b 7u32) 18u32)
                                (U32.or (U32.shl c1 12u32) (U32.shl (Markdown.cont_bits head 2i64) 6u32)))
                            (Markdown.cont_bits head 3i64))
    }

/// The UTF-8 bytes of a codepoint. Surrogate halves, values past U+10FFFF
/// and negatives become U+FFFD, which is CommonMark's rule for numeric
/// character references and also the safe choice for a decoder.
pub def Markdown.utf8_of_codepoint (cp : I64) : String :=
    let too_high : Bool := I64.gt cp 1114111i64 in
    let surrogate : Bool := Bool.and (Bool.not (I64.lt cp 55296i64)) (Bool.not (I64.gt cp 57343i64)) in
    let c : U32 :=
        if Bool.or (Bool.or (I64.lt cp 1i64) too_high) surrogate
        then 65533u32
        else I64.to_u32 cp in
    let c1 : U32 := U32.or 128u32 (U32.and c 63u32) in
    let c2 : U32 := U32.or 128u32 (U32.and (U32.shr c 6u32) 63u32) in
    let c3 : U32 := U32.or 128u32 (U32.and (U32.shr c 12u32) 63u32) in
    if U32.lt c 128u32
    then String.from_list [U32.to_u8 c]
    else if U32.lt c 2048u32
    then String.from_list [U32.to_u8 (U32.or 192u32 (U32.shr c 6u32)), U32.to_u8 c1]
    else if U32.lt c 65536u32
    then String.from_list
            [ U32.to_u8 (U32.or 224u32 (U32.shr c 12u32)),
              U32.to_u8 c2,
              U32.to_u8 c1 ]
    else String.from_list
            [ U32.to_u8 (U32.or 240u32 (U32.shr c 18u32)),
              U32.to_u8 c3,
              U32.to_u8 c2,
              U32.to_u8 c1 ]

// ─── Lines ───

/// The byte length of the first line of `s`, excluding its terminating `\n`.
#[partial]
def Markdown.line_length_go (s : String) (n : I64) : I64 :=
    if is_empty s
    then n
    else
        match String.get s 0 {
            Option.some b =>
                if U8.beq b 10u8
                then n
                else
                    let w : I64 := Markdown.char_width s in
                    Markdown.line_length_go (String.drop w s) (I64.add n w),
            Option.none => n
    }

pub def Markdown.line_length (s : String) : I64 :=
    Markdown.line_length_go s 0i64

/// Drop one trailing `\r`, when the line had a CRLF ending.
def Markdown.strip_cr (line : String) (len : I64) : String :=
    if I64.lt 0i64 len
    then
        match String.get line (I64.sub len 1i64) {
            Option.some b => if U8.beq b 13u8 then String.slice line 0 (I64.sub len 1i64) else line,
            Option.none => line
        }
    else line

#[partial]
def Markdown.split_lines_go (s : String) (acc : List String) : List String :=
    if is_empty s
    then List.reverse acc
    else
        let len : I64 := Markdown.line_length s in
        let line : String := Markdown.strip_cr (String.slice s 0 len) len in
        let after : String := String.drop len s in
        let rest : String := if is_empty after then "" else String.drop 1i64 after in
        Markdown.split_lines_go rest (List.cons line acc)

/// Split a source string into lines: one leading BOM is dropped, CRLF is
/// accepted, and a final newline does not produce a trailing empty line.
/// Empty input has no lines.
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
