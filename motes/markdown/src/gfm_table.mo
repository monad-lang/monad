/// GFM tables: cell splitting, delimiter rows and alignment.
///
/// Cells split on an unescaped `|` that is not inside a code span; the
/// backslash stays in the cell so the inline pass unescapes `\|` normally.
/// A table needs a pipe in the header or the delimiter row -- without one,
/// `foo` over `---` is a setext heading, not a one-column table.
use init::string {}
use parsec::core {is_empty}
use lib::scan {Markdown.char_width}
use lib::types {Markdown.Align}

open Markdown.Align {align_none, align_left, align_center, align_right}

/// The table's cells, with outer pipes removed and each cell trimmed.
pub def Markdown.split_cells (line : String) : List String :=
    //
    // `cells_go` accumulates reversed and `trim_cells` preserves order, so the
    // reversal happens once, here.
    let outer : List String := List.reverse (Markdown.cells_go line List.empty List.empty Option.none) in
    let trimmed : List String := Markdown.trim_cells outer List.empty in
    Markdown.drop_outer_pipes trimmed

#[partial]
def Markdown.trim_cells (cells : List String) (acc : List String) : List String :=
    match cells {
        List.empty => List.reverse acc,
        List.cons c rest => Markdown.trim_cells rest (List.cons (Markdown.trim_both c) acc)
    }

/// Trim spaces from both ends. One self-call per loop: the self-tail-call
/// rewrite emits one merge entry per call site, so a function with two
/// recursive calls in different branches produces an invalid PHI.
def Markdown.trim_both (s : String) : String :=
    Markdown.trim_trailing (Markdown.trim_leading s)

#[partial]
def Markdown.trim_leading (s : String) : String :=
    match String.get s 0 {
        Option.some b =>
            if U8.beq b 32u8
            then Markdown.trim_leading (String.drop 1i64 s)
            else s,
        Option.none => s
    }

#[partial]
def Markdown.trim_trailing (s : String) : String :=
    let len : I64 := String.length s in
    if I64.lt len 1i64
    then s
    else
        match String.get s (I64.sub len 1i64) {
            Option.some b =>
                if U8.beq b 32u8
                then Markdown.trim_trailing (String.slice s 0 (I64.sub len 1i64))
                else s,
            Option.none => s
        }

/// A line that begins or ends with an unescaped pipe has an empty outer cell.
#[partial]
def Markdown.drop_outer_pipes (cells : List String) : List String :=
    match cells {
        List.empty => cells,
        List.cons first rest =>
            let without_lead : List String :=
                if String.beq first "" then rest else cells in
            Markdown.drop_trailing_empty without_lead
    }

#[partial]
def Markdown.drop_trailing_empty (cells : List String) : List String :=
    List.reverse (Markdown.drop_leading_empty (List.reverse cells))

#[partial]
def Markdown.drop_leading_empty (cells : List String) : List String :=
    match cells {
        List.empty => cells,
        List.cons first rest => if String.beq first "" then rest else cells
    }

/// Wrap the current cell and start a new one.
#[partial]
def Markdown.finish_cell (current : List String) (cells : List String) : List String :=
    List.cons (String.concat_list (List.reverse current)) cells

/// Walk the line, splitting on unescaped pipes outside code spans. The
/// accumulator is reversed.
#[partial]
#[partial]
def Markdown.cells_go (s : String) (current : List String) (cells : List String) (code : Option I64)
    : List String :=
    if is_empty s
    then Markdown.finish_cell current cells
    else
        match String.get s 0 {
            Option.none => Markdown.finish_cell current cells,
            Option.some b =>
                if U8.beq b 92u8 then Markdown.cells_escape s current cells code
                else if U8.beq b 96u8 then Markdown.cells_code s current cells code
                else if U8.beq b 124u8 then Markdown.cells_pipe s current cells code
                else Markdown.cells_char s current cells code
        }

/// A backslash keeps the next character, so `\|` does not split.
#[partial]
def Markdown.cells_escape (s : String) (current : List String) (cells : List String) (code : Option I64)
    : List String :=
    let after : String := String.drop 1i64 s in
    match String.get after 0 {
        Option.some _ =>
            Markdown.cells_go (String.drop 1i64 after)
                (List.cons (String.slice after 0 1i64) (List.cons "\\" current)) cells code,
        Option.none => Markdown.finish_cell (List.cons "\\" current) cells
    }

/// A backtick run toggles code-span state so a pipe inside stays literal.
#[partial]
def Markdown.cells_code (s : String) (current : List String) (cells : List String) (code : Option I64)
    : List String :=
    match Markdown.take_run s 96u8 0i64 {
        Pair.pair n after_run =>
            Markdown.cells_go after_run (List.cons (String.slice s 0 n) current) cells
                (Markdown.next_code code n)
    }

def Markdown.next_code (code : Option I64) (n : I64) : Option I64 :=
    match code {
        Option.none => Option.some n,
        Option.some opened => if I64.beq opened n then Option.none else code
    }

#[partial]
def Markdown.cells_pipe (s : String) (current : List String) (cells : List String) (code : Option I64)
    : List String :=
    if Markdown.not_in_code code
    then
        Markdown.cells_go (String.drop 1i64 s) List.empty
            (List.cons (String.concat_list (List.reverse current)) cells) code
    else Markdown.cells_char s current cells code

#[partial]
def Markdown.cells_char (s : String) (current : List String) (cells : List String) (code : Option I64)
    : List String :=
    let w : I64 := Markdown.char_width s in
    Markdown.cells_go (String.drop w s) (List.cons (String.slice s 0 w) current) cells code

def Markdown.not_in_code (code : Option I64) : Bool :=
    match code {
        Option.none => true,
        Option.some _ => false
    }

#[partial]
def Markdown.take_run (s : String) (b : U8) (n : I64) : Pair I64 String :=
    match String.get s 0 {
        Option.some c =>
            if U8.beq c b
            then Markdown.take_run (String.drop 1i64 s) b (I64.add n 1i64)
            else Pair.pair n s,
        Option.none => Pair.pair n s
    }

/// A delimiter row: every cell is `:?-+:?` after trimming, at least one.
pub def Markdown.delimiter_row (line : String) : Option (List Markdown.Align) :=
    let cells : List String := Markdown.split_cells line in
    if List.is_empty cells
    then Option.none
    else Markdown.delim_cells cells List.empty

#[partial]
def Markdown.delim_cells (cells : List String) (acc : List Markdown.Align) : Option (List Markdown.Align) :=
    match cells {
        List.empty => Option.some (List.reverse acc),
        List.cons c rest =>
            match Markdown.delim_cell c {
                Option.some a => Markdown.delim_cells rest (List.cons a acc),
                Option.none => Option.none
            }
    }

/// `---`, `:---`, `---:`, `:---:`.
def Markdown.delim_cell (cell : String) : Option Markdown.Align :=
    let len : I64 := String.length cell in
    if I64.lt len 1i64
    then Option.none
    else
        let leading : Bool := Markdown.starts_char cell 58u8 in
        let trailing : Bool := Markdown.ends_char cell 58u8 in
        let core : String := Markdown.delim_core cell leading trailing in
        if Bool.and (Bool.not (String.beq core "")) (Markdown.all_dashes core)
        then
            if Bool.and leading trailing
            then Option.some align_center
            else if leading
            then Option.some align_left
            else if trailing
            then Option.some align_right
            else Option.some align_none
        else Option.none

def Markdown.delim_core (cell : String) (leading : Bool) (trailing : Bool) : String :=
    let len : I64 := String.length cell in
    let start : I64 := if leading then 1i64 else 0i64 in
    let count : I64 :=
        I64.sub len (I64.add start (if trailing then 1i64 else 0i64)) in
    if I64.lt count 0i64
    then ""
    else String.slice cell start count

def Markdown.starts_char (s : String) (b : U8) : Bool :=
    match String.get s 0 {
        Option.some c => U8.beq c b,
        Option.none => false
    }

def Markdown.ends_char (s : String) (b : U8) : Bool :=
    let len : I64 := String.length s in
    if I64.lt len 1i64
    then false
    else
        match String.get s (I64.sub len 1i64) {
            Option.some c => U8.beq c b,
            Option.none => false
        }

#[partial]
def Markdown.all_dashes (s : String) : Bool :=
    if is_empty s
    then true
    else
        match String.get s 0 {
            Option.some b =>
                if U8.beq b 45u8 then Markdown.all_dashes (String.drop 1i64 s) else false,
            Option.none => true
        }
