/// Link syntax shared by inline links and link reference definitions:
/// bracket labels, destinations, titles, and label normalisation.
///
/// These return RAW text (backslash escapes and entities untouched); the
/// caller unescapes with `Markdown.unescape`, which keeps this module free of
/// a dependency on the inline pass.
use init::string {}
use parsec::core {is_empty}
use lib::scan {Markdown.Cursor, Markdown.char_width}
use lib::unicode {Markdown.case_fold}

// ─── Labels ───

/// A reference label at the cursor's `[`: the label's text and the cursor
/// after `]`. An unescaped `[` ends the attempt, as does a missing `]`.
pub def Markdown.parse_ref_label (c : Markdown.Cursor) : Option (Pair String Markdown.Cursor) :=
    match Markdown.Cursor.peek c {
        Option.some b =>
            if U8.beq b 91u8 then Markdown.ref_label_go (Markdown.Cursor.step c) List.empty 0i64 else Option.none,
        Option.none => Option.none
    }

#[partial]
def Markdown.ref_label_go (c : Markdown.Cursor) (acc : List String) (n : I64) : Option (Pair String Markdown.Cursor) :=
    if I64.lt 999i64 n
    then Option.none
    else
        match Markdown.Cursor.peek c {
            Option.none => Option.none,
            Option.some b =>
                if U8.beq b 93u8 then Option.some (Pair.pair (String.concat_list (List.reverse acc)) (Markdown.Cursor.step c))
                else if U8.beq b 91u8
                then Option.none
                else if U8.beq b 92u8
                then
                    let next : Markdown.Cursor := Markdown.Cursor.step c in
                    match Markdown.Cursor.peek next {
                        Option.some e =>
                            let w : I64 := Markdown.char_width c.text in
                            Markdown.ref_label_go (Markdown.Cursor.step next)
                                (List.cons (String.slice c.text 0 (I64.add 1i64 w)) acc) (I64.add n 1i64),
                        Option.none => Option.none
                    }
                else
                    let w : I64 := Markdown.char_width c.text in
                    Markdown.ref_label_go (Markdown.Cursor.step c) (List.cons (String.slice c.text 0 w) acc) (I64.add n 1i64)
        }

/// Trim, collapse internal whitespace runs to one space, and case-fold
/// (ASCII here; the generated Unicode table joins in the label folding pass).
#[partial]
def Markdown.normalize_label_go (s : String) (acc : List String) (space : Bool) : String :=
    if is_empty s
    then String.concat_list (List.reverse acc)
    else
        match String.get s 0 {
            Option.some b =>
                if Bool.or (U8.beq b 32u8) (Bool.or (U8.beq b 9u8) (U8.beq b 10u8))
                then Markdown.normalize_label_go (String.drop 1i64 s) (if space then acc else List.cons " " acc) true
                else
                    let w : I64 := Markdown.char_width s in
                    Markdown.normalize_label_go (String.drop w s)
                        (List.cons (Markdown.case_fold (String.slice s 0 w)) acc) false,
            Option.none => String.concat_list (List.reverse acc)
        }

pub def Markdown.normalize_label (s : String) : String :=
    Markdown.trim_label (Markdown.normalize_label_go s List.empty true)

/// Drop leading and trailing spaces left by the collapse.
#[partial]
def Markdown.trim_label (s : String) : String :=
    let len : I64 := String.length s in
    if I64.lt 0i64 len
    then
        match String.get s 0 {
            Option.some b =>
                if U8.beq b 32u8 then Markdown.trim_label (String.slice s 1i64 (I64.sub len 1i64)) else Markdown.trim_label_end s len,
            Option.none => s
        }
    else s

#[partial]
def Markdown.trim_label_end (s : String) (len : I64) : String :=
    if I64.lt 0i64 len
    then
        match String.get s (I64.sub len 1i64) {
            Option.some b =>
                if U8.beq b 32u8 then Markdown.trim_label_end (String.slice s 0 (I64.sub len 1i64)) (I64.sub len 1i64) else s,
            Option.none => s
        }
    else s

// ─── Destinations ───

/// Skip spaces and tabs, and at most one newline (cmark's `spnl`).
pub def Markdown.skip_spnl (c : Markdown.Cursor) : Markdown.Cursor :=
    let skipped : Markdown.Cursor := Markdown.Cursor.skip_spaces c in
    match Markdown.Cursor.peek skipped {
        Option.some b =>
            if U8.beq b 10u8
            then Markdown.Cursor.skip_spaces (Markdown.Cursor.step skipped)
            else skipped,
        Option.none => skipped
    }

/// A destination: `<...>` or a bare run with balanced parentheses.
pub def Markdown.parse_destination (c : Markdown.Cursor) : Option (Pair String Markdown.Cursor) :=
    let started : Markdown.Cursor := Markdown.skip_spnl c in
    match Markdown.Cursor.peek started {
        Option.none => Option.none,
        Option.some b =>
            if U8.beq b 60u8
            then Markdown.parse_pointy_destination (Markdown.Cursor.step started) List.empty
            else Markdown.parse_bare_destination started List.empty 0i64
    }

#[partial]
def Markdown.parse_pointy_destination (c : Markdown.Cursor) (acc : List String) : Option (Pair String Markdown.Cursor) :=
    match Markdown.Cursor.peek c {
        Option.none => Option.none,
        Option.some b =>
            if U8.beq b 62u8
            then
                if List.is_empty acc
                then Option.none
                else Option.some (Pair.pair (String.concat_list (List.reverse acc)) (Markdown.Cursor.step c))
            else if Bool.or (U8.beq b 60u8) (Bool.or (U8.beq b 10u8) (U8.beq b 13u8))
            then Option.none
            else Markdown.pointy_char c acc
    }

/// An escaped pair is kept verbatim so the caller can unescape it.
#[partial]
def Markdown.pointy_char (c : Markdown.Cursor) (acc : List String) : Option (Pair String Markdown.Cursor) :=
    match Markdown.Cursor.peek c {
        Option.some b =>
            if U8.beq b 92u8
            then
                let next : Markdown.Cursor := Markdown.Cursor.step c in
                let w : I64 := Markdown.char_width c.text in
                Markdown.parse_pointy_destination (Markdown.Cursor.step next)
                    (List.cons (String.slice c.text 0 (I64.add 1i64 w)) acc)
            else
                let w : I64 := Markdown.char_width c.text in
                Markdown.parse_pointy_destination (Markdown.Cursor.step c)
                    (List.cons (String.slice c.text 0 w) acc),
        Option.none => Option.none
    }

/// A bare destination: no spaces or control characters, balanced parens.
#[partial]
def Markdown.parse_bare_destination (c : Markdown.Cursor) (acc : List String) (depth : I64) : Option (Pair String Markdown.Cursor) :=
    match Markdown.Cursor.peek c {
        Option.none =>
            if List.is_empty acc
            then Option.none
            else Option.some (Pair.pair (String.concat_list (List.reverse acc)) c),
        Option.some b =>
            let w : I64 := Markdown.char_width c.text in
            if U8.lt b 32u8
            then (if List.is_empty acc then Option.none
                  else Option.some (Pair.pair (String.concat_list (List.reverse acc)) c))
            else if U8.beq b 32u8
            then (if List.is_empty acc then Option.none
                  else Option.some (Pair.pair (String.concat_list (List.reverse acc)) c))
            else if Bool.and (U8.beq b 40u8) (Bool.not (List.is_empty acc))
            then Markdown.parse_bare_destination (Markdown.Cursor.step c) (List.cons "(" acc) (I64.add depth 1i64)
            else if U8.beq b 41u8
            then (if I64.lt depth 1i64
                  then (if List.is_empty acc then Option.none
                        else Option.some (Pair.pair (String.concat_list (List.reverse acc)) c))
                  else Markdown.parse_bare_destination (Markdown.Cursor.step c) (List.cons ")" acc) (I64.sub depth 1i64))
            else Markdown.parse_bare_destination (Markdown.Cursor.step c) (List.cons (String.slice c.text 0 w) acc) depth
    }

// ─── Titles ───

pub def Markdown.parse_title (c : Markdown.Cursor) : Option (Pair String Markdown.Cursor) :=
    let started : Markdown.Cursor := Markdown.skip_spnl c in
    match Markdown.Cursor.peek started {
        Option.none => Option.none,
        Option.some b =>
            if U8.beq b 34u8 then Markdown.parse_quoted started 34u8 List.empty
            else if U8.beq b 39u8 then Markdown.parse_quoted started 39u8 List.empty
            else if U8.beq b 40u8 then Markdown.parse_quoted started 41u8 List.empty
            else Option.none
    }

/// A title delimited by `closing`; the opening delimiter has not been
/// consumed yet.
#[partial]
def Markdown.parse_quoted (c : Markdown.Cursor) (closing : U8) (acc : List String) : Option (Pair String Markdown.Cursor) :=
    let after_open : Markdown.Cursor := Markdown.Cursor.step c in
    Markdown.parse_quoted_go after_open closing acc 0i64

#[partial]
def Markdown.parse_quoted_go (c : Markdown.Cursor) (closing : U8) (acc : List String) (newlines : I64)
    : Option (Pair String Markdown.Cursor) :=
    match Markdown.Cursor.peek c {
        Option.none => Option.none,
        Option.some b =>
            if U8.beq b closing
            then Option.some (Pair.pair (String.concat_list (List.reverse acc)) (Markdown.Cursor.step c))
            else if U8.beq b 92u8
            then
                let next : Markdown.Cursor := Markdown.Cursor.step c in
                let w : I64 := Markdown.char_width c.text in
                Markdown.parse_quoted_go (Markdown.Cursor.step next) closing
                    (List.cons (String.slice c.text 0 (I64.add 1i64 w)) acc) newlines
            else if U8.beq b 10u8
            then
                if I64.lt 0i64 newlines
                then Option.none
                else Markdown.parse_quoted_go (Markdown.Cursor.step c) closing (List.cons "\n" acc) (I64.add newlines 1i64)
            else
                let w : I64 := Markdown.char_width c.text in
                Markdown.parse_quoted_go (Markdown.Cursor.step c) closing (List.cons (String.slice c.text 0 w) acc) 0i64
    }

// ─── Inline link tail ───

pub struct Markdown.LinkTail {
    dest : String,
    title : Option String,
    rest : Markdown.Cursor
}

def Markdown.mk_tail (dest : String) (title : Option String) (rest : Markdown.Cursor) : Markdown.LinkTail :=
    let t : Markdown.LinkTail := { dest := dest, title := title, rest := rest } in t

/// `(destination "title")`, with the title optional.
pub def Markdown.parse_link_tail (c : Markdown.Cursor) : Option Markdown.LinkTail :=
    match Markdown.Cursor.peek c {
        Option.some b =>
            if U8.beq b 40u8
            then
                match Markdown.parse_destination (Markdown.Cursor.step c) {
                    Option.none => Option.none,
                    Option.some d =>
                        match d {
                            Pair.pair dest after_dest =>
                                match Markdown.parse_title after_dest {
                                    Option.some t =>
                                        match t {
                                            Pair.pair title after_title =>
                                                match Markdown.Cursor.peek (Markdown.skip_spnl after_title) {
                                                    Option.some close =>
                                                        if U8.beq close 41u8
                                                        then Option.some
                                                            (Markdown.mk_tail dest (Option.some title)
                                                                (Markdown.Cursor.step (Markdown.skip_spnl after_title)))
                                                        else Option.none,
                                                    Option.none => Option.none
                                                }
                                        },
                                    Option.none =>
                                        match Markdown.Cursor.peek (Markdown.Cursor.skip_spaces after_dest) {
                                            Option.some close =>
                                                if U8.beq close 41u8
                                                then Option.some
                                                    (Markdown.mk_tail dest Option.none
                                                        (Markdown.Cursor.step (Markdown.Cursor.skip_spaces after_dest)))
                                                else Option.none,
                                            Option.none => Option.none
                                        }
                                }
                        }
                }
            else Option.none,
        Option.none => Option.none
    }
