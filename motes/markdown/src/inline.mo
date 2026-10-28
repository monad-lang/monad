/// The inline pass (Phase 1 shell).
///
/// This phase handles textual content, backslash escapes, numeric and a few
/// named character references, and soft/hard line breaks. Code spans,
/// emphasis, links, images, autolinks and raw inline HTML arrive in Phase 3;
/// their entry points plug into `inline_loop`'s dispatch.
use init::string {}
use parsec::core {is_empty}
use lib::scan {Markdown.char_width, Markdown.utf8_of_codepoint}
use lib::types {Markdown.Inline}

open Markdown.Inline {inline_text, inline_soft_break, inline_hard_break}

struct Markdown.InlineBuild {
    pieces : List String,
    nodes : List Markdown.Inline
}

def Markdown.mk_build (pieces : List String) (nodes : List Markdown.Inline) : Markdown.InlineBuild :=
    let b : Markdown.InlineBuild := { pieces := pieces, nodes := nodes } in b

def Markdown.inline_start : Markdown.InlineBuild :=
    Markdown.mk_build List.empty List.empty

def Markdown.push_piece (s : String) (b : Markdown.InlineBuild) : Markdown.InlineBuild :=
    let next : Markdown.InlineBuild := { pieces := List.cons s b.pieces, nodes := b.nodes } in next

/// Turn the pending character pieces into one text node.
def Markdown.flush (b : Markdown.InlineBuild) : Markdown.InlineBuild :=
    match b.pieces {
        List.empty => b,
        List.cons _ _ =>
            let t : String := String.concat_list (List.reverse b.pieces) in
            Markdown.mk_build List.empty (List.cons (inline_text t) b.nodes)
    }

def Markdown.push_node (n : Markdown.Inline) (b : Markdown.InlineBuild) : Markdown.InlineBuild :=
    let flushed : Markdown.InlineBuild := Markdown.flush b in
    let next : Markdown.InlineBuild := { pieces := flushed.pieces, nodes := List.cons n flushed.nodes } in next

// ─── Escapes ───

/// ASCII punctuation, the only characters a backslash escapes.
def Markdown.is_ascii_punct (b : U8) : Bool :=
    Bool.or
        (Bool.and (U8.lt 32u8 b) (U8.lt b 48u8))
        (Bool.or
            (Bool.and (U8.lt 57u8 b) (U8.lt b 65u8))
            (Bool.or
                (Bool.and (U8.lt 90u8 b) (U8.lt b 97u8))
                (Bool.and (U8.lt 122u8 b) (U8.lt b 127u8))))

// ─── Character references ───

/// A short named table for Phase 1; Phase 3 replaces it with the generated
/// HTML5 table.
def Markdown.named_entity (name : String) : Option String :=
    if String.beq name "amp" then Option.some "&"
    else if String.beq name "lt" then Option.some "<"
    else if String.beq name "gt" then Option.some ">"
    else if String.beq name "quot" then Option.some "\""
    else if String.beq name "apos" then Option.some "'"
    else if String.beq name "nbsp" then Option.some "\u{a0}"
    else Option.none

/// Read up to `max` ASCII alphanumerics, returning (name, rest).
#[partial]
def Markdown.take_alnum (s : String) (acc : List String) (n : I64) : Pair String String :=
    if I64.lt 32i64 n
    then Pair.pair (String.concat_list (List.reverse acc)) s
    else
        match String.get s 0 {
            Option.some b =>
                let alnum : Bool :=
                    Bool.or
                        (Bool.and (U8.lt 47u8 b) (U8.lt b 58u8))
                        (Bool.or
                            (Bool.and (U8.lt 64u8 b) (U8.lt b 91u8))
                            (Bool.and (U8.lt 96u8 b) (U8.lt b 123u8))) in
                if alnum
                then Markdown.take_alnum (String.drop 1i64 s) (List.cons (String.slice s 0 1i64) acc) (I64.add n 1i64)
                else Pair.pair (String.concat_list (List.reverse acc)) s,
            Option.none => Pair.pair (String.concat_list (List.reverse acc)) s
        }

/// Read decimal digits, returning (value, rest). Values past 2^31 saturate:
/// no codepoint is that large, and the caller maps out-of-range to U+FFFD.
#[partial]
def Markdown.take_digits (s : String) (acc : I64) (n : I64) : Pair I64 String :=
    if I64.lt 9i64 n
    then Pair.pair acc s
    else
        match String.get s 0 {
            Option.some b =>
                if Bool.and (U8.lt 47u8 b) (U8.lt b 58u8)
                then
                    let d : I64 := Markdown.digit_value b in
                    Markdown.take_digits (String.drop 1i64 s)
                        (I64.add (I64.mul acc 10i64) d) (I64.add n 1i64)
                else Pair.pair acc s,
            Option.none => Pair.pair acc s
        }

def Markdown.digit_value (b : U8) : I64 :=
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

def Markdown.hex_value (b : U8) : I64 :=
    if U8.beq b 48u8 then 0i64
    else if U8.beq b 49u8 then 1i64
    else if U8.beq b 50u8 then 2i64
    else if U8.beq b 51u8 then 3i64
    else if U8.beq b 52u8 then 4i64
    else if U8.beq b 53u8 then 5i64
    else if U8.beq b 54u8 then 6i64
    else if U8.beq b 55u8 then 7i64
    else if U8.beq b 56u8 then 8i64
    else if U8.beq b 57u8 then 9i64
    else if U8.beq b 65u8 then 10i64
    else if U8.beq b 66u8 then 11i64
    else if U8.beq b 67u8 then 12i64
    else if U8.beq b 68u8 then 13i64
    else if U8.beq b 69u8 then 14i64
    else if U8.beq b 70u8 then 15i64
    else if U8.beq b 97u8 then 10i64
    else if U8.beq b 98u8 then 11i64
    else if U8.beq b 99u8 then 12i64
    else if U8.beq b 100u8 then 13i64
    else if U8.beq b 101u8 then 14i64
    else 15i64

#[partial]
def Markdown.take_hex (s : String) (acc : I64) (n : I64) : Pair I64 String :=
    if I64.lt 6i64 n
    then Pair.pair acc s
    else
        match String.get s 0 {
            Option.some b =>
                let is_hex : Bool :=
                    Bool.or
                        (Bool.and (U8.lt 47u8 b) (U8.lt b 58u8))
                        (Bool.or
                            (Bool.and (U8.lt 64u8 b) (U8.lt b 71u8))
                            (Bool.and (U8.lt 96u8 b) (U8.lt b 103u8))) in
                if is_hex
                then Markdown.take_hex (String.drop 1i64 s) (I64.add (I64.mul acc 16i64) (Markdown.hex_value b)) (I64.add n 1i64)
                else Pair.pair acc s,
            Option.none => Pair.pair acc s
        }

/// A character reference at `s` (which starts with `&`): the decoded text and
/// the remaining input, or `none` when this `&` is literal.
pub def Markdown.try_entity (s : String) : Option (Pair String String) :=
    let after : String := String.drop 1i64 s in
    match String.get after 0 {
        Option.none => Option.none,
        Option.some b =>
            if U8.beq b 35u8
            then Markdown.try_numeric (String.drop 1i64 after)
            else
                match Markdown.take_alnum after List.empty 0i64 {
                    Pair.pair name rest =>
                        match String.get rest 0 {
                            Option.some semi =>
                                if Bool.and (U8.beq semi 59u8) (Bool.not (String.beq name ""))
                                then
                                    match Markdown.named_entity name {
                                        Option.some text => Option.some (Pair.pair text (String.drop 1i64 rest)),
                                        Option.none => Option.none
                                    }
                                else Option.none,
                            Option.none => Option.none
                        }
                }
    }

def Markdown.try_numeric (s : String) : Option (Pair String String) :=
    match String.get s 0 {
        Option.none => Option.none,
        Option.some b =>
            if Bool.or (U8.beq b 120u8) (U8.beq b 88u8)
            then
                match Markdown.take_hex (String.drop 1i64 s) 0i64 0i64 {
                    Pair.pair v rest => Markdown.numeric_tail v rest
                }
            else
                match Markdown.take_digits s 0i64 0i64 {
                    Pair.pair v rest => Markdown.numeric_tail v rest
                }
    }

def Markdown.numeric_tail (v : I64) (rest : String) : Option (Pair String String) :=
    match String.get rest 0 {
        Option.some semi =>
            if U8.beq semi 59u8
            then Option.some (Pair.pair (Markdown.utf8_of_codepoint v) (String.drop 1i64 rest))
            else Option.none,
        Option.none => Option.none
    }

// ─── Breaks ───

#[partial]
def Markdown.drop_space_pieces (pieces : List String) (n : I64) : Pair I64 (List String) :=
    match pieces {
        List.empty => Pair.pair n pieces,
        List.cons p rest =>
            if String.beq p " "
            then Markdown.drop_space_pieces rest (I64.add n 1i64)
            else Pair.pair n pieces
    }

// ─── Driver ───

#[partial]
def Markdown.inline_loop (b : Markdown.InlineBuild) (s : String) : Markdown.InlineBuild :=
    if is_empty s
    then b
    else
        match String.get s 0 {
            Option.some byte =>
                if U8.beq byte 92u8
                then Markdown.scan_escape b s
                else if U8.beq byte 38u8
                then Markdown.scan_entity b s
                else if U8.beq byte 10u8
                then Markdown.scan_newline b s
                else
                    let w : I64 := Markdown.char_width s in
                    Markdown.inline_loop (Markdown.push_piece (String.slice s 0 w) b) (String.drop w s),
            Option.none => b
        }

#[partial]
def Markdown.scan_escape (b : Markdown.InlineBuild) (s : String) : Markdown.InlineBuild :=
    let after : String := String.drop 1i64 s in
    match String.get after 0 {
        Option.some byte =>
            if U8.beq byte 10u8
            then Markdown.inline_loop (Markdown.push_node inline_hard_break b) (String.drop 1i64 after)
            else if Markdown.is_ascii_punct byte
            then
                let w : I64 := Markdown.char_width after in
                Markdown.inline_loop (Markdown.push_piece (String.slice after 0 w) b) (String.drop w after)
            else Markdown.inline_loop (Markdown.push_piece "\\" b) after,
        Option.none => Markdown.push_piece "\\" b
    }

#[partial]
def Markdown.scan_entity (b : Markdown.InlineBuild) (s : String) : Markdown.InlineBuild :=
    match Markdown.try_entity s {
        Option.some found =>
            match found {
                Pair.pair text rest => Markdown.inline_loop (Markdown.push_piece text b) rest
            },
        Option.none => Markdown.inline_loop (Markdown.push_piece "&" b) (String.drop 1i64 s)
    }

#[partial]
def Markdown.scan_newline (b : Markdown.InlineBuild) (s : String) : Markdown.InlineBuild :=
    match Markdown.drop_space_pieces b.pieces 0i64 {
        Pair.pair spaces rest =>
            let cleared : Markdown.InlineBuild := Markdown.mk_build rest b.nodes in
            let brk : Markdown.Inline :=
                if I64.lt 1i64 spaces then inline_hard_break else inline_soft_break in
            Markdown.inline_loop (Markdown.push_node brk cleared) (String.drop 1i64 s)
    }

/// Parse inline source into a node list. Adjacent text is merged and empty
/// text nodes are dropped.
pub def Markdown.inline_parse (src : String) : List Markdown.Inline :=
    let done : Markdown.InlineBuild := Markdown.flush (Markdown.inline_loop Markdown.inline_start src) in
    List.reverse done.nodes

/// Unescape a one-line string the way a link destination or a code fence's
/// info string is unescaped: backslash escapes and character references, and
/// nothing else.
#[partial]
def Markdown.flatten_text (nodes : List Markdown.Inline) (acc : List String) : String :=
    match nodes {
        List.empty => String.concat_list (List.reverse acc),
        List.cons n rest =>
            match n {
                inline_text t => Markdown.flatten_text rest (List.cons t acc),
                inline_soft_break => Markdown.flatten_text rest (List.cons "\n" acc),
                _ => Markdown.flatten_text rest acc
            }
    }

pub def Markdown.unescape (s : String) : String :=
    Markdown.flatten_text (Markdown.inline_parse s) List.empty
