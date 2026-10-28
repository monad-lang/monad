/// GFM bare autolinks: `www.`, `http://`, `https://` and bare email
/// addresses at a word boundary.
///
/// The link text ends at whitespace or `<`, then trailing punctuation is
/// trimmed; closing parentheses are trimmed only while they are unbalanced,
/// which keeps a URL that ends in `(bar)` intact.
use init::string {}
use parsec::core {is_empty}
use lib::scan {Markdown.char_width}

/// The text up to whitespace or `<`.
#[partial]
def Markdown.linkish_go (s : String) (acc : List String) : Pair String String :=
    if is_empty s
    then Pair.pair (String.concat_list (List.reverse acc)) s
    else
        match String.get s 0 {
            Option.some b =>
                if Bool.or (U8.beq b 32u8)
                        (Bool.or (U8.beq b 9u8)
                            (Bool.or (U8.beq b 10u8) (U8.beq b 60u8)))
                then Pair.pair (String.concat_list (List.reverse acc)) s
                else
                    let w : I64 := Markdown.char_width s in
                    Markdown.linkish_go (String.drop w s) (List.cons (String.slice s 0 w) acc),
            Option.none => Pair.pair (String.concat_list (List.reverse acc)) s
        }

#[partial]
def Markdown.trim_end_punct (s : String) : String :=
    if String.beq s ""
    then s
    else
        let len : I64 := String.length s in
        match String.get s (I64.sub len 1i64) {
            Option.some b =>
                if Markdown.is_trailing_punct b
                then Markdown.trim_end_punct (String.slice s 0 (I64.sub len 1i64))
                else if U8.beq b 41u8
                then
                    if I64.lt (Markdown.count_char s 40u8) (Markdown.count_char s 41u8)
                    then Markdown.trim_end_punct (String.slice s 0 (I64.sub len 1i64))
                    else s
                else s,
            Option.none => s
        }

def Markdown.is_trailing_punct (b : U8) : Bool :=
    if U8.beq b 63u8 then true      // ?
    else if U8.beq b 33u8 then true  // !
    else if U8.beq b 46u8 then true  // .
    else if U8.beq b 44u8 then true  // ,
    else if U8.beq b 58u8 then true  // :
    else if U8.beq b 42u8 then true  // *
    else if U8.beq b 95u8 then true  // _
    else U8.beq b 126u8              // ~

#[partial]
def Markdown.count_char (s : String) (b : U8) : I64 :=
    Markdown.count_char_go s b 0i64

#[partial]
def Markdown.count_char_go (s : String) (b : U8) (n : I64) : I64 :=
    if is_empty s
    then n
    else
        match String.get s 0 {
            Option.some c =>
                let w : I64 := Markdown.char_width s in
                Markdown.count_char_go (String.drop w s) b (if U8.beq c b then I64.add n 1i64 else n),
            Option.none => n
        }

def Markdown.has_dot (s : String) : Bool :=
    String.contains s "."

/// A bare autolink: the destination, the text to show, and the remainder.
/// `www.` is the only form whose text differs from its destination (the
/// `http://` prefix is added), so the label is carried explicitly.
pub struct Markdown.Bare {
    dest : String,
    label : String,
    rest : String
}

def Markdown.mk_bare (dest : String) (label : String) (rest : String) : Markdown.Bare :=
    let b : Markdown.Bare := { dest := dest, label := label, rest := rest } in b

/// A bare URL or email at `s`: its destination and the remaining input.
pub def Markdown.scan_bare (s : String) : Option Markdown.Bare :=
    if String.starts_with "www." s
    then Markdown.bare_www s
    else if String.starts_with "https://" s
    then Markdown.bare_scheme s
    else if String.starts_with "http://" s
    then Markdown.bare_scheme s
    else Markdown.bare_email s

def Markdown.bare_www (s : String) : Option Markdown.Bare :=
    match Markdown.linkish_go s List.empty {
        Pair.pair text rest =>
            let trimmed : String := Markdown.trim_end_punct text in
            if Bool.and (Markdown.has_dot trimmed) (I64.gt (String.length trimmed) 4i64)
            then Option.some
                (Markdown.mk_bare (String.concat "http://" trimmed) trimmed
                    (Markdown.rewind trimmed text rest))
            else Option.none
    }

def Markdown.bare_scheme (s : String) : Option Markdown.Bare :=
    match Markdown.linkish_go s List.empty {
        Pair.pair text rest =>
            let trimmed : String := Markdown.trim_end_punct text in
            if I64.gt (String.length trimmed) 7i64
            then Option.some (Markdown.mk_bare trimmed trimmed (Markdown.rewind trimmed text rest))
            else Option.none
    }

/// The characters trimmed off the end of a URL are NOT part of the link, so
/// the remainder starts right after the link text.
def Markdown.rewind (trimmed : String) (untrimmed : String) (rest : String) : String :=
    String.drop (String.length trimmed) (String.concat untrimmed rest)

def Markdown.is_email_local (b : U8) : Bool :=
    Bool.or
        (Bool.and (U8.lt 47u8 b) (U8.lt b 58u8))
        (Bool.or
            (Bool.and (U8.lt 64u8 b) (U8.lt b 91u8))
            (Bool.or
                (Bool.and (U8.lt 96u8 b) (U8.lt b 123u8))
                (Bool.or (U8.beq b 46u8) (Bool.or (U8.beq b 95u8) (U8.beq b 43u8)))))

def Markdown.bare_email (s : String) : Option Markdown.Bare :=
    match Markdown.linkish_go s List.empty {
        Pair.pair text rest =>
            let trimmed : String := Markdown.trim_end_punct text in
            let at : String := String.from_list [64u8] in
            if String.contains trimmed at
            then
                if Markdown.looks_like_email trimmed
                then Option.some
                    (Markdown.mk_bare (String.concat "mailto:" trimmed) trimmed
                        (Markdown.rewind trimmed text rest))
                else Option.none
            else Option.none
    }

/// `local@domain` with a dot in the domain and no second `@`.
def Markdown.looks_like_email (s : String) : Bool :=
    let at : String := String.from_list [64u8] in
    if Bool.not (String.contains s at)
    then false
    else
        let parts : List String := Markdown.split_at_at s List.empty List.empty false in
        match parts {
            List.cons local rest =>
                match rest {
                    List.cons domain more =>
                        Bool.and (List.is_empty more)
                            (Bool.and (Bool.not (String.beq local ""))
                                (Bool.and (Bool.not (String.beq domain "")) (Markdown.has_dot domain))),
                    List.empty => false
                },
            List.empty => false
        }

/// Split on the FIRST `@`.
#[partial]
def Markdown.split_at_at (s : String) (current : List String) (parts : List String) (seen : Bool) : List String :=
    if is_empty s
    then List.reverse (List.cons (String.concat_list (List.reverse current)) parts)
    else
        match String.get s 0 {
            Option.some b =>
                if Bool.and (U8.beq b 64u8) (Bool.not seen)
                then Markdown.split_at_at (String.drop 1i64 s) List.empty
                        (List.cons (String.concat_list (List.reverse current)) parts) true
                else
                    let w : I64 := Markdown.char_width s in
                    Markdown.split_at_at (String.drop w s) (List.cons (String.slice s 0 w) current) parts seen,
            Option.none => List.reverse (List.cons (String.concat_list (List.reverse current)) parts)
        }
