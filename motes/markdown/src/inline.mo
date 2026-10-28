/// The inline pass (Phase 1 shell).
///
/// This phase handles textual content, backslash escapes, numeric and a few
/// named character references, and soft/hard line breaks. Code spans,
/// emphasis, links, images, autolinks and raw inline HTML arrive in Phase 3;
/// their entry points plug into `inline_loop`'s dispatch.
use init::string {}
use parsec::core {is_empty}
use lib::scan {
    Markdown.Cursor, Markdown.char_width, Markdown.codepoint_at, Markdown.list_drop,
    Markdown.list_take, Markdown.utf8_of_codepoint,
}
use lib::entities {Markdown.entity_lookup}
use lib::gfm_autolink {Markdown.Bare, Markdown.scan_bare}
use lib::unicode {Markdown.is_unicode_punctuation, Markdown.is_unicode_whitespace}
use lib::link_syntax {
    Markdown.is_ascii_punct,
    Markdown.LinkTail, Markdown.normalize_label, Markdown.parse_link_tail,
    Markdown.parse_ref_label,
}
use lib::inline_html {
    Markdown.scan_email_autolink, Markdown.scan_html_tag, Markdown.scan_uri_autolink,
}
use lib::refs {Markdown.lookup_ref}
use lib::types {Markdown.Inline, Markdown.LinkRef}
use lib::options {Markdown.Options, Markdown.default_options}

open Markdown.Inline {
    inline_text, inline_soft_break, inline_hard_break, inline_code,
    inline_link, inline_image,
}

/// An open delimiter run: its character, how many remain, its original
/// length (the rule of three), whether it may open, and the node count
/// BEFORE its own text node was pushed -- which is what makes the content of
/// a later match computable from `len`.
struct Markdown.DelimRec {
    ch : U8,
    count : I64,
    orig : I64,
    can_open : Bool,
    can_close : Bool,
    outer_len : I64
}

pub def Markdown.mk_delim_rec (ch : U8) (count : I64) (orig : I64) (can_open : Bool) (can_close : Bool)
    (outer_len : I64) : Markdown.DelimRec :=
    let d : Markdown.DelimRec :=
        { ch := ch, count := count, orig := orig, can_open := can_open, can_close := can_close,
          outer_len := outer_len } in d

struct Markdown.InlineBuild {
    pieces : List String,
    nodes : List Markdown.Inline,
    refs : List Markdown.LinkRef,
    len : I64,
    delims : List Markdown.DelimRec,
    prev : Option U32,
    opts : Markdown.Options
}

def Markdown.mk_build
    (pieces : List String) (nodes : List Markdown.Inline) (refs : List Markdown.LinkRef)
    (len : I64) (delims : List Markdown.DelimRec) (prev : Option U32) (opts : Markdown.Options)
    : Markdown.InlineBuild :=
    let b : Markdown.InlineBuild :=
        { pieces := pieces, nodes := nodes, refs := refs, len := len, delims := delims,
          prev := prev, opts := opts } in b

def Markdown.inline_start (opts : Markdown.Options) (refs : List Markdown.LinkRef) : Markdown.InlineBuild :=
    Markdown.mk_build List.empty List.empty refs 0i64 List.empty Option.none opts

def Markdown.push_piece (s : String) (b : Markdown.InlineBuild) : Markdown.InlineBuild :=
    let next : Markdown.InlineBuild := { b with pieces := List.cons s b.pieces } in next

/// Turn the pending character pieces into one text node.
def Markdown.flush (b : Markdown.InlineBuild) : Markdown.InlineBuild :=
    match b.pieces {
        List.empty => b,
        List.cons _ _ =>
            let t : String := String.concat_list (List.reverse b.pieces) in
            Markdown.mk_build List.empty (List.cons (inline_text t) b.nodes) b.refs
                (I64.add b.len 1i64) b.delims b.prev b.opts
    }

def Markdown.push_node (n : Markdown.Inline) (b : Markdown.InlineBuild) : Markdown.InlineBuild :=
    let flushed : Markdown.InlineBuild := Markdown.flush b in
    let next : Markdown.InlineBuild :=
        { flushed with nodes := List.cons n flushed.nodes, len := I64.add flushed.len 1i64 } in next

// ─── Escapes ───

// ─── Character references ───



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
    if I64.lt 6i64 n
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
    if I64.lt 5i64 n
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
                                    match Markdown.entity_lookup name {
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
                let after : String := String.drop 1i64 s in
                match Markdown.take_hex after 0i64 0i64 {
                    Pair.pair v rest =>
                        if String.beq rest after then Option.none else Markdown.numeric_tail v rest
                }
            else
                match Markdown.take_digits s 0i64 0i64 {
                    Pair.pair v rest =>
                        if String.beq rest s then Option.none else Markdown.numeric_tail v rest
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

// ─── Code spans ───

/// Count a backtick run at the head of `s`; returns the count and the rest.
#[partial]
def Markdown.count_backticks (s : String) (n : I64) : Pair I64 String :=
    match String.get s 0 {
        Option.some b =>
            if U8.beq b 96u8
            then Markdown.count_backticks (String.drop 1i64 s) (I64.add n 1i64)
            else Pair.pair n s,
        Option.none => Pair.pair n s
    }

/// Search `text` for a run of exactly `n` backticks. Returns the content
/// before it and the remainder after it.
#[partial]
def Markdown.find_code_close (text : String) (rest : String) (pos : I64) (n : I64)
    : Option (Pair String String) :=
    if is_empty rest
    then Option.none
    else
        match String.get rest 0 {
            Option.some b =>
                if U8.beq b 96u8
                then
                    match Markdown.count_backticks rest 0i64 {
                        Pair.pair k after =>
                            if I64.beq k n
                            then Option.some (Pair.pair (String.slice text 0 pos) (String.drop (I64.add pos k) text))
                            else Markdown.find_code_close text after (I64.add pos k) n
                    }
                else
                    let w : I64 := Markdown.char_width rest in
                    Markdown.find_code_close text (String.drop w rest) (I64.add pos w) n,
            Option.none => Option.none
        }

/// Line endings become spaces; one leading and one trailing space are
/// stripped when both are present and the content is not all spaces.
def Markdown.normalize_code (content : String) : String :=
    let spaced : String := Markdown.newlines_to_spaces content List.empty in
    let len : I64 := String.length spaced in
    let first_space : Bool :=
        match String.get spaced 0 {
            Option.some b => U8.beq b 32u8,
            Option.none => false
        } in
    let last_space : Bool :=
        if I64.lt 0i64 len
        then
            match String.get spaced (I64.sub len 1i64) {
                Option.some b => U8.beq b 32u8,
                Option.none => false
            }
        else false in
    if Bool.and first_space last_space
    then
        let inner : String := String.slice spaced 1i64 (I64.sub len 2i64) in
        if Markdown.all_spaces inner
        then spaced
        else inner
    else spaced

#[partial]
def Markdown.newlines_to_spaces (s : String) (acc : List String) : String :=
    if is_empty s
    then String.concat_list (List.reverse acc)
    else
        match String.get s 0 {
            Option.some b =>
                if U8.beq b 10u8
                then Markdown.newlines_to_spaces (String.drop 1i64 s) (List.cons " " acc)
                else
                    let w : I64 := Markdown.char_width s in
                    Markdown.newlines_to_spaces (String.drop w s) (List.cons (String.slice s 0 w) acc),
            Option.none => String.concat_list (List.reverse acc)
        }

#[partial]
def Markdown.all_spaces (s : String) : Bool :=
    if is_empty s
    then true
    else
        match String.get s 0 {
            Option.some b =>
                if U8.beq b 32u8 then Markdown.all_spaces (String.drop 1i64 s) else false,
            Option.none => true
        }

#[partial]
def Markdown.scan_code (b : Markdown.InlineBuild) (s : String) : Markdown.InlineBuild :=
    match Markdown.count_backticks s 0i64 {
        Pair.pair n rest =>
            match Markdown.find_code_close rest rest 0i64 n {
                Option.some found =>
                    match found {
                        Pair.pair content after =>
                            Markdown.inline_loop
                                (Markdown.prev_of s after
                                    (Markdown.push_node (inline_code (Markdown.normalize_code content)) b))
                                after
                    },
                Option.none =>
                    Markdown.inline_loop
                        (Markdown.push_piece (String.slice s 0 n) b)
                        (String.drop n s)
            }
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
                else if U8.beq byte 96u8
                then Markdown.scan_code b s
                else if U8.beq byte 91u8
                then Markdown.scan_bracket b s false
                else if U8.beq byte 33u8
                then Markdown.scan_bang b s
                else if U8.beq byte 60u8
                then Markdown.scan_lt b s
                else if Bool.or (U8.beq byte 42u8) (U8.beq byte 95u8)
                then Markdown.scan_delim b s byte
                else if Bool.and (U8.beq byte 126u8) b.opts.gfm_strikethrough
                then Markdown.scan_strike b s
                else if Bool.and b.opts.gfm_autolinks (Markdown.bare_start b.prev byte)
                then Markdown.scan_autolink b s
                else
                    let w : I64 := Markdown.char_width s in
                    let piece : String := String.slice s 0 w in
                    let b2 : Markdown.InlineBuild := { b with prev := Markdown.codepoint_at piece } in
                    Markdown.inline_loop (Markdown.push_piece piece b2) (String.drop w s),
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
                Pair.pair text rest =>
                    Markdown.inline_loop
                        (Markdown.prev_of s rest (Markdown.push_piece text b)) rest
            },
        Option.none => Markdown.inline_loop (Markdown.push_piece "&" b) (String.drop 1i64 s)
    }

#[partial]
def Markdown.scan_newline (b : Markdown.InlineBuild) (s : String) : Markdown.InlineBuild :=
    match Markdown.drop_space_pieces b.pieces 0i64 {
        Pair.pair spaces rest =>
            let cleared : Markdown.InlineBuild :=
                Markdown.mk_build rest b.nodes b.refs b.len b.delims (Option.some 10u32) b.opts in
            let brk : Markdown.Inline :=
                if I64.lt 1i64 spaces then inline_hard_break else inline_soft_break in
            Markdown.inline_loop (Markdown.push_node brk cleared) (String.drop 1i64 s)
    }

/// Parse inline source into a node list. Adjacent text is merged and empty
/// text nodes are dropped.
#[partial]
pub def Markdown.inline_parse_opts
    (opts : Markdown.Options) (refs : List Markdown.LinkRef) (src : String) : List Markdown.Inline :=
    let done : Markdown.InlineBuild :=
        Markdown.flush (Markdown.inline_loop (Markdown.inline_start opts refs) src) in
    List.reverse done.nodes

/// Resolve backslash escapes and character references, and nothing else: the
/// rule for a link destination, a title, or a code fence's info string.
/// Reference LABELS are deliberately not unescaped (`[foo\!]` does not match
/// `[foo!]`), so they never pass through here.
#[partial]
pub def Markdown.unescape (s : String) : String :=
    Markdown.unescape_go s List.empty

#[partial]
def Markdown.unescape_go (s : String) (acc : List String) : String :=
    if is_empty s
    then String.concat_list (List.reverse acc)
    else
        match String.get s 0 {
            Option.none => String.concat_list (List.reverse acc),
            Option.some b =>
                if U8.beq b 92u8
                then
                    let after : String := String.drop 1i64 s in
                    match String.get after 0 {
                        Option.some p =>
                            if Markdown.is_ascii_punct p
                            then Markdown.unescape_go (String.drop 1i64 after) (List.cons (String.slice after 0 1i64) acc)
                            else Markdown.unescape_go after (List.cons "\\" acc),
                        Option.none => String.concat_list (List.reverse (List.cons "\\" acc))
                    }
                else if U8.beq b 38u8
                then
                    match Markdown.try_entity s {
                        Option.some found =>
                            match found {
                                Pair.pair text rest => Markdown.unescape_go rest (List.cons text acc)
                            },
                        Option.none => Markdown.unescape_go (String.drop 1i64 s) (List.cons "&" acc)
                    }
                else
                    let w : I64 := Markdown.char_width s in
                    Markdown.unescape_go (String.drop w s) (List.cons (String.slice s 0 w) acc)
        }

/// A bare autolink may start here only at a word boundary.
pub def Markdown.bare_start (prev : Option U32) (b : U8) : Bool :=
    let at_boundary : Bool :=
        match prev {
            Option.none => true,
            Option.some cp =>
                Bool.not
                    (Bool.or (Bool.and (U32.lt 47u32 cp) (U32.lt cp 58u32))
                        (Bool.or (Bool.and (U32.lt 64u32 cp) (U32.lt cp 91u32))
                            (Bool.or (Bool.and (U32.lt 96u32 cp) (U32.lt cp 123u32))
                                (U32.beq cp 95u32))))
        } in
    Bool.and at_boundary
        (Bool.or (Markdown.is_alpha_byte b) (U8.beq b 104u8))

def Markdown.is_alpha_byte (b : U8) : Bool :=
    Bool.or (Bool.and (U8.lt 64u8 b) (U8.lt b 91u8)) (Bool.and (U8.lt 96u8 b) (U8.lt b 123u8))

/// `www.`, `http(s)://` or a bare email, as a link whose text is the URL.
#[partial]
def Markdown.scan_autolink (b : Markdown.InlineBuild) (s : String) : Markdown.InlineBuild :=
    match Markdown.scan_bare s {
        Option.some link => Markdown.bare_node link s b,
        Option.none =>
            let w : I64 := Markdown.char_width s in
            let piece : String := String.slice s 0 w in
            let b2 : Markdown.InlineBuild := { b with prev := Markdown.codepoint_at piece } in
            Markdown.inline_loop (Markdown.push_piece piece b2) (String.drop w s)
    }

#[partial]
def Markdown.bare_node (link : Markdown.Bare) (s : String) (b : Markdown.InlineBuild) : Markdown.InlineBuild :=
    let node : Markdown.Inline :=
        inline_link link.dest Option.none (List.cons (inline_text link.label) List.empty) in
    Markdown.inline_loop
        (Markdown.prev_of s link.rest (Markdown.push_node node b)) link.rest

// ─── Links and images ───

/// `![` opens an image; a lone `!` is text.
#[partial]
def Markdown.scan_bang (b : Markdown.InlineBuild) (s : String) : Markdown.InlineBuild :=
    let next : String := String.drop 1i64 s in
    match String.get next 0 {
        Option.some b2 =>
            if U8.beq b2 91u8
            then Markdown.scan_bracket b s true
            else Markdown.inline_loop (Markdown.push_piece "!" b) next,
        Option.none => Markdown.push_piece "!" b
    }


/// Find the `]` matching an already-consumed `[`. Skips escapes and code
/// spans; nested brackets increase the depth. Returns the label text and the
/// text after the `]`.
#[partial]
def Markdown.find_bracket_close (text : String) (rest : String) (pos : I64) (depth : I64)
    : Option (Pair String String) :=
    if is_empty rest
    then Option.none
    else
        match String.get rest 0 {
            Option.none => Option.none,
            Option.some b =>
                if U8.beq b 92u8
                then
                    let next : String := String.drop 1i64 rest in
                    let w : I64 := Markdown.char_width next in
                    Markdown.find_bracket_close text (String.drop w next) (I64.add pos (I64.add 1i64 w)) depth
                else if U8.beq b 96u8
                then
                    match Markdown.count_backticks rest 0i64 {
                        Pair.pair n after_run =>
                            match Markdown.find_code_close after_run after_run 0i64 n {
                                Option.some found =>
                                    match found {
                                        Pair.pair _ after_code =>
                                            let consumed : I64 := I64.sub (I64.sub (String.length rest) (String.length after_code)) 0i64 in
                                            Markdown.find_bracket_close text after_code (I64.add pos consumed) depth
                                    },
                                Option.none =>
                                    Markdown.find_bracket_close text (String.drop n rest) (I64.add pos n) depth
                            }
                    }
                else if U8.beq b 60u8
                then
                    match Markdown.skip_inline_angle rest {
                        Option.some after_angle =>
                            let consumed : I64 := I64.sub (String.length rest) (String.length after_angle) in
                            Markdown.find_bracket_close text after_angle (I64.add pos consumed) depth,
                        Option.none =>
                            Markdown.find_bracket_close text (String.drop 1i64 rest) (I64.add pos 1i64) depth
                    }
                else if U8.beq b 91u8
                then Markdown.find_bracket_close text (String.drop 1i64 rest) (I64.add pos 1i64) (I64.add depth 1i64)
                else if U8.beq b 93u8
                then
                    if I64.beq depth 1i64
                    then Option.some (Pair.pair (String.slice text 0 pos) (String.drop 1i64 rest))
                    else Markdown.find_bracket_close text (String.drop 1i64 rest) (I64.add pos 1i64) (I64.sub depth 1i64)
                else
                    let w : I64 := Markdown.char_width rest in
                    Markdown.find_bracket_close text (String.drop w rest) (I64.add pos w) depth
        }

#[partial]
def Markdown.has_link (nodes : List Markdown.Inline) : Bool :=
    match nodes {
        List.empty => false,
        List.cons n rest =>
            Bool.or
                (match n {
                    inline_link _ _ _ => true,
                    Markdown.Inline.inline_emphasis children => Markdown.has_link children,
                    Markdown.Inline.inline_strong children => Markdown.has_link children,
                    Markdown.Inline.inline_strikethrough children => Markdown.has_link children,
                    _ => false
                })
                (Markdown.has_link rest)
    }

/// A `<`-construct inside a label (autolink or raw HTML) is skipped whole; a
/// `]` inside it must not close the label.
pub def Markdown.skip_inline_angle (s : String) : Option String :=
    match Markdown.scan_uri_autolink s {
        Option.some found =>
            match found {
                Pair.pair _ rest => Option.some rest
            },
        Option.none =>
            match Markdown.scan_email_autolink s {
                Option.some found =>
                    match found {
                        Pair.pair _ rest => Option.some rest
                    },
                Option.none =>
                    match Markdown.scan_html_tag s {
                        Option.some found =>
                            match found {
                                Pair.pair _ rest => Option.some rest
                            },
                        Option.none => Option.none
                    }
            }
    }

/// Flatten nodes to plain text: what an image's `alt` is.
#[partial]
pub def Markdown.flatten_alt (nodes : List Markdown.Inline) (acc : List String) : String :=
    match nodes {
        List.empty => String.concat_list (List.reverse acc),
        List.cons n rest =>
            match n {
                inline_text t => Markdown.flatten_alt rest (List.cons t acc),
                inline_code t => Markdown.flatten_alt rest (List.cons t acc),
                inline_soft_break => Markdown.flatten_alt rest (List.cons "\n" acc),
                inline_hard_break => Markdown.flatten_alt rest (List.cons "\n" acc),
                inline_emphasis children => Markdown.flatten_alt rest
                    (List.cons (Markdown.flatten_alt children List.empty) acc),
                inline_strong children => Markdown.flatten_alt rest
                    (List.cons (Markdown.flatten_alt children List.empty) acc),
                inline_strikethrough children => Markdown.flatten_alt rest
                    (List.cons (Markdown.flatten_alt children List.empty) acc),
                inline_link _ _ children => Markdown.flatten_alt rest
                    (List.cons (Markdown.flatten_alt children List.empty) acc),
                inline_image _ _ alt => Markdown.flatten_alt rest (List.cons alt acc),
                inline_autolink _ label => Markdown.flatten_alt rest (List.cons label acc),
                inline_html literal => Markdown.flatten_alt rest (List.cons literal acc)
            }
    }

/// A resolution: destination, title and the text after the construct.
struct Markdown.Resolved {
    dest : String,
    title : Option String,
    rest : String
}

def Markdown.mk_resolved (dest : String) (title : Option String) (rest : String) : Markdown.Resolved :=
    let r : Markdown.Resolved := { dest := dest, title := title, rest := rest } in r

/// An inline tail, a full/collapsed reference, or a shortcut reference.
#[partial]
pub def Markdown.resolve_link (label : String) (after : String) (refs : List Markdown.LinkRef)
    : Option Markdown.Resolved :=
    let normal : String := Markdown.normalize_label label in
    match Markdown.Cursor.peek (Markdown.Cursor.start after) {
        Option.some b =>
            if U8.beq b 40u8
            then
                match Markdown.parse_link_tail (Markdown.Cursor.start after) {
                    Option.some tail => Markdown.resolved_tail tail,
                    Option.none => Markdown.resolve_by_label normal after refs
                }
            else if U8.beq b 91u8
            then
                if String.starts_with "[]" after
                then Markdown.resolve_by_label normal (String.drop 2i64 after) refs
                else
                    match Markdown.Cursor.peek (Markdown.Cursor.step (Markdown.Cursor.start after)) {
                        Option.some inner =>
                            if U8.beq inner 93u8
                            then Markdown.resolve_by_label normal (String.drop 2i64 after) refs
                            else
                                match Markdown.parse_ref_label (Markdown.Cursor.start after) {
                                    Option.some labelled =>
                                        match labelled {
                                            Pair.pair ref_label after_ref =>
                                                Markdown.resolve_by_label
                                                    (Markdown.normalize_label ref_label)
                                                    after_ref.text refs
                                        },
                                    Option.none => Option.none
                                },
                        Option.none => Option.none
                    }
            else Markdown.resolve_by_label normal after refs,
        Option.none => Markdown.resolve_by_label normal after refs
    }

#[partial]
def Markdown.resolve_by_label (label : String) (rest : String) (refs : List Markdown.LinkRef)
    : Option Markdown.Resolved :=
    if String.beq label ""
    then Option.none
    else
        match Markdown.lookup_ref label refs {
            Option.some r => Option.some (Markdown.mk_resolved (Markdown.unescape r.dest) (Markdown.unescape_title r.title) rest),
            Option.none => Option.none
        }

#[partial]
def Markdown.unescape_title (title : Option String) : Option String :=
    match title {
        Option.some t => Option.some (Markdown.unescape t),
        Option.none => Option.none
    }

#[partial]
def Markdown.resolved_tail (tail : Markdown.LinkTail) : Option Markdown.Resolved :=
    Option.some
        (Markdown.mk_resolved (Markdown.unescape tail.dest) (Markdown.unescape_title tail.title) tail.rest.text)

/// Emit a link or an image, or fall back to a literal opener. A link whose
/// label already contains a link is not formed (links cannot nest).
#[partial]
def Markdown.emit_link (b : Markdown.InlineBuild) (image : Bool) (label : String) (resolved : Markdown.Resolved)
    (whole : String) : Markdown.InlineBuild :=
    // `max_depth` doubles as the inline nesting budget: each link or image
    // label parses against one less, and at zero the construct stays text.
    let base_opts : Markdown.Options := b.opts in
    let inner_opts : Markdown.Options :=
        { base_opts with max_depth := I64.sub b.opts.max_depth 1i64 } in
    let children : List Markdown.Inline := Markdown.inline_parse_opts inner_opts b.refs label in
    let over_depth : Bool := I64.lt b.opts.max_depth 1i64 in
    if Bool.or over_depth (Bool.and (Bool.not image) (Markdown.has_link children))
    then
        // Links cannot nest: the outer opener is literal and the label is
        // rescanned, which is what lets the inner one form.
        Markdown.inline_loop (Markdown.push_piece (if image then "![" else "[") b)
            (String.drop (if image then 2i64 else 1i64) whole)
    else
        let node : Markdown.Inline :=
            if image
            then inline_image resolved.dest resolved.title (Markdown.flatten_alt children List.empty)
            else inline_link resolved.dest resolved.title children in
        Markdown.inline_loop
            (Markdown.prev_of whole resolved.rest (Markdown.push_node node b)) resolved.rest

#[partial]
def Markdown.scan_bracket (b : Markdown.InlineBuild) (s : String) (image : Bool) : Markdown.InlineBuild :=
    let opener : I64 := if image then 2i64 else 1i64 in
    let inner : String := String.drop opener s in
    if I64.lt b.opts.max_depth 1i64
    then
        // The nesting budget is spent: the opener is text, and NOT looking
        // for its `]` is what keeps deep nesting linear instead of quadratic.
        Markdown.inline_loop (Markdown.push_piece (String.slice s 0 opener) b) inner
    else
    match Markdown.find_bracket_close inner inner 0i64 1i64 {
        Option.none =>
            // No `]` closes this label. When the remainder holds no `]` at
            // all, no later bracket can close either: taking the rest as text
            // once keeps pathological input linear instead of rescanning the
            // tail for every `[`.
            if String.contains inner "]"
            then Markdown.inline_loop (Markdown.push_piece (String.slice s 0 opener) b) inner
            else Markdown.inline_loop (Markdown.push_piece (String.concat (String.slice s 0 opener) inner) b) "",
        Option.some found =>
            match found {
                Pair.pair label after =>
                    match Markdown.resolve_link label after b.refs {
                        Option.some resolved => Markdown.emit_link b image label resolved s,
                        Option.none =>
                            Markdown.inline_loop (Markdown.push_piece (String.slice s 0 opener) b) inner
                    }
            }
    }

/// `<` : URI autolink, email autolink, raw HTML, then a literal `<`.
#[partial]
def Markdown.scan_lt (b : Markdown.InlineBuild) (s : String) : Markdown.InlineBuild :=
    match Markdown.scan_uri_autolink s {
        Option.some found =>
            match found {
                Pair.pair content rest =>
                    Markdown.inline_loop
                        (Markdown.prev_of s rest
                            (Markdown.push_node (Markdown.Inline.inline_autolink content content) b))
                        rest
            },
        Option.none =>
            match Markdown.scan_email_autolink s {
                Option.some found =>
                    match found {
                        Pair.pair content rest =>
                            Markdown.inline_loop
                                (Markdown.prev_of s rest
                                    (Markdown.push_node
                                        (Markdown.Inline.inline_autolink (String.concat "mailto:" content) content)
                                        b))
                                rest
                    },
                Option.none =>
                    match Markdown.scan_html_tag s {
                        Option.some found =>
                            match found {
                                Pair.pair literal rest =>
                                    Markdown.inline_loop
                                        (Markdown.prev_of s rest
                                            (Markdown.push_node (Markdown.Inline.inline_html literal) b))
                                        rest
                            },
                        Option.none =>
                            Markdown.inline_loop (Markdown.push_piece "<" b) (String.drop 1i64 s)
                    }
            }
    }

/// The last codepoint of `s`, for the delimiter flanking state.
#[partial]
def Markdown.last_cp (s : String) (acc : Option U32) : Option U32 :=
    if is_empty s
    then acc
    else
        match Markdown.codepoint_at s {
            Option.some cp => Markdown.last_cp (String.drop (Markdown.char_width s) s) (Option.some cp),
            Option.none => acc
        }

/// Set `prev` to the last source character of the construct that consumed
/// `whole` down to `rest`. Flanking depends on it, so every construct that
/// does not feed the loop one character at a time must set it.
pub def Markdown.prev_of (whole : String) (rest : String) (b : Markdown.InlineBuild) : Markdown.InlineBuild :=
    let consumed : I64 := I64.sub (String.length whole) (String.length rest) in
    let prefix : String := String.slice whole 0 consumed in
    let p : Option U32 := Markdown.last_cp prefix Option.none in
    { b with prev := p }

// ─── Emphasis ───
//
// Delimiter runs are pushed as text nodes with a `DelimRec` recording the
// node count before them. A later closer looks back for the nearest opener,
// wraps the nodes between (excluding the opener's own text node) and drops
// the records inside the range -- exactly cmark's "remove delimiters between
// opener and closer". Leftover opener delimiters stay as text before the
// wrapped node; leftover closer delimiters are rematched.

def Markdown.is_space_cp (cp : Option U32) : Bool :=
    match cp {
        Option.none => true,
        Option.some c => Markdown.is_unicode_whitespace c
    }

def Markdown.is_punct_cp (cp : Option U32) : Bool :=
    match cp {
        Option.none => false,
        Option.some c => Markdown.is_unicode_punctuation c
    }

/// (left-flanking, right-flanking).
pub def Markdown.flanking (prev : Option U32) (next : Option U32) : Pair Bool Bool :=
    let prev_space : Bool := Markdown.is_space_cp prev in
    let prev_punct : Bool := Markdown.is_punct_cp prev in
    let next_space : Bool := Markdown.is_space_cp next in
    let next_punct : Bool := Markdown.is_punct_cp next in
    let left : Bool :=
        Bool.and (Bool.not next_space)
            (Bool.or (Bool.not next_punct) (Bool.or prev_space prev_punct)) in
    let right : Bool :=
        Bool.and (Bool.not prev_space)
            (Bool.or (Bool.not prev_punct) (Bool.or next_space next_punct)) in
    Pair.pair left right

/// A `*` run opens when left-flanking, closes when right-flanking. An `_` run
/// additionally refuses intraword use.
def Markdown.can_open_run (ch : U8) (prev : Option U32) (next : Option U32) (left : Bool) (right : Bool) : Bool :=
    if U8.beq ch 95u8
    then Bool.and left (Bool.or (Bool.not right) (Markdown.is_punct_cp prev))
    else left

def Markdown.can_close_run (ch : U8) (prev : Option U32) (next : Option U32) (left : Bool) (right : Bool) : Bool :=
    if U8.beq ch 95u8
    then Bool.and right (Bool.or (Bool.not left) (Markdown.is_punct_cp next))
    else right

#[partial]
def Markdown.count_same (ch : U8) (s : String) (n : I64) : Pair I64 String :=
    match String.get s 0 {
        Option.some b =>
            if U8.beq b ch
            then Markdown.count_same ch (String.drop 1i64 s) (I64.add n 1i64)
            else Pair.pair n s,
        Option.none => Pair.pair n s
    }

def Markdown.one_char (ch : U8) : String := String.from_list [ch]

#[partial]
def Markdown.repeat_char (ch : U8) (n : I64) (piece : String) (acc : List String) : String :=
    if I64.lt n 1i64
    then String.concat_list (List.reverse acc)
    else Markdown.repeat_char ch (I64.sub n 1i64) piece (List.cons piece acc)

def Markdown.mod3 (n : I64) : I64 :=
    I64.sub n (I64.mul 3i64 (I64.div n 3i64))

/// cmark's rule of three.
pub def Markdown.rule_of_three (opener : Markdown.DelimRec) (closer_count : I64) (closer_orig : I64)
    (closer_can_open : Bool) : Bool :=
    if Bool.or closer_can_open opener.can_close
    then
        Bool.and (Bool.not (I64.beq (Markdown.mod3 closer_orig) 0i64))
            (I64.beq (Markdown.mod3 (I64.add opener.count closer_orig)) 0i64)
    else false

/// Index of the nearest opener for this closer, or none.
#[partial]
def Markdown.find_opener
    (delims : List Markdown.DelimRec) (ch : U8) (closer_count : I64) (closer_orig : I64)
    (closer_can_open : Bool) (i : I64) : Option I64 :=
    match delims {
        List.empty => Option.none,
        List.cons d rest =>
            if Bool.and (U8.beq d.ch ch) d.can_open
            then
                if Markdown.rule_of_three d closer_count closer_orig closer_can_open
                then Markdown.find_opener rest ch closer_count closer_orig closer_can_open (I64.add i 1i64)
                else Option.some i
            else Markdown.find_opener rest ch closer_count closer_orig closer_can_open (I64.add i 1i64)
    }

def Markdown.emphasis_node (ch : U8) (width : I64) (children : List Markdown.Inline) : Markdown.Inline :=
    if U8.beq ch 126u8
    then Markdown.Inline.inline_strikethrough children
    else if I64.beq width 2i64
    then Markdown.Inline.inline_strong children
    else Markdown.Inline.inline_emphasis children

/// Finish a delimiter run: push any leftover as text, and record it as an
/// opener when it may open.
#[partial]
def Markdown.finish_delim
    (b : Markdown.InlineBuild) (ch : U8) (remaining : I64) (orig : I64) (can_open : Bool) (can_close : Bool)
    (rest : String) : Markdown.InlineBuild :=
    if I64.lt remaining 1i64
    then Markdown.inline_loop b rest
    else
        let text : String := Markdown.repeat_char ch remaining (Markdown.one_char ch) List.empty in
        let outer_len : I64 := b.len in
        let b1 : Markdown.InlineBuild := Markdown.push_node (inline_text text) b in
        let delims : List Markdown.DelimRec :=
            if can_open
            then List.cons (Markdown.mk_delim_rec ch remaining orig can_open can_close outer_len) b.delims
            else b.delims in
        let b2 : Markdown.InlineBuild := { b1 with delims := delims } in
        Markdown.inline_loop b2 rest

/// Match as many closers as possible against this run, then push the rest.
#[partial]
def Markdown.match_closers
    (b : Markdown.InlineBuild) (ch : U8) (remaining : I64) (orig : I64) (can_open : Bool)
    (can_close : Bool) (rest : String) : Markdown.InlineBuild :=
    if I64.lt remaining 1i64
    then Markdown.inline_loop b rest
    else Markdown.match_one b ch remaining orig can_open can_close rest

#[partial]
def Markdown.match_one
    (b : Markdown.InlineBuild) (ch : U8) (remaining : I64) (orig : I64) (can_open : Bool)
    (can_close : Bool) (rest : String) : Markdown.InlineBuild :=
    match Markdown.find_opener b.delims ch remaining orig can_open 0i64 {
        Option.none => Markdown.finish_delim b ch remaining orig can_open can_close rest,
        Option.some index =>
            match List.get index b.delims {
                Option.none => Markdown.finish_delim b ch remaining orig can_open can_close rest,
                Option.some opener =>
                    let width : I64 :=
                        if Bool.and (Bool.not (I64.lt remaining 2i64)) (Bool.not (I64.lt opener.count 2i64))
                        then 2i64 else 1i64 in
                    let content_count : I64 := I64.sub (I64.sub b.len opener.outer_len) 1i64 in
                    let content_rev : List Markdown.Inline := Markdown.list_take content_count b.nodes in
                    let outer : List Markdown.Inline := Markdown.list_drop (I64.add content_count 1i64) b.nodes in
                    let wrapped : Markdown.Inline :=
                        Markdown.emphasis_node ch width (List.reverse content_rev) in
                    let left : I64 := I64.sub opener.count width in
                    let nodes1 : List Markdown.Inline :=
                        if I64.lt left 1i64
                        then List.cons wrapped outer
                        else List.cons wrapped
                                (List.cons (inline_text (Markdown.repeat_char ch left (Markdown.one_char ch) List.empty)) outer) in
                    let len1 : I64 :=
                        if I64.lt left 1i64
                        then I64.add opener.outer_len 1i64
                        else I64.add opener.outer_len 2i64 in
                    let rest_delims : List Markdown.DelimRec := Markdown.list_drop (I64.add index 1i64) b.delims in
                    let delims1 : List Markdown.DelimRec :=
                        if I64.lt left 1i64
                        then rest_delims
                        else List.cons
                                (Markdown.mk_delim_rec ch left opener.orig opener.can_open
                                    opener.can_close opener.outer_len)
                                rest_delims in
                    let b1 : Markdown.InlineBuild :=
                        { b with pieces := List.empty, nodes := nodes1, len := len1, delims := delims1 } in
                    let remaining1 : I64 := I64.sub remaining width in
                    Markdown.match_closers b1 ch remaining1 orig can_open can_close rest
            }
    }

/// `~~` is a strikethrough delimiter; a lone `~` is text.
#[partial]
def Markdown.scan_strike (b : Markdown.InlineBuild) (s : String) : Markdown.InlineBuild :=
    match Markdown.count_same 126u8 s 0i64 {
        Pair.pair n rest =>
            if I64.lt n 2i64
            then Markdown.inline_loop (Markdown.push_piece "~" b) (String.drop 1i64 s)
            else Markdown.scan_delim b s 126u8
    }

#[partial]
def Markdown.scan_delim (b : Markdown.InlineBuild) (s : String) (ch : U8) : Markdown.InlineBuild :=
    match Markdown.count_same ch s 0i64 {
        Pair.pair n rest =>
            let next : Option U32 := Markdown.codepoint_at rest in
            let flank : Pair Bool Bool := Markdown.flanking b.prev next in
            match flank {
                Pair.pair left right =>
                    let can_open : Bool := Markdown.can_open_run ch b.prev next left right in
                    let can_close : Bool := Markdown.can_close_run ch b.prev next left right in
                    let settled : Markdown.InlineBuild := Markdown.flush b in
                    let b1 : Markdown.InlineBuild :=
                        { settled with prev := Option.some (U8.to_u32 ch) } in
                    if can_close
                    then Markdown.match_closers b1 ch n n can_open can_close rest
                    else Markdown.finish_delim b1 ch n n can_open can_close rest
            }
    }
