/// Inline `<` constructs: URI and email autolinks, then raw inline HTML.
///
/// Each scanner returns the recognised text and the remainder, so the inline
/// pass can fall back to a literal `<` in order: autolink, raw HTML, text.
use init::string {}
use parsec::core {is_empty}
use lib::scan {Markdown.char_width}

def Markdown.is_uri_char (b : U8) : Bool :=
    Bool.not
        (Bool.or (U8.lt b 33u8)
            (Bool.or (U8.beq b 60u8) (U8.beq b 62u8)))

def Markdown.is_alpha (b : U8) : Bool :=
    Bool.or (Bool.and (U8.lt 64u8 b) (U8.lt b 91u8))
        (Bool.and (U8.lt 96u8 b) (U8.lt b 123u8))

def Markdown.is_scheme_char (b : U8) : Bool :=
    Bool.or (Markdown.is_alpha b)
        (Bool.or (Bool.and (U8.lt 47u8 b) (U8.lt b 58u8))
            (Bool.or (U8.beq b 43u8) (Bool.or (U8.beq b 45u8) (U8.beq b 46u8))))

/// `<scheme:...>`: a scheme, a colon, then no spaces or angle brackets.
#[partial]
def Markdown.uri_autolink_go (content : String) (s : String) (n : I64) : Option (Pair String String) :=
    if I64.lt 1000000i64 n
    then Option.none
    else
        match String.get s 0 {
            Option.none => Option.none,
            Option.some b =>
                if U8.beq b 62u8
                then
                    if I64.lt n 1i64
                    then Option.none
                    else
                        let inner : String := String.slice content 0 n in
                        if Markdown.has_scheme inner
                        then Option.some (Pair.pair inner (String.drop 1i64 s))
                        else Option.none
                else if Markdown.is_uri_char b
                then Markdown.uri_autolink_go content (String.drop 1i64 s) (I64.add n 1i64)
                else Option.none
        }

/// Whether the text before the first `:` is a valid scheme (2-32 chars).
pub def Markdown.has_scheme (s : String) : Bool :=
    Markdown.has_scheme_go s 0i64

#[partial]
def Markdown.has_scheme_go (s : String) (n : I64) : Bool :=
    if I64.lt 32i64 n
    then false
    else
        match String.get s 0 {
            Option.none => false,
            Option.some b =>
                if U8.beq b 58u8
                then Bool.not (I64.lt n 2i64)
                else if Bool.not (Markdown.is_scheme_char b)
                then false
                else Markdown.has_scheme_go (String.drop 1i64 s) (I64.add n 1i64)
        }

/// `<scheme:...>` at `s` (which starts with `<`).
#[partial]
pub def Markdown.scan_uri_autolink (s : String) : Option (Pair String String) :=
    let after : String := String.drop 1i64 s in
    match Markdown.uri_autolink_go after after 0i64 {
        Option.some found => Option.some found,
        Option.none => Option.none
    }

// ─── Email autolinks ───

def Markdown.is_local_char (b : U8) : Bool :=
    if Markdown.is_alpha b then true
    else if Bool.and (U8.lt 47u8 b) (U8.lt b 58u8) then true
    else if Bool.and (U8.lt 41u8 b) (U8.lt b 44u8) then true
    else if U8.beq b 46u8 then true
    else if U8.beq b 33u8 then true
    else if U8.beq b 35u8 then true
    else if U8.beq b 36u8 then true
    else if U8.beq b 37u8 then true
    else if U8.beq b 38u8 then true
    else if U8.beq b 39u8 then true
    else if U8.beq b 42u8 then true
    else if U8.beq b 43u8 then true
    else if U8.beq b 61u8 then true
    else if U8.beq b 63u8 then true
    else if U8.beq b 94u8 then true
    else if U8.beq b 95u8 then true
    else if U8.beq b 96u8 then true
    else if U8.beq b 123u8 then true
    else if U8.beq b 124u8 then true
    else if U8.beq b 125u8 then true
    else U8.beq b 126u8

/// `<local@domain>`: the local part is non-empty, the domain has a dot.
#[partial]
pub def Markdown.scan_email_autolink (s : String) : Option (Pair String String) :=
    let after : String := String.drop 1i64 s in
    Markdown.email_go after List.empty 0i64 false false

#[partial]
def Markdown.email_go (s : String) (acc : List String) (n : I64) (seen_at : Bool) (dot_after_at : Bool)
    : Option (Pair String String) :=
    match String.get s 0 {
        Option.none => Option.none,
        Option.some b =>
            if U8.beq b 62u8
            then
                if Bool.and seen_at dot_after_at
                then
                    let inner : String := String.concat_list (List.reverse acc) in
                    if Markdown.valid_email inner
                    then Option.some (Pair.pair inner (String.drop 1i64 s))
                    else Option.none
                else Option.none
            else if U8.beq b 64u8
            then
                if seen_at
                then Option.none
                else Markdown.email_go (String.drop 1i64 s) (List.cons "@" acc) (I64.add n 1i64) true false
            else if Markdown.is_local_char b
            then
                Markdown.email_go (String.drop 1i64 s) (List.cons (String.slice s 0 1i64) acc) (I64.add n 1i64)
                    seen_at (Bool.or dot_after_at (Bool.and seen_at (U8.beq b 46u8)))
            else if Bool.and seen_at (U8.beq b 45u8)
            then
                Markdown.email_go (String.drop 1i64 s) (List.cons "-" acc) (I64.add n 1i64) seen_at dot_after_at
            else Option.none
    }

/// Loose email shape check: one `@`, something before it, and a dot after it
/// that is not the last character.
#[partial]
def Markdown.valid_email (s : String) : Bool :=
    Markdown.valid_email_go s 0i64 (-1i64) (-1i64)

#[partial]
def Markdown.valid_email_go (s : String) (i : I64) (at : I64) (dot : I64) : Bool :=
    if is_empty s
    then Bool.and (Bool.not (I64.lt at 0i64)) (I64.gt dot at)
    else
        match String.get s 0 {
            Option.some b =>
                if U8.beq b 64u8
                then (if I64.lt (-1i64) at then false
                      else Markdown.valid_email_go (String.drop 1i64 s) (I64.add i 1i64) i dot)
                else if U8.beq b 46u8
                then Markdown.valid_email_go (String.drop 1i64 s) (I64.add i 1i64) at i
                else Markdown.valid_email_go (String.drop 1i64 s) (I64.add i 1i64) at dot,
            Option.none => false
        }

// ─── Raw inline HTML ───

def Markdown.is_tag_ws (b : U8) : Bool :=
    Bool.or (U8.beq b 32u8) (Bool.or (U8.beq b 9u8) (Bool.or (U8.beq b 10u8) (U8.beq b 13u8)))

def Markdown.is_tag_name_char (b : U8) : Bool :=
    Bool.or
        (Bool.and (U8.lt 47u8 b) (U8.lt b 58u8))
        (Bool.or
            (Bool.and (U8.lt 64u8 b) (U8.lt b 91u8))
            (Bool.or
                (Bool.and (U8.lt 96u8 b) (U8.lt b 123u8))
                (U8.beq b 45u8)))

/// Consume up to `needle` (inclusive); returns the remainder.
#[partial]
def Markdown.skip_past (needle : String) (s : String) (n : I64) : Option String :=
    if I64.lt (String.length s) (String.length needle)
    then Option.none
    else if String.starts_with needle s
    then Option.some (String.drop (String.length needle) s)
    else
        match String.get s 0 {
            Option.some b => Markdown.skip_past needle (String.drop 1i64 s) (I64.add n 1i64),
            Option.none => Option.none
        }

/// An attribute name starts with a letter, `_` or `:`, and continues with
/// letters, digits, `_`, `.`, `:` or `-`.
def Markdown.is_attr_start (b : U8) : Bool :=
    Bool.or (Markdown.is_alpha b) (Bool.or (U8.beq b 95u8) (U8.beq b 58u8))

def Markdown.is_attr_name_char (b : U8) : Bool :=
    Bool.or (Markdown.is_attr_start b)
        (Bool.or (Bool.and (U8.lt 47u8 b) (U8.lt b 58u8))
            (Bool.or (U8.beq b 46u8) (U8.beq b 45u8)))

/// A raw inline HTML construct at `s` (which starts with `<`): the literal and
/// the remainder.
pub def Markdown.scan_html_tag (s : String) : Option (Pair String String) :=
    if String.starts_with "<!--" s
    then
        // A comment's content may not start with `>` or `->`.
        if Bool.or (String.starts_with "<!-->" s) (String.starts_with "<!--->" s)
        then Option.none
        else Markdown.html_span "<!--" "-->" s
    else if String.starts_with "<![CDATA[" s
    then Markdown.html_span "<![CDATA[" "]]>" s
    else if String.starts_with "<?" s
    then Markdown.html_span "<?" "?>" s
    else Markdown.scan_tag s

def Markdown.html_span (open_marker : String) (close_marker : String) (s : String)
    : Option (Pair String String) :=
    match Markdown.skip_past close_marker (String.drop (String.length open_marker) s) 0i64 {
        Option.some rest =>
            let consumed : I64 := I64.sub (String.length s) (String.length rest) in
            Option.some (Pair.pair (String.slice s 0 consumed) rest),
        Option.none => Option.none
    }

/// A declaration (`<!A…>`) or an open/closing tag.
#[partial]
def Markdown.scan_tag (s : String) : Option (Pair String String) :=
    let after : String := String.drop 1i64 s in
    match String.get after 0 {
        Option.none => Option.none,
        Option.some b =>
            if U8.beq b 33u8 then Markdown.scan_declaration s after
            else if U8.beq b 47u8 then Markdown.scan_close_tag s after
            else if Markdown.is_alpha b then Markdown.scan_open_tag s after
            else Option.none
    }

#[partial]
def Markdown.scan_declaration (orig : String) (after : String) : Option (Pair String String) :=
    match String.get (String.drop 1i64 after) 0 {
        Option.none => Option.none,
        Option.some d =>
            if Markdown.is_alpha d
            then
                match Markdown.declaration_end (String.drop 2i64 after) 0i64 {
                    Option.some rest => Markdown.finish_span orig rest,
                    Option.none => Option.none
                }
            else Option.none
    }

#[partial]
def Markdown.scan_close_tag (orig : String) (after : String) : Option (Pair String String) :=
    match Markdown.tag_name_end (String.drop 1i64 after) {
        Option.some after_name => Markdown.close_tag_tail orig after_name,
        Option.none => Option.none
    }

#[partial]
def Markdown.scan_open_tag (orig : String) (after : String) : Option (Pair String String) :=
    match Markdown.tag_name_end after {
        Option.some after_name => Markdown.open_tag_tail orig after_name,
        Option.none => Option.none
    }

#[partial]
def Markdown.declaration_end (s : String) (n : I64) : Option String :=
    if I64.lt 1000000i64 n
    then Option.none
    else
        match String.get s 0 {
            Option.none => Option.none,
            Option.some b =>
                if U8.beq b 62u8 then Option.some (String.drop 1i64 s)
                else Markdown.declaration_end (String.drop 1i64 s) (I64.add n 1i64)
        }

#[partial]
def Markdown.tag_name_end (s : String) : Option String :=
    match String.get s 0 {
        Option.some b =>
            if Markdown.is_tag_name_char b
            then Markdown.tag_name_end (String.drop 1i64 s)
            else Option.some s,
        Option.none => Option.none
    }

/// After a closing tag's name: whitespace then `>`.
#[partial]
def Markdown.close_tag_tail (orig : String) (s : String) : Option (Pair String String) :=
    match String.get s 0 {
        Option.some b =>
            if Markdown.is_tag_ws b then Markdown.close_tag_tail orig (String.drop 1i64 s)
            else if U8.beq b 62u8
            then Markdown.finish_span orig (String.drop 1i64 s)
            else Option.none,
        Option.none => Option.none
    }

/// After an open tag's name: attributes, then `>` or `/>`.
#[partial]
def Markdown.open_tag_tail (orig : String) (s : String) : Option (Pair String String) :=
    match String.get s 0 {
        Option.none => Option.none,
        Option.some b =>
            if U8.beq b 62u8
            then Markdown.finish_span orig (String.drop 1i64 s)
            else if U8.beq b 47u8
            then Markdown.self_closing_tail orig s
            else if Markdown.is_tag_ws b
            then Markdown.after_tag_space orig (Markdown.skip_ws s)
            else Option.none
    }

/// After whitespace inside a tag: another attribute, `>` or `/>`.
#[partial]
def Markdown.after_tag_space (orig : String) (s : String) : Option (Pair String String) :=
    match String.get s 0 {
        Option.none => Option.none,
        Option.some b =>
            if U8.beq b 62u8
            then Markdown.finish_span orig (String.drop 1i64 s)
            else if U8.beq b 47u8
            then Markdown.self_closing_tail orig s
            else if Markdown.is_attr_start b
            then
                match Markdown.attr_name_end s {
                    Option.some after_name => Markdown.attr_tail orig after_name,
                    Option.none => Option.none
                }
            else Option.none
    }

/// `/>` after a tag name or an attribute.
def Markdown.self_closing_tail (orig : String) (s : String) : Option (Pair String String) :=
    match String.get (String.drop 1i64 s) 0 {
        Option.some c =>
            if U8.beq c 62u8
            then Markdown.finish_span orig (String.drop 2i64 s)
            else Option.none,
        Option.none => Option.none
    }

#[partial]
def Markdown.attr_name_end (s : String) : Option String :=
    match String.get s 0 {
        Option.some b =>
            if Markdown.is_attr_name_char b
            then Markdown.attr_name_end (String.drop 1i64 s)
            else Option.some s,
        Option.none => Option.none
    }

#[partial]
def Markdown.attr_tail (orig : String) (s : String) : Option (Pair String String) :=
    let skipped : String := Markdown.skip_ws s in
    match String.get skipped 0 {
        Option.some b =>
            if U8.beq b 61u8
            then
                let after_eq : String := Markdown.skip_ws (String.drop 1i64 skipped) in
                Markdown.attr_value orig after_eq
            else Markdown.open_tag_tail orig skipped,
        Option.none => Option.none
    }

#[partial]
def Markdown.attr_value (orig : String) (s : String) : Option (Pair String String) :=
    match String.get s 0 {
        Option.none => Option.none,
        Option.some q =>
            if Bool.or (U8.beq q 34u8) (U8.beq q 39u8)
            then Markdown.skip_to_char q (String.drop 1i64 s) orig
            else Markdown.unquoted_end s orig
    }

#[partial]
def Markdown.skip_ws (s : String) : String :=
    match String.get s 0 {
        Option.some b => if Markdown.is_tag_ws b then Markdown.skip_ws (String.drop 1i64 s) else s,
        Option.none => s
    }

#[partial]
def Markdown.skip_to_char (closing : U8) (s : String) (orig : String) : Option (Pair String String) :=
    match String.get s 0 {
        Option.none => Option.none,
        Option.some b =>
            if U8.beq b closing
            then Markdown.after_quoted orig (String.drop 1i64 s)
            else Markdown.skip_to_char closing (String.drop 1i64 s) orig
    }

#[partial]
def Markdown.unquoted_end (s : String) (orig : String) : Option (Pair String String) :=
    match String.get s 0 {
        Option.none => Option.none,
        Option.some b =>
            if Markdown.is_tag_ws b then Markdown.open_tag_tail orig s
            else if U8.beq b 62u8 then Markdown.finish_span orig (String.drop 1i64 s)
            else if U8.beq b 34u8 then Option.none
            else if U8.beq b 39u8 then Option.none
            else if U8.beq b 60u8 then Option.none
            else if U8.beq b 61u8 then Option.none
            else if U8.beq b 96u8 then Option.none
            else Markdown.unquoted_end (String.drop 1i64 s) orig
    }

/// After a quoted attribute value: whitespace, `>` or `/>` -- another
/// attribute must be separated by whitespace.
#[partial]
def Markdown.after_quoted (orig : String) (s : String) : Option (Pair String String) :=
    match String.get s 0 {
        Option.none => Option.none,
        Option.some b =>
            if Markdown.is_tag_ws b
            then Markdown.open_tag_tail orig s
            else if U8.beq b 62u8
            then Markdown.finish_span orig (String.drop 1i64 s)
            else if U8.beq b 47u8
            then Markdown.self_closing_tail orig s
            else Option.none
    }

#[partial]
def Markdown.finish_span (orig : String) (rest : String) : Option (Pair String String) :=
    let consumed : I64 := I64.sub (String.length orig) (String.length rest) in
    Option.some (Pair.pair (String.slice orig 0 consumed) rest)
