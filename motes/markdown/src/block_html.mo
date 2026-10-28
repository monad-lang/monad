/// HTML block starts and terminations: CommonMark's seven kinds.
///
///   1. `<script`, `<pre`, `<style`, `<textarea` -- ends at the matching
///      closing tag, and a blank line does not end it;
///   2. `<!--` -- ends at `-->`;
///   3. `<?` -- ends at `?>`;            4. `<!A` -- ends at `>`;
///   5. `<![CDATA[` -- ends at `]]>`;
///   6. a block-level tag name -- ends at a blank line;
///   7. any complete tag alone on the line -- ends at a blank line, and it
///      cannot interrupt a paragraph.
///
/// Types 1-6 interrupt a paragraph; 7 cannot. The literal keeps the source
/// lines from the container's content column, so a block that starts with up
/// to three leading spaces keeps them in its output.
use init::string {}
use parsec::core {is_empty}
use lib::scan {Markdown.Cursor, Markdown.char_width}

/// ASCII-only case-insensitive prefix test (`String.to_lowercase` is ASCII).
pub def Markdown.ci_prefix (prefix : String) (s : String) : Bool :=
    String.starts_with prefix (String.to_lowercase s)

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

#[partial]
def Markdown.take_tag_name (c : Markdown.Cursor) (acc : List String) : Pair String Markdown.Cursor :=
    match Markdown.Cursor.peek c {
        Option.some b =>
            if Markdown.is_tag_name_char b
            then
                let w : I64 := Markdown.char_width c.text in
                Markdown.take_tag_name (Markdown.Cursor.step c) (List.cons (String.slice c.text 0 w) acc)
            else Pair.pair (String.concat_list (List.reverse acc)) c,
        Option.none => Pair.pair (String.concat_list (List.reverse acc)) c
    }

/// The raw HTML tag names that open a type-6 block.
def Markdown.html_block_tags : List String :=
    [ "address", "article", "aside", "base", "basefont", "blockquote", "body",
      "caption", "center", "col", "colgroup", "dd", "details", "dialog", "dir",
      "div", "dl", "dt", "fieldset", "figcaption", "figure", "footer", "form",
      "frame", "frameset", "h1", "h2", "h3", "h4", "h5", "h6", "head", "header",
      "hr", "html", "iframe", "legend", "li", "link", "main", "menu", "menuitem",
      "nav", "noframes", "ol", "optgroup", "option", "p", "param", "section",
      "source", "summary", "table", "tbody", "td", "tfoot", "th", "thead",
      "title", "tr", "track", "ul" ]

pub def Markdown.block_tag (name : String) : Bool :=
    Markdown.html_tag_member name Markdown.html_block_tags

#[partial]
def Markdown.html_tag_member (name : String) (names : List String) : Bool :=
    match names {
        List.empty => false,
        List.cons n rest => Bool.or (String.beq n name) (Markdown.html_tag_member name rest)
    }

/// After a tag name: whitespace, `>`, `/>`, or the end of the line.
def Markdown.tag_name_terminated (c : Markdown.Cursor) : Bool :=
    match Markdown.Cursor.peek c {
        Option.none => true,
        Option.some b =>
            if Markdown.is_tag_ws b
            then true
            else if U8.beq b 62u8
            then true
            else U8.beq b 47u8
    }

/// Type 1: `<script`, `<pre`, `<style`, `<textarea`, then a terminator.
def Markdown.html_type_one (c : Markdown.Cursor) : Option I64 :=
    if Bool.or
        (Bool.or (Markdown.ci_prefix "<script" c.text) (Markdown.ci_prefix "<pre" c.text))
        (Bool.or (Markdown.ci_prefix "<style" c.text) (Markdown.ci_prefix "<textarea" c.text))
    then
        let name : String :=
            if Markdown.ci_prefix "<script" c.text then "script"
            else if Markdown.ci_prefix "<pre" c.text then "pre"
            else if Markdown.ci_prefix "<style" c.text then "style"
            else "textarea" in
        let after : Markdown.Cursor := Markdown.Cursor.step_many (I64.add 1i64 (String.length name)) c in
        if Markdown.tag_name_terminated after then Option.some 1i64 else Option.none
    else Option.none

/// Types 2-5, by their fixed prefixes.
def Markdown.html_type_prefix (c : Markdown.Cursor) : Option I64 :=
    if String.starts_with "<!--" c.text then Option.some 2i64
    else if String.starts_with "<?" c.text then Option.some 3i64
    else if String.starts_with "<![CDATA[" c.text then Option.some 5i64
    else if String.starts_with "<!" c.text then
        match Markdown.Cursor.peek (Markdown.Cursor.step_many 2i64 c) {
            Option.some b =>
                if Bool.and (U8.lt 64u8 b) (U8.lt b 91u8) then Option.some 4i64 else Option.none,
            Option.none => Option.none
        }
    else Option.none

/// Types 6 and 7, from the tag name.
def Markdown.html_type_tag (c : Markdown.Cursor) (in_paragraph : Bool) : Option I64 :=
    let after_lt : Markdown.Cursor := Markdown.Cursor.step c in
    let closing : Bool :=
        match Markdown.Cursor.peek after_lt {
            Option.some b => U8.beq b 47u8,
            Option.none => false
        } in
    let name_cursor : Markdown.Cursor :=
        if closing then Markdown.Cursor.step after_lt else after_lt in
    match Markdown.take_tag_name name_cursor List.empty {
        Pair.pair name after_name =>
            if String.beq name ""
            then Option.none
            else if Bool.and (Markdown.block_tag (String.to_lowercase name))
                    (Markdown.tag_name_terminated after_name)
            then Option.some 6i64
            else if in_paragraph
            then Option.none
            else if Markdown.complete_tag (c)
            then Option.some 7i64
            else Option.none
    }

/// A complete open or closing tag, with nothing but spaces after it.
def Markdown.complete_tag (c : Markdown.Cursor) : Bool :=
    let after_lt : Markdown.Cursor := Markdown.Cursor.step c in
    match Markdown.Cursor.peek after_lt {
        Option.some b =>
            if U8.beq b 47u8
            then Markdown.complete_tag_named true (Markdown.Cursor.step after_lt)
            else Markdown.complete_tag_named false after_lt,
        Option.none => false
    }

def Markdown.complete_tag_named (closing : Bool) (c : Markdown.Cursor) : Bool :=
    match Markdown.take_tag_name c List.empty {
        Pair.pair name after_name =>
            if String.beq name ""
            then false
            else if closing
            then Markdown.close_tag_tail after_name
            else Markdown.open_tag_tail after_name
    }

/// A closing tag's tail: whitespace then `>`, then only whitespace.
#[partial]
def Markdown.close_tag_tail (c : Markdown.Cursor) : Bool :=
    let skipped : Markdown.Cursor := Markdown.Cursor.skip_spaces c in
    match Markdown.Cursor.peek skipped {
        Option.some b =>
            if U8.beq b 62u8
            then Markdown.Cursor.blank (Markdown.Cursor.step skipped)
            else false,
        Option.none => false
    }

/// An open tag's tail: attributes, then `>` or `/>`, then only whitespace.
#[partial]
def Markdown.open_tag_tail (c : Markdown.Cursor) : Bool :=
    let skipped : Markdown.Cursor := Markdown.Cursor.skip_spaces c in
    match Markdown.Cursor.peek skipped {
        Option.none => false,
        Option.some b =>
            if U8.beq b 62u8
            then Markdown.Cursor.blank (Markdown.Cursor.step skipped)
            else if U8.beq b 47u8
            then
                match Markdown.Cursor.peek (Markdown.Cursor.step skipped) {
                    Option.some s2 =>
                        if U8.beq s2 62u8
                        then Markdown.Cursor.blank (Markdown.Cursor.step (Markdown.Cursor.step skipped))
                        else false,
                    Option.none => false
                }
            else Markdown.open_tag_attr skipped
    }

/// One attribute, then the tag tail again.
#[partial]
def Markdown.open_tag_attr (c : Markdown.Cursor) : Bool :=
    match Markdown.take_tag_name c List.empty {
        Pair.pair name after_name =>
            if String.beq name ""
            then false
            else
                let skipped : Markdown.Cursor := Markdown.Cursor.skip_spaces after_name in
                match Markdown.Cursor.peek skipped {
                    Option.some b =>
                        if U8.beq b 61u8
                        then Markdown.open_tag_value (Markdown.Cursor.skip_spaces (Markdown.Cursor.step skipped))
                        else Markdown.open_tag_tail after_name,
                    Option.none => Markdown.open_tag_tail after_name
                }
    }

#[partial]
def Markdown.open_tag_value (c : Markdown.Cursor) : Bool :=
    match Markdown.Cursor.peek c {
        Option.none => false,
        Option.some b =>
            if Bool.or (U8.beq b 34u8) (U8.beq b 39u8)
            then Markdown.skip_to_quote b (Markdown.Cursor.step c)
            else if U8.beq b 60u8
            then false
            else Markdown.skip_unquoted (Markdown.Cursor.step c)
    }

#[partial]
def Markdown.skip_to_quote (closing : U8) (c : Markdown.Cursor) : Bool :=
    match Markdown.Cursor.peek c {
        Option.none => false,
        Option.some b =>
            if U8.beq b closing
            then Markdown.open_tag_tail (Markdown.Cursor.step c)
            else Markdown.skip_to_quote closing (Markdown.Cursor.step c)
    }

#[partial]
def Markdown.skip_unquoted (c : Markdown.Cursor) : Bool :=
    match Markdown.Cursor.peek c {
        Option.none => false,
        Option.some b =>
            if Bool.or (Markdown.is_tag_ws b) (U8.beq b 62u8)
            then Markdown.open_tag_tail c
            else if Bool.or (U8.beq b 34u8)
                    (Bool.or (U8.beq b 39u8)
                        (Bool.or (U8.beq b 60u8) (Bool.or (U8.beq b 61u8) (U8.beq b 96u8))))
            then false
            else Markdown.skip_unquoted (Markdown.Cursor.step c)
    }

/// The type of an HTML block starting at `c` (first non-space, `base` is the
/// container's content column), or `none`.
pub def Markdown.html_block_start (c : Markdown.Cursor) (base : I64) (in_paragraph : Bool) : Option I64 :=
    if I64.gt (I64.sub c.column base) 3i64
    then Option.none
    else
        match Markdown.Cursor.peek c {
            Option.some b =>
                if Bool.not (U8.beq b 60u8)
                then Option.none
                else
                    match Markdown.html_type_one c {
                        Option.some t => Option.some t,
                        Option.none =>
                            match Markdown.html_type_prefix c {
                                Option.some t => Option.some t,
                                Option.none => Markdown.html_type_tag c in_paragraph
                            }
                    },
            Option.none => Option.none
        }

/// Whether an open block of `html_type` ends on this line (types 1-5 end on
/// their terminator; 6 and 7 end at a blank line, which is a matching
/// failure, not a terminator).
pub def Markdown.html_block_ends (html_type : I64) (line : String) : Bool :=
    let lower : String := String.to_lowercase line in
    if I64.beq html_type 1i64
    then Bool.or
        (Bool.or (String.contains lower "</script") (String.contains lower "</pre"))
        (Bool.or (String.contains lower "</style") (String.contains lower "</textarea"))
    else if I64.beq html_type 2i64 then String.contains lower "-->"
    else if I64.beq html_type 3i64 then String.contains lower "?>"
    else if I64.beq html_type 4i64 then String.contains lower ">"
    else if I64.beq html_type 5i64 then String.contains lower "]]>"
    else false
