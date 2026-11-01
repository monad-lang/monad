/// The formatting policy. Kept separate from `render`/`fmt` so both can read
/// it without a module cycle, and so a caller can derive a style with
/// `{ FmtConfig.default with indent_width := 2 }`.
///
/// `max_width` is deliberately absent: this version preserves the author's
/// line breaks and never reflows, and a knob that does nothing is worse than
/// no knob. It belongs here when width-aware layout lands.

pub type LineEnding {
    lf,
    crlf,
}

pub struct FmtConfig {
    /// Spaces per nesting level when `use_tabs` is false.
    indent_width : I64,
    /// One tab per level instead of `indent_width` spaces.
    use_tabs : Bool,
    /// At most this many consecutive blank lines are kept.
    max_blank_lines : I64,
    line_ending : LineEnding,
}

pub def FmtConfig.default : FmtConfig :=
    let c : FmtConfig := {
        indent_width := 4,
        use_tabs := false,
        max_blank_lines := 1,
        line_ending := LineEnding.lf,
    } in
    c

pub def FmtConfig.line_terminator (e : LineEnding) : String :=
    match e {
        LineEnding.lf => "\n",
        LineEnding.crlf => "\r\n",
    }

/// The greatest number of newlines a gap may emit: one line break plus the
/// configured blank lines.
pub def FmtConfig.max_newlines (c : FmtConfig) : I64 :=
    let blank : I64 := c.max_blank_lines in
    I64.add (if I64.lt blank 0 then 0 else blank) 1

/// The indentation text for a nesting level.
pub def FmtConfig.indent (c : FmtConfig) (level : I64) : String :=
    match c {
        { indent_width, use_tabs, .. } =>
            let n : I64 := if I64.lt level 0 then 0 else level in
            if use_tabs
            then String.repeat "\t" n
            else
                let width : I64 := if I64.lt indent_width 0 then 0 else indent_width in
                String.repeat " " (I64.mul n width),
    }
