/// Emit formatted source from the token stream.
///
/// Two invariants drive the whole module:
///
/// 1. **Line breaks are the author's.** A gap with a newline in it always
///    becomes a line break; it is never joined into the previous line. Only
///    blank runs are capped. That makes idempotence easy to argue and keeps
///    the formatter from deciding where an expression "should" break.
/// 2. **Tight pairs are the parser's.** `rules.tight_pair` marks the token
///    pairs whose 0-vs-positive gap the parser observes; those are preserved
///    exactly. Everything else gets canonical spacing from `rules`.
///
/// Indentation combines two signals, because neither alone is enough:
///
/// - a source-relative level tree, so an author's continuation lines (a
///   multi-line signature, a broken `match` arm) keep a consistent one-level
///   step and tabs/2/4/8-space files all canonicalize to the configured unit;
/// - opener-line alignment, so a line inside `(`/`[`/`{` is never less
///   indented than one level below the line that opened the innermost one,
///   and a closing line lines up with the line that opened it. (The RAW count
///   of open delimiters is the wrong floor: `return (match x {` opens a paren
///   and a brace on one line, and the arms belong one level below that line,
///   not three.)
///
/// Multi-line token interiors (strings, raw strings, block comments) are
/// opaque: they are written verbatim and never re-indented.

use lib::config { FmtConfig }
use lib::lexer { Lex.gap_tight, Token }
use lib::rules {
    Rules.is_closer, Rules.is_opener, Rules.matching_closer,
    Rules.space_between, Rules.tight_pair,
}

struct OpenDelim {
    close_text : String,
    open_level : I64,
}

struct IndentFrame {
    orig : I64,
    level : I64,
}

struct IndentStep {
    stack : List IndentFrame,
    level : I64,
}

struct CloserStep {
    delims : List OpenDelim,
    level : I64,
    matched : Bool,
}

/// The minimum level for a line inside delimiters: one deeper than the line
/// that opened the innermost one. Deliberately NOT the number of open
/// delimiters -- `return (match x {` opens a paren and a brace on one line,
/// and the arms belong one level below that line, not three.
def inner_floor (delims : List OpenDelim) : I64 :=
    match delims {
        List.empty => 0,
        List.cons top _ => I64.add top.open_level 1,
    }

/// Resolve a line's source-relative level: +1 for a deeper original indent,
/// the same level for an equal one, and a pop (then +1 when the new indent is
/// strictly between two frames) for a shallower one. Capping every increase at
/// one level is what turns an alignment-style indent into a nesting level.
#[partial]
def indent_level (frames : List IndentFrame) (orig : I64) : IndentStep :=
    match frames {
        List.empty =>
            let frame : IndentFrame := { orig := orig, level := 0 } in
            let s : IndentStep := {
                stack := [frame],
                level := 0,
            } in
            s,
        List.cons top rest =>
            if I64.gt orig top.orig then
                let lvl : I64 := I64.add top.level 1 in
                let frame : IndentFrame := { orig := orig, level := lvl } in
                let s : IndentStep := {
                    stack := List.cons frame frames,
                    level := lvl,
                } in
                s
            else if I64.beq orig top.orig then
                let s : IndentStep := { stack := frames, level := top.level } in
                s
            else indent_pop orig frames,
    }

#[partial]
def indent_pop (orig : I64) (frames : List IndentFrame) : IndentStep :=
    match frames {
        List.empty =>
            let frame : IndentFrame := { orig := orig, level := 0 } in
            let s : IndentStep := {
                stack := [frame],
                level := 0,
            } in
            s,
        List.cons top rest =>
            if I64.gt top.orig orig then indent_pop orig rest
            else if I64.beq top.orig orig then
                let s : IndentStep := { stack := frames, level := top.level } in
                s
            else
                // `top.orig < orig`: a continuation indent between two frames.
                let lvl : I64 := I64.add top.level 1 in
                let frame : IndentFrame := { orig := orig, level := lvl } in
                let s : IndentStep := {
                    stack := List.cons frame frames,
                    level := lvl,
                } in
                s,
    }

def push_delim (delims : List OpenDelim) (t : Token) (line_level : I64) : List OpenDelim :=
    let d : OpenDelim := {
        close_text := Rules.matching_closer t.text,
        open_level := line_level,
    } in
    List.cons d delims

/// Pop a matching closer from the top of the delimiter stack. A closer that
/// does not match the top (only possible on input the strict parser rejects)
/// leaves the stack alone and reports `matched := false`.
def closer_step (delims : List OpenDelim) (t : Token) : CloserStep :=
    if Rules.is_closer t then
        match delims {
            List.empty =>
                let s : CloserStep := {
                    delims := List.empty,
                    level := 0,
                    matched := false,
                } in
                s,
            List.cons top rest =>
                if String.beq top.close_text t.text then
                    let s : CloserStep := {
                        delims := rest,
                        level := top.open_level,
                        matched := true,
                    } in
                    s
                else
                    let s : CloserStep := {
                        delims := delims,
                        level := 0,
                        matched := false,
                    } in
                    s,
        }
    else
        let s : CloserStep := {
            delims := delims,
            level := 0,
            matched := false,
        } in
        s

/// The delimiter stack after emitting `t`, given the closer step already
/// applied for it.
def after_delim (cs : CloserStep) (t : Token) (line_level : I64) : List OpenDelim :=
    if Rules.is_opener t
    then push_delim cs.delims t line_level
    else cs.delims

def max_i64 (a : I64) (b : I64) : I64 :=
    if I64.gt a b then a else b

#[partial]
def render_loop
    (cfg : FmtConfig) (tokens : List Token)
    (prev : Option Token) (delims : List OpenDelim)
    (indents : List IndentFrame) (line_level : I64)
    (out : List String) (first : Bool) : List String :=
    match tokens {
        List.empty => out,
        List.cons t rest =>
            if first then
                // Leading whitespace and blank lines are dropped: the first
                // token is always at level 0.
                let cs := closer_step delims t in
                let after : List OpenDelim := after_delim cs t 0 in
                let frame : IndentFrame := { orig := t.gap.indent, level := 0 } in
                render_loop cfg rest (Option.some t) after
                    [frame] 0 (List.cons t.text out) false
            else if I64.gt t.gap.newlines 0 then
                let step := indent_level indents t.gap.indent in
                let cs := closer_step delims t in
                let level : I64 :=
                    if Rules.is_closer t && cs.matched
                    then cs.level
                    else max_i64 step.level (inner_floor delims) in
                let after : List OpenDelim := after_delim cs t level in
                let count : I64 :=
                    if I64.gt t.gap.newlines (FmtConfig.max_newlines cfg)
                    then FmtConfig.max_newlines cfg
                    else t.gap.newlines in
                let newline : String :=
                    String.repeat (FmtConfig.line_terminator cfg.line_ending) count in
                let indent : String := FmtConfig.indent cfg level in
                render_loop cfg rest (Option.some t) after
                    step.stack level
                    (List.cons t.text (List.cons indent (List.cons newline out))) false
            else
                let cs := closer_step delims t in
                let after : List OpenDelim := after_delim cs t line_level in
                let spaces : I64 := match prev {
                    Option.none => 0,
                    Option.some p =>
                        if Rules.tight_pair p t
                        then if Lex.gap_tight t.gap then 0 else 1
                        else Rules.space_between p t,
                } in
                let out2 : List String :=
                    if I64.beq spaces 0
                    then List.cons t.text out
                    else List.cons t.text (List.cons " " out) in
                render_loop cfg rest (Option.some t) after
                    indents line_level out2 false,
    }

pub def Render.render (cfg : FmtConfig) (tokens : List Token) : String :=
    match tokens {
        List.empty => "",
        List.cons _ _ =>
            let pieces : List String :=
                render_loop cfg tokens Option.none List.empty List.empty 0 List.empty true in
            let body : String := String.concat_list (List.reverse pieces) in
            String.concat body (FmtConfig.line_terminator cfg.line_ending),
    }
