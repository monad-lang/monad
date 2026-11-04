/// weaver / shell_words -- a conservative POSIX-sh tokenizer for approval
/// decisions: it splits a command line into simple commands and their words
/// and redirects, so the gate can tell where a command reaches and what it
/// runs. It never executes or expands anything. A word that depends on an
/// expansion (`$VAR`, `$(..)`, backticks) is marked dynamic; a substituted
/// command's text is kept in `nested` so it is scanned too.

/// One word after quote removal. `dynamic` when an expansion makes its
/// runtime value unknowable here.
pub struct ShellWord {
    text : String,
    dynamic : Bool,
}

/// `>`/`>>` (out) or `<` (in) and the word it names.
pub struct ShellRedir {
    out : Bool,
    target : ShellWord,
}

/// A simple command; `piped` when its stdin is the previous command's
/// stdout.
pub struct ShellCmd {
    words : List ShellWord,
    redirs : List ShellRedir,
    piped : Bool,
}

/// `unknown` when the text could not be read (an unterminated quote or
/// substitution, a redirect with no target).
pub struct ShellScript {
    cmds : List ShellCmd,
    unknown : Bool,
    nested : List String,
}

struct Lex {
    word : List U8,
    has_word : Bool,
    dyn : Bool,
    words : List ShellWord,
    redirs : List ShellRedir,
    redir : Option Bool,
    piped : Bool,
    cmds : List ShellCmd,
    unknown : Bool,
    nested : List String,
}

def lex_start : Lex :=
    let l : Lex := {
        word := List.empty, has_word := false, dyn := false, words := List.empty, redirs := List.empty,
        redir := Option.none, piped := false, cmds := List.empty, unknown := false, nested := List.empty,
    } in
    l

pub def ShellWords.parse (s : String) : ShellScript :=
    let l : Lex := lex (String.to_list s) lex_start in
    let sc : ShellScript := { cmds := List.reverse l.cmds, unknown := l.unknown, nested := List.reverse l.nested } in
    sc

// ── the lexer state ─────────────────────────────────────────────────────

def push_byte (b : U8) (st : Lex) : Lex :=
    let st2 : Lex := { st with word := List.cons b st.word, has_word := true } in
    st2

def mark_dyn (st : Lex) : Lex :=
    let st2 : Lex := { st with dyn := true, has_word := true } in
    st2

def add_nested (text : String) (st : Lex) : Lex :=
    let st2 : Lex := { st with nested := List.cons text st.nested } in
    st2

def set_unknown (st : Lex) : Lex :=
    let st2 : Lex := { st with unknown := true } in
    st2

/// Close the current word: it is a pending redirect's target, or the
/// command's next word.
def end_word (st : Lex) : Lex :=
    if Bool.not st.has_word then st
    else
        let w : ShellWord := { text := String.from_list (List.reverse st.word), dynamic := st.dyn } in
        match st.redir {
            Option.some out =>
                let r : ShellRedir := { out := out, target := w } in
                let st2 : Lex := { st with word := List.empty, has_word := false, dyn := false, redir := Option.none, redirs := List.cons r st.redirs } in
                st2,
            Option.none =>
                let st2 : Lex := { st with word := List.empty, has_word := false, dyn := false, words := List.cons w st.words } in
                st2,
        }

/// Close the current command; `piped_next` says whether the next one
/// reads this one's output.
def end_cmd (piped_next : Bool) (st0 : Lex) : Lex :=
    let st : Lex := end_word st0 in
    let dangling : Bool := match st.redir { Option.some _ => true, Option.none => false } in
    let empty : Bool := Bool.and (List.is_empty st.words) (List.is_empty st.redirs) in
    let c : ShellCmd := { words := List.reverse st.words, redirs := List.reverse st.redirs, piped := st.piped } in
    let cmds : List ShellCmd := if empty then st.cmds else List.cons c st.cmds in
    let st2 : Lex := { st with words := List.empty, redirs := List.empty, redir := Option.none, piped := piped_next,
        cmds := cmds, unknown := Bool.or st.unknown dangling } in
    st2

def start_redir (out : Bool) (st0 : Lex) : Lex :=
    let st : Lex := end_word st0 in
    let st2 : Lex := { st with redir := Option.some out } in
    st2

// ── bytes ───────────────────────────────────────────────────────────────

def is_byte (c : I64) (b : U8) : Bool := U8.to_i64 b == c

def is_blank (b : U8) : Bool := Bool.or (is_byte 32 b) (is_byte 9 b)

def is_digit (b : U8) : Bool :=
    let c : I64 := U8.to_i64 b in
    Bool.and (Bool.not (c < 48)) (Bool.not (57 < c))

def next_is (c : I64) (bs : List U8) : Bool :=
    match bs {
        List.empty => false,
        List.cons b _ => is_byte c b,
    }

def drop1 (bs : List U8) : List U8 :=
    match bs {
        List.empty => bs,
        List.cons _ rest => rest,
    }

#[partial]
def all_digits (bs : List U8) : Bool :=
    match bs {
        List.empty => true,
        List.cons b rest => if is_digit b then all_digits rest else false,
    }

/// `2>`: a word of digits right before `>`/`<` is a file descriptor, not
/// an argument.
def drop_fd_word (st : Lex) : Lex :=
    if Bool.and st.has_word (Bool.and (Bool.not st.dyn) (all_digits st.word))
    then
        let st2 : Lex := { st with word := List.empty, has_word := false } in
        st2
    else st

// ── the scanner ─────────────────────────────────────────────────────────

#[partial]
def lex (bs : List U8) (st : Lex) : Lex :=
    match bs {
        List.empty => end_cmd false st,
        List.cons b rest => lex_byte b rest st,
    }

#[partial]
def lex_byte (b : U8) (rest : List U8) (st : Lex) : Lex :=
    if is_blank b then lex rest (end_word st)
    else if Bool.or (is_byte 10 b) (is_byte 59 b) then lex rest (end_cmd false st)
    else if is_byte 124 b then lex_pipe rest st
    else if is_byte 38 b then lex_amp rest st
    else if is_byte 62 b then lex_out rest (drop_fd_word st)
    else if is_byte 60 b then lex_in rest (drop_fd_word st)
    else if Bool.or (is_byte 40 b) (is_byte 41 b) then lex rest (end_cmd false st)
    else if is_byte 39 b then lex_squote rest st
    else if is_byte 34 b then lex_dquote rest st
    else if is_byte 92 b then lex_escape rest st
    else if is_byte 36 b then lex_dollar rest st
    else if is_byte 96 b then lex_backtick rest st
    else if Bool.and (is_byte 35 b) (Bool.not st.has_word) then lex (skip_comment rest) st
    else lex rest (push_byte b st)

/// `|` pipes; `||` separates; `|&` pipes stderr too.
#[partial]
def lex_pipe (rest : List U8) (st : Lex) : Lex :=
    if next_is 124 rest then lex (drop1 rest) (end_cmd false st)
    else if next_is 38 rest then lex (drop1 rest) (end_cmd true st)
    else lex rest (end_cmd true st)

/// `&&` separates; `&>` redirects both streams; a lone `&` backgrounds.
#[partial]
def lex_amp (rest : List U8) (st : Lex) : Lex :=
    if next_is 38 rest then lex (drop1 rest) (end_cmd false st)
    else if next_is 62 rest then lex (drop_gt (drop1 rest)) (start_redir true st)
    else lex rest (end_cmd false st)

def drop_gt (bs : List U8) : List U8 :=
    if next_is 62 bs then drop1 bs else bs

/// `>`, `>>`, `>|`; `>&2` duplicates a descriptor and names no file.
#[partial]
def lex_out (rest : List U8) (st : Lex) : Lex :=
    let r1 : List U8 := if Bool.or (next_is 62 rest) (next_is 124 rest) then drop1 rest else rest in
    if next_is 38 r1 then lex (skip_fd (drop1 r1)) (end_word st)
    else lex r1 (start_redir true st)

/// `<`, `<<` (heredoc delimiter), `<<<` (here-string), `<&0`; `<(..)` is a
/// process substitution, scanned like `$(..)`.
#[partial]
def lex_in (rest : List U8) (st : Lex) : Lex :=
    if next_is 40 rest then lex_subst (drop1 rest) (mark_dyn st)
    else if next_is 38 rest then lex (skip_fd (drop1 rest)) (end_word st)
    else
        let r1 : List U8 := if next_is 60 rest then drop1 rest else rest in
        let r2 : List U8 := if next_is 60 r1 then drop1 r1 else r1 in
        let r3 : List U8 := if next_is 45 r2 then drop1 r2 else r2 in
        lex r3 (start_redir false st)

#[partial]
def skip_fd (bs : List U8) : List U8 :=
    match bs {
        List.empty => bs,
        List.cons b rest => if Bool.or (is_digit b) (is_byte 45 b) then skip_fd rest else bs,
    }

#[partial]
def skip_comment (bs : List U8) : List U8 :=
    match bs {
        List.empty => bs,
        List.cons b rest => if is_byte 10 b then bs else skip_comment rest,
    }

/// `'...'`: every byte literal up to the closing quote.
#[partial]
def lex_squote (bs : List U8) (st : Lex) : Lex :=
    match bs {
        List.empty => end_cmd false (set_unknown st),
        List.cons b rest =>
            if is_byte 39 b then lex rest (mark_quoted st)
            else lex_squote rest (push_byte b st),
    }

/// `''` is still a word.
def mark_quoted (st : Lex) : Lex :=
    let st2 : Lex := { st with has_word := true } in
    st2

/// `"..."`: backslash escapes, and expansions stay live. One self-call:
/// the compiled backend's tail-call rewrite needs that.
#[partial]
def lex_dquote (bs : List U8) (st : Lex) : Lex :=
    match bs {
        List.empty => end_cmd false (set_unknown st),
        List.cons b rest =>
            if is_byte 34 b then lex rest (mark_quoted st)
            else match dquote_step b rest st {
                Pair.pair r st2 => lex_dquote r st2,
            },
    }

/// One byte (or escape, or substitution) inside double quotes. A
/// substitution that never closes answers no input and an unknown state.
def dquote_step (b : U8) (rest : List U8) (st : Lex) : Pair (List U8) Lex :=
    if is_byte 92 b then Pair.pair (drop1 rest) (push_first rest st)
    else if Bool.and (is_byte 36 b) (next_is 40 rest) then nested_into (capture_paren (drop1 rest) 1 List.empty) (mark_dyn st)
    else if is_byte 36 b then Pair.pair rest (push_byte b (mark_dyn st))
    else if is_byte 96 b then nested_into (capture_backtick rest List.empty) (mark_dyn st)
    else Pair.pair rest (push_byte b st)

def nested_into (got : Pair (List U8) (Option String)) (st : Lex) : Pair (List U8) Lex :=
    match got {
        Pair.pair rest text => match text {
            Option.none => Pair.pair List.empty (set_unknown st),
            Option.some t => Pair.pair rest (add_nested t st),
        },
    }

def push_first (bs : List U8) (st : Lex) : Lex :=
    match bs {
        List.empty => st,
        List.cons b _ => push_byte b st,
    }

/// `\x` is `x`; a backslash-newline joins lines.
#[partial]
def lex_escape (bs : List U8) (st : Lex) : Lex :=
    match bs {
        List.empty => lex bs st,
        List.cons b rest => if is_byte 10 b then lex rest st else lex rest (push_byte b st),
    }

/// `$(..)`/`$((..))` capture a nested command; any other `$` is a
/// parameter expansion.
#[partial]
def lex_dollar (bs : List U8) (st : Lex) : Lex :=
    if next_is 40 bs then lex_subst (drop1 bs) (mark_dyn st)
    else lex bs (push_byte 36u8 (mark_dyn st))

#[partial]
def lex_subst (bs : List U8) (st : Lex) : Lex :=
    match nested_into (capture_paren bs 1 List.empty) st {
        Pair.pair rest st2 => lex rest st2,
    }

#[partial]
def lex_backtick (bs : List U8) (st : Lex) : Lex :=
    match nested_into (capture_backtick bs List.empty) (mark_dyn st) {
        Pair.pair rest st2 => lex rest st2,
    }

/// The text up to the `)` that closes depth 1, and the bytes after it.
/// None when the input ends first.
#[partial]
def capture_paren (bs : List U8) (depth : I64) (acc : List U8) : Pair (List U8) (Option String) :=
    match bs {
        List.empty => Pair.pair bs Option.none,
        List.cons b rest =>
            if Bool.and (is_byte 41 b) (depth == 1) then Pair.pair rest (Option.some (String.from_list (List.reverse acc)))
            else capture_paren rest (paren_depth b depth) (List.cons b acc),
    }

def paren_depth (b : U8) (depth : I64) : I64 :=
    if is_byte 40 b then depth + 1
    else if is_byte 41 b then depth - 1
    else depth

#[partial]
def capture_backtick (bs : List U8) (acc : List U8) : Pair (List U8) (Option String) :=
    match bs {
        List.empty => Pair.pair bs Option.none,
        List.cons b rest =>
            if is_byte 96 b then Pair.pair rest (Option.some (String.from_list (List.reverse acc)))
            else capture_backtick rest (List.cons b acc),
    }
