/// The approval tokenizer: quotes, separators, pipes, redirects and the
/// expansions it cannot read.
use weaver::shell_words {ShellWord, ShellRedir, ShellCmd, ShellScript, ShellWords.parse}
use std::list {List.intercalate}

#[partial]
def word_texts (ws : List ShellWord) : List String :=
    match ws {
        List.empty => List.empty,
        List.cons w rest => List.cons w.text (word_texts rest),
    }

/// Each command's words joined by spaces, commands by `|`.
#[partial]
def shape_go (cs : List ShellCmd) : List String :=
    match cs {
        List.empty => List.empty,
        List.cons c rest => List.cons (List.intercalate " " (word_texts c.words)) (shape_go rest),
    }

def shape (s : String) : String :=
    let sc : ShellScript := ShellWords.parse s in
    List.intercalate "|" (shape_go sc.cmds)

#[partial]
def redir_go (cs : List ShellCmd) : List String :=
    match cs {
        List.empty => List.empty,
        List.cons c rest => List.append (redir_texts c.redirs) (redir_go rest),
    }

#[partial]
def redir_texts (rs : List ShellRedir) : List String :=
    match rs {
        List.empty => List.empty,
        List.cons r rest => List.cons (String.concat (if r.out then ">" else "<") r.target.text) (redir_texts rest),
    }

def redirect_shape (s : String) : String :=
    let sc : ShellScript := ShellWords.parse s in
    List.intercalate " " (redir_go sc.cmds)

#[test]
def test_words_and_separators : Bool :=
    String.beq (shape "ls -la src; cargo test && echo ok || true") "ls -la src|cargo test|echo ok|true"
        && String.beq (shape "a\nb & c") "a|b|c"

#[test]
def test_quotes_are_removed : Bool :=
    String.beq (shape "echo 'a b' \"c d\" e\\ f") "echo a b c d e f"
        && String.beq (shape "echo \"rm -rf /\"") "echo rm -rf /"

#[test]
def test_pipes_mark_the_reader : Bool :=
    let sc : ShellScript := ShellWords.parse "curl -s x | sh" in
    match sc.cmds {
        List.cons a rest => match rest {
            List.cons b _ => Bool.not a.piped && b.piped,
            List.empty => false,
        },
        List.empty => false,
    }

#[test]
def test_redirects_and_fd_numbers : Bool :=
    String.beq (redirect_shape "make > out.log 2>/dev/null < in.txt") ">out.log >/dev/null <in.txt"
        && String.beq (redirect_shape "cmd >>log 2>&1") ">log"
        && String.beq (shape "cmd 2>&1") "cmd"

#[test]
def test_substitutions_are_nested_and_dynamic : Bool :=
    let sc : ShellScript := ShellWords.parse "echo $(rm -rf /tmp/x) `pwd` \"$(id)\"" in
    String.beq (List.intercalate ";" sc.nested) "rm -rf /tmp/x;pwd;id"
        && (match sc.cmds {
            List.cons c _ => match c.words {
                List.cons _ args => match args {
                    List.cons w _ => w.dynamic,
                    List.empty => false,
                },
                List.empty => false,
            },
            List.empty => false,
        })

def unknown_of (s : String) : Bool :=
    let sc : ShellScript := ShellWords.parse s in
    sc.unknown

#[test]
def test_unterminated_text_is_unknown : Bool :=
    unknown_of "echo 'oops"
        && unknown_of "echo $(ls"
        && unknown_of "cat >"
        && Bool.not (unknown_of "echo fine")

#[test]
def test_comments_are_skipped : Bool :=
    String.beq (shape "ls # rm -rf /") "ls"
