/// `! cmd` (`bang.mo`): which lines are shell lines, and the note the next
/// model message carries.
use weaver::bang {Bang.command, Bang.note, Bang.note_bytes}

#[test]
def test_command_takes_the_rest_trimmed : Bool :=
    let tight : Bool := match Bang.command "!ls -la" { Option.some c => c == "ls -la", Option.none => false } in
    let spaced : Bool :=
        match Bang.command "!   git status  " { Option.some c => c == "git status", Option.none => false } in
    tight && spaced

/// A bare `!` is a shell line with no command (the UI shows usage).
#[test]
def test_bare_bang_is_an_empty_command : Bool :=
    match Bang.command "!" { Option.some c => String.is_empty c, Option.none => false }

#[test]
def test_other_lines_are_not_shell_lines : Bool :=
    let slash : Bool := match Bang.command "/help" { Option.some _ => false, Option.none => true } in
    let prose : Bool := match Bang.command "why does ! fail" { Option.some _ => false, Option.none => true } in
    slash && prose

#[test]
def test_note_names_the_command_and_its_output : Bool :=
    let n : String := Bang.note "echo hi" "hi\n" in
    String.contains n "$ echo hi" && String.contains n "hi\n" && String.contains n "the user ran"

/// A flood of output is capped before it reaches the model.
#[test]
def test_note_caps_the_output : Bool :=
    let big : String := String.repeat "0123456789abcdef" 2048i64 in
    let n : String := Bang.note "cat big" big in
    I64.lt (String.length n) (Bang.note_bytes + 200i64) && String.contains n "truncated"
