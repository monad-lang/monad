/// `/btw` (`btw.mo`): the one prompt the side question sends.
use weaver::btw {Btw.prompt}
use shuttle::message {Message}
use shuttle::message_types {Role, Content}

def say (r : Role) (t : String) : Message :=
    let m : Message := { role := r, content := List.cons (Content.text t) List.empty } in
    m

/// The question and the quoted prose are in; tool traffic is not (a tool
/// result could otherwise steer the answer).
#[test]
def test_prompt_quotes_prose_and_drops_tool_traffic : Bool :=
    let tool : Message := { role := Role.user, content := List.cons (Content.tool_result "c1" "TOOL-OUTPUT" false) List.empty } in
    let h : List Message := [say Role.user "fix the build", tool, say Role.assistant "patched lexer.mo"] in
    let p : String := Btw.prompt h "what changed?" in
    String.contains p "User: fix the build" && String.contains p "Assistant: patched lexer.mo"
        && String.contains p "Side question: what changed?" && Bool.not (String.contains p "TOOL-OUTPUT")

/// An empty session still asks the question.
#[test]
def test_prompt_without_history : Bool :=
    let p : String := Btw.prompt List.empty "hi?" in
    String.contains p "(no conversation yet)" && String.contains p "Side question: hi?"

/// Past the budget, the newest messages win.
#[test]
def test_prompt_keeps_the_newest_messages : Bool :=
    let old : Message := say Role.user (String.concat "OLDEST " (String.repeat "x" 30000)) in
    let h : List Message := [old, say Role.assistant "NEWEST"] in
    let p : String := Btw.prompt h "q" in
    String.contains p "NEWEST" && Bool.not (String.contains p "OLDEST")
