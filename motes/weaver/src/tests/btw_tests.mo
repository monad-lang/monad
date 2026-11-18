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

/// A resume folds the older turns into one SYSTEM digest (`fold.mo`), and
/// autocompact summarizes into another: the side question must still SEE
/// them. Dropping system messages would hide the whole earlier conversation.
#[test]
def test_prompt_quotes_the_system_digest : Bool :=
    let digest : Message := say Role.system_ "earlier conversation, folded at resume: 42 messages" in
    let p : String := Btw.prompt [digest, say Role.user "new ask"] "what did we do?" in
    String.contains p "folded at resume" && String.contains p "Note:"

/// The folded digest is the FIRST thing the byte budget drops on a long
/// session (the budget is spent newest-first), so the prompt must still be
/// well-formed: the question comes last and a dropped digest is not a
/// crash. This pins the ordering, not the digest's survival.
#[test]
def test_prompt_survives_a_starved_digest : Bool :=
    let digest : Message := say Role.system_ (String.concat "folded at resume " (String.repeat "y" 30000)) in
    let p : String := Btw.prompt [digest, say Role.user "the newest ask"] "q" in
    Bool.and (String.contains p "the newest ask") (String.contains p "Side question: q")
