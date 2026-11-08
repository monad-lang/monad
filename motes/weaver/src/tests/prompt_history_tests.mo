/// Prompt history across a resume: the session's `prompts.jsonl` record,
/// the fallback from an older session's history, and the merge into Up's
/// list.
use weaver::store {StoreState, Store.append_prompt, Store.read_prompts, Store.prompts_of_history}
use weaver::ui::prompt {PromptModel, Prompt.empty, Prompt.submitted, Prompt.with_history, Prompt.hist_cap}
use shuttle::message {Message}
use shuttle::message_types {Role, Content}
use std::path {Path}
use std::process {exec_cmd, process_id}
use std::list {List.length, List.intercalate}

/// Lists compare as one string (generic list equality is unreliable).
def joined (xs : List String) : String := List.intercalate "|" xs

def text_msg (r : Role) (t : String) : Message :=
    let m : Message := { role := r, content := List.cons (Content.text t) List.empty } in
    m

/// The current entries stay first, the resumed ones follow, and a line in
/// both keeps its newest place.
#[test]
def test_with_history_merges_newest_first : Bool :=
    let p : PromptModel := Prompt.submitted (Prompt.submitted Prompt.empty "a") "b" in
    let merged : PromptModel := Prompt.with_history p ["c", "a", "d"] in
    joined merged.hist == "b|a|c|d" && merged.hist_idx == 0 - 1

#[partial]
def many (n : I64) (acc : List String) : List String :=
    if n < 1 then acc else many (n - 1) (List.cons (I64.to_string n) acc)

#[test]
def test_with_history_keeps_the_cap : Bool :=
    let p : PromptModel := Prompt.with_history Prompt.empty (many 500 List.empty) in
    List.length p.hist == Prompt.hist_cap

/// The fallback keeps what the user typed: no tool results, no notes
/// weaver posted (the compaction summary), no assistant text.
#[test]
def test_prompts_of_history_keeps_user_text : Bool :=
    let tool : Message := { role := Role.user, content := List.cons (Content.tool_result "c" "out" false) List.empty } in
    let h : List Message := [
        text_msg Role.user "first ask",
        text_msg Role.assistant "an answer",
        tool,
        text_msg Role.user "[summary of earlier conversation]\nstuff",
        text_msg Role.user "second\nline two",
    ] in
    joined (Store.prompts_of_history h) == "second\nline two|first ask"

/// Append then read: newest first, a multi-line line whole, quotes,
/// backslashes and non-ASCII intact. A session with no file has none.
#[test]
def test_prompt_record_round_trips : IO Bool := do {
    let dir : String := String.concat "/tmp/weaver_prompt_history_" (I64.to_string process_id);
    let _ <- exec_cmd "rm" ["-rf", dir];
    let _ <- exec_cmd "mkdir" ["-p", dir];
    let st : StoreState := { root := Path.path "/tmp", dir := Path.path dir, id := "s-1" };
    let none_yet <- Store.read_prompts st;
    Store.append_prompt st "fix it";
    Store.append_prompt st "two\nlines \"quoted\" \\ café";
    let got <- Store.read_prompts st;
    let _ <- exec_cmd "rm" ["-rf", dir];
    return (List.length none_yet == 0 && joined got == "two\nlines \"quoted\" \\ café|fix it")
}
