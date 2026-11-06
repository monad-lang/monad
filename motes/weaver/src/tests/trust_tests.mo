/// Trusting a project: the record, the state it gives, the prompt's
/// answers, and the whole decision against a temp project and record.
use weaver::trust {
    TrustItem, TrustState, TrustAnswer, Trust.state, Trust.parse_record, Trust.with_root,
    Trust.recorded, Trust.answer_of, Trust.relative, Trust.decide, Trust.forced_by,
    Trust.view,
}
use weaver::place {SessionPlace}
use std::path {Path}
use std::list {List.intercalate}
use std::process {process_id, exec_cmd}
use std::io {IO.write_file, IO.read_file}

def item (name : String) (text : String) : TrustItem :=
    let it : TrustItem := { name := name, text := text } in
    it

def state_name (s : TrustState) : String :=
    match s {
        TrustState.trust_ok => "ok",
        TrustState.trust_new => "new",
        TrustState.trust_changed names => String.concat "changed:" (List.intercalate "," names),
    }

#[test]
def test_state_new_ok_and_changed : Bool :=
    let old : List TrustItem := [item "AGENTS.md" "a", item ".weaver/config.toml" "m"] in
    String.beq (state_name (Trust.state Option.none old)) "new"
        && String.beq (state_name (Trust.state (Option.some old) old)) "ok"
        && String.beq (state_name (Trust.state (Option.some old) [item "AGENTS.md" "a"])) "ok"
        && String.beq (state_name (Trust.state (Option.some old) [item "AGENTS.md" "b", item "sub/AGENTS.md" "c"])) "changed:AGENTS.md,sub/AGENTS.md"

#[test]
def test_record_round_trips : Bool :=
    let text : String := Trust.with_root (Trust.parse_record "{}") "/r" [item "AGENTS.md" "line \"one\"\n"] in
    let again : String := Trust.with_root (Trust.parse_record text) "/q" [item "AGENTS.md" "q"] in
    match Trust.recorded (Trust.parse_record again) "/r" {
        Option.some its => String.beq (List.intercalate "|" (List.map (fn (it : TrustItem) => it.text) its)) "line \"one\"\n",
        Option.none => false,
    }

#[test]
def test_an_unknown_root_is_not_recorded : Bool :=
    match Trust.recorded (Trust.parse_record "not json") "/r" {
        Option.none => true,
        Option.some _ => false,
    }

def n (a : TrustAnswer) : String :=
    match a { TrustAnswer.answer_yes => "y", TrustAnswer.answer_view => "v", TrustAnswer.answer_no => "n" }

#[test]
def test_answers : Bool :=
    String.beq (String.concat_list [n (Trust.answer_of " Y\n"), n (Trust.answer_of "view"), n (Trust.answer_of ""), n (Trust.answer_of "sure")]) "yvnn"

#[test]
def test_relative_names : Bool :=
    String.beq (Trust.relative (Path.path "/r") (Path.path "/r/sub/AGENTS.md")) "sub/AGENTS.md"
        && String.beq (Trust.relative (Path.path "/r") (Path.path "/rx/AGENTS.md")) "/rx/AGENTS.md"

#[test]
def test_view_diffs_a_changed_file : Bool :=
    let v : String := Trust.view (Option.some [item "AGENTS.md" "keep\nold\n"]) [item "AGENTS.md" "keep\nnew\n"] in
    String.contains v "AGENTS.md (changed)" && String.contains v "- old" && String.contains v "+ new"

// ── the decision, against a temp project ───────────────────────────────

def root : String := String.concat "/tmp/weaver_trust_test_" (I64.to_string process_id)

def place : SessionPlace :=
    let p : SessionPlace := { cwd := Path.path root, repo := Path.path root } in
    p

def record : Path := Path.path (String.concat root "-home/.weaver/trusted.json")

def setup : IO Unit := do {
    let _ <- exec_cmd "rm" ["-rf", root, String.concat root "-home"];
    let _ <- exec_cmd "mkdir" ["-p", String.concat root "/.weaver"];
    let _ <- IO.write_file (Path.path (String.concat root "/AGENTS.md")) "rules\n";
    let _ <- IO.write_file (Path.path (String.concat root "/.weaver/config.toml")) "mode = \"auto\"\n";
    IO.pure unit
}

def teardown : IO Unit := do {
    let _ <- exec_cmd "rm" ["-rf", root, String.concat root "-home"];
    IO.pure unit
}

def says (line : String) (_ : Unit) : IO (Option String) := IO.pure (Option.some line)
def tty (b : Bool) (_ : Unit) : IO Bool := IO.pure b
def quiet (_ : String) : IO Unit := IO.pure unit

#[test]
def test_no_terminal_means_untrusted_with_a_note : IO Bool := do {
    setup;
    let o <- Trust.decide (Option.some record) (Option.some place) false (tty false) (says "y") quiet;
    teardown;
    IO.pure (Bool.not o.trusted && match o.note { Option.some n => String.contains n "--trust", Option.none => false })
}

#[test]
def test_forced_trusts_without_recording : IO Bool := do {
    setup;
    let o <- Trust.decide (Option.some record) (Option.some place) true (tty false) (says "n") quiet;
    let r <- IO.read_file record;
    teardown;
    IO.pure (o.trusted && match r { Result.err _ => true, Result.ok _ => false })
}

/// A yes is recorded, so the next start does not ask; an edit asks again.
def yes_then_edit : IO Bool := do {
    let first <- Trust.decide (Option.some record) (Option.some place) false (tty true) (says "y") quiet;
    let second <- Trust.decide (Option.some record) (Option.some place) false (tty true) (says "n") quiet;
    let _ <- IO.write_file (Path.path (String.concat root "/AGENTS.md")) "rules, edited\n";
    let third <- Trust.decide (Option.some record) (Option.some place) false (tty true) (says "n") quiet;
    IO.pure (first.trusted && second.trusted && Bool.not third.trusted)
}

#[test]
def test_a_yes_is_remembered_until_a_file_changes : IO Bool := do {
    setup;
    let ok <- yes_then_edit;
    teardown;
    IO.pure ok
}

#[test]
def test_a_project_with_nothing_to_load_is_not_asked : IO Bool := do {
    let _ <- exec_cmd "rm" ["-rf", root];
    let _ <- exec_cmd "mkdir" ["-p", root];
    let o <- Trust.decide (Option.some record) (Option.some place) false (tty true) (says "n") quiet;
    teardown;
    IO.pure o.trusted
}

#[test]
def test_forced_by_flag_or_env_one : Bool :=
    Trust.forced_by true Option.none
        && Trust.forced_by false (Option.some "1")
        && Bool.not (Trust.forced_by false (Option.some "0"))
        && Bool.not (Trust.forced_by false Option.none)
