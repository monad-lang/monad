/// The `plan` tool: decoding and validation, the metadata change and its
/// changelog line, and -- against a scratch directory -- a call that
/// updates the session's linked plan file.
use init::string {}
use init::transformers {ResultT}
use std::path {Path}
use std::process {process_id, exec_cmd}
use json::json {Json, Json.parse, Json.make_str}
use shuttle::message_types {Content}
use shuttle::tool {ToolImpl}
use weaver::store {StoreState}
use weaver::plan_file {PlanRepo, PlanDoc, PlanMeta, PlanMeta.empty, PlanRepo.capture, PlanFile.read, PlanFile.linked, Stored}
use weaver::plan_tool {PlanCall, PlanTool.decode, PlanTool.apply, PlanTool.line, PlanTool.impl}

def json_of (s : String) : Json :=
    match Json.parse s { Result.ok j => j, Result.err _ => Json.make_str "" }

def tool_decoded (s : String) : Result String PlanCall := PlanTool.decode (json_of s)

def tool_is_err (r : Result String PlanCall) : Bool :=
    match r { Result.err _ => true, Result.ok _ => false }

#[test]
def test_an_empty_call_is_refused : Bool := tool_is_err (tool_decoded "{}")

#[test]
def test_an_unknown_status_is_refused : Bool := tool_is_err (tool_decoded "{\"status\":\"finished\"}")

#[test]
def test_completion_is_bounded : Bool :=
    tool_is_err (tool_decoded "{\"completion\":101}") && tool_is_err (tool_decoded "{\"completion\":-1}")

#[test]
def test_progress_applies_and_keeps_the_rest : Bool :=
    match tool_decoded "{\"completion\":60,\"next_action\":\"wire the dialog\"}" {
        Result.err _ => false,
        Result.ok c =>
            let m : PlanMeta := PlanTool.apply c { PlanMeta.empty with status := "approved", completion := 10 } in
            m.completion == 60 && m.next_action == "wire the dialog" && m.status == "approved",
    }

#[test]
def test_the_line_is_the_note_else_the_change : Bool :=
    match tool_decoded "{\"status\":\"done\",\"completion\":100}" {
        Result.err _ => false,
        Result.ok c => match tool_decoded "{\"note\":\"landed PR A\",\"status\":\"in-progress\"}" {
            Result.err _ => false,
            Result.ok n => PlanTool.line c == "status: done; completion: 100%" && PlanTool.line n == "landed PR A",
        },
    }

def tool_scratch (name : String) : String :=
    String.concat "/tmp/weaver_plantool_" (String.concat (I64.to_string process_id) (String.concat "_" name))

def tool_session_in (base : String) : IO StoreState := do {
    let dir : String := String.concat base "/sessions/s-1";
    let _ <- exec_cmd "rm" ["-rf", base];
    let _ <- exec_cmd "mkdir" ["-p", dir];
    let st : StoreState := { root := Path.path (String.concat base "/sessions"), dir := Path.path dir, id := "s-1" };
    IO.pure st
}

def tool_repo_in (base : String) : PlanRepo :=
    let r : PlanRepo := { root := String.concat base "/plans", dir := String.concat base "/plans/app", commit := false } in
    r

def tool_call (t : ToolImpl) (input : String) : IO (Result String Content) :=
    ResultT.run (t.run "call-1" (json_of input))

def tool_errored (r : Result String Content) : Bool :=
    match r {
        Result.err _ => true,
        Result.ok c => match c { Content.tool_result _ _ e => e, _ => true },
    }

#[test]
def test_without_a_linked_plan_the_tool_errors : IO Bool := do {
    let base : String := tool_scratch "unlinked";
    let st <- tool_session_in base;
    let r <- tool_call (PlanTool.impl (Option.some st) (Option.some (tool_repo_in base))) "{\"status\":\"done\"}";
    IO.pure (tool_errored r)
}

#[test]
def test_the_tool_updates_the_linked_plan : IO Bool := do {
    let base : String := tool_scratch "linked";
    let st <- tool_session_in base;
    let repo : PlanRepo := tool_repo_in base;
    let _ <- PlanRepo.capture repo st "m" "" "# Tool target\n";
    let r <- tool_call (PlanTool.impl (Option.some st) (Option.some repo)) "{\"status\":\"in-progress\",\"completion\":30,\"next_action\":\"step 2\",\"note\":\"step 1 landed\"}";
    let linked <- PlanFile.linked st;
    let d <- read_or linked;
    IO.pure (Bool.not (tool_errored r) && updated_ok d)
}

def read_or (p : Option String) : IO (Option PlanDoc) :=
    match p {
        Option.none => IO.pure Option.none,
        Option.some path => PlanFile.read path,
    }

def updated_ok (d : Option PlanDoc) : Bool :=
    match d {
        Option.none => false,
        Option.some doc => doc.meta.status == "in-progress" && doc.meta.completion == 30
            && doc.meta.next_action == "step 2" && String.contains doc.body "step 1 landed",
    }
