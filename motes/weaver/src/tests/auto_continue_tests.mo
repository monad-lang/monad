/// `AutoContinue` -- weaver's plan-anchored unattended loop: when it may
/// continue, the prompt it sends, and the statuses that end a plan.
use shuttle::agent {RunState, silent_sleep, silent_usage, silent_stop, silent_inbox, silent_side_spend}
use shuttle::context {usage_zero}
use shuttle::gate {Gate}
use shuttle::message {Usage}
use shuttle::provider {ProviderConfig, Wire}
use shuttle::registry {ToolRegistry}
use shuttle::session {Session}
use weaver::auto_continue {AutoContinue.terminal, AutoContinue.prompt, AutoContinue.next, AutoContinue.budget_note, AutoContinue.finish_note, AutoContinue.delta_has_tool}
use shuttle::message_types {StopReason, Content, Role}
use shuttle::message {Message}
use weaver::commands {WeaverState}
use weaver::policy {Mode}
use weaver::store {StoreState}
use weaver::plan_file {PlanDoc, PlanMeta, PlanMeta.empty, PlanFile.render, PlanFile.link}
use std::test {Test.write_fixture}
use std::path {Path}
use std::map {BTreeMap}
use json::json {Json}
use std::process {process_id, exec_cmd}

def mock_config : ProviderConfig :=
    { base_url := "mock", model := "mock", api_key_env := "WEAVER_UNUSED_KEY", api_key := Option.none, max_tokens := 8, wire := Wire.mock, thinking := false }

def session_of : Session :=
    { config := mock_config, system_prompt := "test", tools := List.empty, history := List.empty, turns := 0, spent := usage_zero }

def run_of : RunState :=
    { session := session_of, reg := ToolRegistry.empty, turns_left := 10, emit := fn (_ : String) => IO.pure unit, gate := Gate.auto, always := List.empty, retries := 1, sleep_ms := silent_sleep, on_usage := silent_usage, should_stop := silent_stop, inbox := silent_inbox, side_spend := silent_side_spend, stopped := false, last_stop := Option.none }

def store_at (dir : String) : StoreState :=
    let s : StoreState := { root := Path.path dir, dir := Path.path dir, id := "s-1" } in
    s

def state_of (mode : Mode) (store : Option StoreState) : WeaverState :=
    { run := run_of, mode := mode, provider := "mock", budget := 10, context_window := 128000, compact_at := 80, plan := Option.none, last_context := 0, grants := Option.none, place := Option.none, mcps := List.empty, keys := BTreeMap.empty, catalog := BTreeMap.empty, quit := false, fatal := Option.none, colors := false, name := Option.none, trusted := false, instructions := List.empty, instr_seen := Option.none, store := store }

def meta_of : PlanMeta :=
    { PlanMeta.empty with title := "Tracked", status := "in-progress", completion := 40, next_action := "write the test" }

def doc_of (m : PlanMeta) : PlanDoc :=
    let d : PlanDoc := { meta := m, body := "# Body\n" } in
    d

#[test]
def test_terminal_statuses : Bool :=
    AutoContinue.terminal "done" && AutoContinue.terminal "abandoned"
        && Bool.not (AutoContinue.terminal "draft")
        && Bool.not (AutoContinue.terminal "approved")
        && Bool.not (AutoContinue.terminal "in-progress")

#[test]
def test_prompt_names_the_status_and_next_action : Bool :=
    let p : String := AutoContinue.prompt (doc_of meta_of) in
    String.starts_with "[auto-continue]" p
        && String.contains p "in-progress"
        && String.contains p "40%"
        && String.contains p "write the test"
        && String.contains p "status \"done\""

#[test]
def test_prompt_omits_an_empty_next_action : Bool :=
    let m : PlanMeta := { meta_of with next_action := "" } in
    Bool.not (String.contains (AutoContinue.prompt (doc_of m)) "Next action:")

#[test]
def test_next_is_off_outside_auto : IO Bool := do {
    let r <- AutoContinue.next (state_of Mode.manual Option.none) run_of;
    return (match r { Option.none => true, _ => false })
}

#[test]
def test_next_needs_a_store : IO Bool := do {
    let r <- AutoContinue.next (state_of Mode.auto Option.none) run_of;
    return (match r { Option.none => true, _ => false })
}

#[test]
def test_next_is_off_after_a_stop : IO Bool := do {
    let stopped : RunState := { run_of with stopped := true };
    let r <- AutoContinue.next (state_of Mode.auto Option.none) stopped;
    return (match r { Option.none => true, _ => false })
}

#[test]
def test_next_is_off_when_the_budget_is_spent : IO Bool := do {
    let spent : RunState := { run_of with turns_left := 0 };
    let r <- AutoContinue.next (state_of Mode.auto Option.none) spent;
    return (match r { Option.none => true, _ => false })
}

def temp_root : String :=
    String.concat "/tmp/weaver_auto_continue_" (I64.to_string process_id)

#[test]
def test_next_reads_a_linked_plan : IO Bool := do {
    let _ <- exec_cmd "rm" ["-rf", temp_root];
    let _ <- exec_cmd "mkdir" ["-p", temp_root];
    let path : String := String.concat temp_root "/plan.md";
    let _ <- Test.write_fixture (Path.path path) (PlanFile.render (doc_of meta_of));
    let s : StoreState := store_at temp_root;
    let _ <- PlanFile.link s path;
    let r <- AutoContinue.next (state_of Mode.auto (Option.some (store_at temp_root))) run_of;
    let _ <- exec_cmd "rm" ["-rf", temp_root];
    return (match r {
        Option.some p => String.contains p "Continue the plan" && String.contains p "write the test",
        Option.none => false,
    })
}

#[test]
def test_next_stops_for_a_done_plan : IO Bool := do {
    let _ <- exec_cmd "rm" ["-rf", temp_root];
    let _ <- exec_cmd "mkdir" ["-p", temp_root];
    let path : String := String.concat temp_root "/plan.md";
    let done : PlanMeta := { meta_of with status := "done", completion := 100 };
    let _ <- Test.write_fixture (Path.path path) (PlanFile.render (doc_of done));
    let s : StoreState := store_at temp_root;
    let _ <- PlanFile.link s path;
    let r <- AutoContinue.next (state_of Mode.auto (Option.some (store_at temp_root))) run_of;
    let _ <- exec_cmd "rm" ["-rf", temp_root];
    return (match r { Option.none => true, _ => false })
}

// ── the stop lines ─────────────────────────────────────────────────────

/// The budget line is for EVERY mode: a manual-mode run that hits the cap
/// used to stop after a tool result with no reason.
/// A run whose budget is spent (a plain body: `{ x with .. }` is a
/// plain-body form).
def spent_run : RunState :=
    let r : RunState := { run_of with turns_left := 0 } in
    r

#[test]
def test_budget_note_fires_in_manual_mode : IO Bool := do {
    let note <- AutoContinue.budget_note (state_of Mode.manual Option.none) spent_run;
    return (match note {
        Option.some s => String.contains s "turn budget spent",
        Option.none => false,
    })
}

#[test]
def test_budget_note_is_quiet_with_budget_left : IO Bool := do {
    let note <- AutoContinue.budget_note (state_of Mode.manual Option.none) run_of;
    return (match note { Option.none => true, Option.some _ => false })
}

/// A truncated reply is a normal finish, but never a silent one.
def cut_run : RunState :=
    let r : RunState := { run_of with last_stop := Option.some StopReason.max_tokens } in
    r

def refused_run : RunState :=
    let r : RunState := { run_of with last_stop := Option.some StopReason.refusal } in
    r

#[test]
def test_finish_note_names_truncation_and_refusal : Bool :=
    let cut : RunState := cut_run in
    let refused : RunState := refused_run in
    (match AutoContinue.finish_note cut { Option.some s => String.contains s "cut off", Option.none => false })
        && (match AutoContinue.finish_note refused { Option.some s => String.contains s "refused", Option.none => false })
        && (match AutoContinue.finish_note run_of { Option.none => true, Option.some _ => false })

/// "Progress" is a tool call anywhere in the turn's delta.
#[test]
def test_delta_has_tool : Bool :=
    let call : Content := Content.tool_use "c1" "read" (Json.make_object BTreeMap.empty) in
    let text : Content := Content.text "hi" in
    let with_tool : Message := { role := Role.assistant, content := [text, call] } in
    let without : Message := { role := Role.assistant, content := [text] } in
    Bool.and (AutoContinue.delta_has_tool [with_tool]) (Bool.not (AutoContinue.delta_has_tool [without]))
