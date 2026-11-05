/// The task registry and the /tasks monitor's pure halves: subagent
/// records, ordering, the running count, exit notes, and how a dialog
/// choice maps to the next view or action.
use weaver::tasks {
    TaskEntry, TaskKind, Tasks.agent_of_json, Tasks.sort, Tasks.running_count, Tasks.running_ids,
    Tasks.exit_notes, Tasks.line,
}
use weaver::tui_app {
    TuiApp.monitor_list_next, TuiApp.detail_action, TuiApp.detail_options, TuiApp.with_task_notes,
    TuiApp.monitor_dialog, TuiApp.monitor_refreshed,
    MonitorView, DetailAction,
}
use tui::widgets::dialog {DialogStep, DialogModel}
use std::list {List.length, List.intercalate}

def proc_task (id : String) (running : Bool) (status : String) (started : I64) : TaskEntry :=
    let t : TaskEntry := { kind := TaskKind.task_proc, id := id, label := String.concat "cmd " id, status := status,
        running := running, started_ns := started, proc := Option.none, summary := "" } in
    t

def agent_task (id : String) (running : Bool) : TaskEntry :=
    let t : TaskEntry := { kind := TaskKind.task_agent, id := id, label := "find the bug", status := if running then "running" else "done",
        running := running, started_ns := 5, proc := Option.none, summary := "" } in
    t

#[partial]
def ids (ts : List TaskEntry) : String :=
    List.intercalate "," (List.map (fn (t : TaskEntry) => t.id) ts)

#[test]
def test_agent_record_decodes : Bool :=
    match Tasks.agent_of_json "a-1" "{\"prompt\": \"find the bug\\nin detail\", \"status\": \"running\", \"started_ns\": 7, \"summary\": \"\"}" {
        Option.none => false,
        Option.some t => t.running && String.beq t.label "find the bug" && t.started_ns == 7,
    }

#[test]
def test_newest_first_and_running_count : Bool :=
    let ts : List TaskEntry := Tasks.sort [proc_task "p-1" true "running" 1, proc_task "p-3" false "exited (0)" 3, agent_task "a-2" true] in
    String.beq (ids ts) "a-2,p-3,p-1" && Tasks.running_count ts == 2

/// A process that was running and is not any more gets a note; a still
/// running one, an agent, and one never seen running get none.
#[test]
def test_exit_notes : Bool :=
    let before : List String := Tasks.running_ids [proc_task "p-1" true "running" 1, proc_task "p-2" true "running" 2, agent_task "a-1" true] in
    let now : List TaskEntry := [proc_task "p-1" false "exited (0)" 1, proc_task "p-2" true "running" 2,
        agent_task "a-1" false, proc_task "p-9" false "killed" 9] in
    let notes : List String := Tasks.exit_notes before now in
    List.length notes == 1
        && String.beq (List.intercalate "" notes) "[background task p-1 exited (0): cmd p-1]"

#[test]
def test_line_marks_running : Bool :=
    String.starts_with "● running" (Tasks.line 5 (proc_task "p-1" true "running" 5))
        && String.contains (Tasks.line 5 (agent_task "a-1" false)) "agent: find the bug"

/// List view: a row opens its task, Refresh keeps the list, Close and Esc end.
#[test]
def test_list_choices : Bool :=
    let ts : List TaskEntry := [proc_task "p-1" true "running" 1, proc_task "p-2" false "killed" 2] in
    (match TuiApp.monitor_list_next ts (DialogStep.choose 1) { MonitorView.mon_detail id => String.beq id "p-2", _ => false })
        && (match TuiApp.monitor_list_next ts (DialogStep.choose 2) { MonitorView.mon_list _ => true, _ => false })
        && (match TuiApp.monitor_list_next ts (DialogStep.choose 3) { MonitorView.mon_closed => true, _ => false })
        && (match TuiApp.monitor_list_next ts DialogStep.cancel { MonitorView.mon_closed => true, _ => false })

/// Detail view: Kill only while running, then Refresh and Back.
#[test]
def test_detail_choices : Bool :=
    let live : TaskEntry := proc_task "p-1" true "running" 1 in
    let done : TaskEntry := proc_task "p-2" false "exited (0)" 2 in
    List.length (TuiApp.detail_options live) == 3
        && List.length (TuiApp.detail_options done) == 2
        && (match TuiApp.detail_action live (DialogStep.choose 0) { DetailAction.detail_kill => true, _ => false })
        && (match TuiApp.detail_action live (DialogStep.choose 1) { DetailAction.detail_refresh => true, _ => false })
        && (match TuiApp.detail_action done (DialogStep.choose 0) { DetailAction.detail_refresh => true, _ => false })
        && (match TuiApp.detail_action done DialogStep.cancel { DetailAction.detail_back => true, _ => false })

#[test]
def test_notes_ride_the_next_message : Bool :=
    String.beq (TuiApp.with_task_notes List.empty "go") "go"
        && String.beq (TuiApp.with_task_notes ["[background task p-1 exited (0): make]"] "go") "go\n\n[background task p-1 exited (0): make]"

/// A refresh that finds a new task keeps the selected task selected: it
/// moved down one row. The selection never runs past the last option.
#[test]
def test_monitor_refresh_keeps_the_selected_task : Bool :=
    let before : List TaskEntry := [proc_task "p-1" true "running" 1, proc_task "p-0" true "running" 0] in
    let after : List TaskEntry := List.cons (proc_task "p-2" true "running" 2) before in
    let old : DialogModel := { (TuiApp.monitor_dialog 5 60 before) with selected := 1 } in
    let moved : DialogModel := TuiApp.monitor_refreshed old (TuiApp.monitor_dialog 5 60 after) 1 in
    let far : DialogModel := TuiApp.monitor_refreshed { old with selected := 9 } (TuiApp.monitor_dialog 5 60 before) 0 in
    moved.selected == 2 && far.selected == 3
