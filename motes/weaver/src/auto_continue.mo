/// Auto mode's plan-anchored continuation: after a normal turn, when the
/// session is in `auto` and a plan is linked, the next turn starts on its
/// own until the plan reports `done` or `abandoned` (or the turn budget is
/// spent, Esc stopped the turn, or a user line is already queued).
///
/// The prompt starts with `[auto-continue] `. `Classify.intent` skips a
/// `[...]` current line, exactly as it skips weaver's history notes, so the
/// plan's `next_action` never becomes the classifier's idea of what the user
/// asked for.
use shuttle::agent {RunState}
use weaver::commands {WeaverState}
use weaver::policy {Mode}
use weaver::plan_file {PlanDoc, PlanFile.linked, PlanFile.read}
use weaver::store {StoreState}

/// Statuses that end a plan: there is nothing left to continue.
pub def AutoContinue.terminal (status : String) : Bool :=
    Bool.or (String.beq status "done") (String.beq status "abandoned")

def is_auto (m : Mode) : Bool :=
    match m { Mode.auto => true, _ => false }

/// The next turn's line for a plan, or none when it is finished.
pub def AutoContinue.prompt (d : PlanDoc) : String :=
    let next : String :=
        if String.is_empty d.meta.next_action
        then ""
        else String.concat " Next action: " (String.concat d.meta.next_action ".") in
    String.concat_list [
        "[auto-continue] Continue the plan. Status: ", d.meta.status,
        ", completion: ", I64.to_string d.meta.completion, "%.", next,
        " Do the next step. When the whole plan is done, call the plan tool with status \"done\", completion 100, and a changelog note."
    ]

def prompt_of (doc : Option PlanDoc) : Option String :=
    match doc {
        Option.none => Option.none,
        Option.some d =>
            if AutoContinue.terminal d.meta.status
            then Option.none
            else Option.some (AutoContinue.prompt d),
    }

def next_at (path : String) : IO (Option String) := do {
    let doc <- PlanFile.read path;
    IO.pure (prompt_of doc)
}

def next_linked (s : StoreState) : IO (Option String) := do {
    let linked <- PlanFile.linked s;
    match linked {
        Option.none => IO.pure Option.none,
        Option.some path => next_at path,
    }
}

/// Continue only in auto mode, after a normal turn, with budget left and a
/// linked plan whose status is not terminal.
pub def AutoContinue.next (st : WeaverState) (run : RunState) : IO (Option String) :=
    if Bool.not (is_auto st.mode)
    then IO.pure Option.none
    else if run.stopped
    then IO.pure Option.none
    else if I64.lt run.turns_left 1
    then IO.pure Option.none
    else match st.store {
        Option.none => IO.pure Option.none,
        Option.some s => next_linked s,
    }
