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
use weaver::policy {Mode, Mode.is_auto}
use weaver::plan_file {PlanDoc, PlanFile.linked, PlanFile.read}
use weaver::store {StoreState}
use std::ref {Ref, Ref.add_i64, Ref.set}

/// Statuses that end a plan: there is nothing left to continue.
pub def AutoContinue.terminal (status : String) : Bool :=
    Bool.or (String.beq status "done") (String.beq status "abandoned")

/// The next turn's line for a plan, or none when it is finished.
pub def AutoContinue.prompt (d : PlanDoc) : String :=
    let next : String :=
        if String.is_empty d.meta.next_action
        then ""
        else String.concat " Next action: " (String.concat d.meta.next_action ".") in
    String.concat_list [
        "[auto-continue] Continue the plan. Status: ", d.meta.status,
        ", completion: ", I64.to_string d.meta.completion, "%.", next,
        " Do the next step. You are running unattended: if something is unclear, choose the most reasonable option, record the assumption in the plan, and continue. When the whole plan is done, call the plan tool with status \"done\", completion 100, and a changelog note."
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
    if Bool.not (Mode.is_auto st.mode)
    then IO.pure Option.none
    else if run.stopped
    then IO.pure Option.none
    else if I64.lt run.turns_left 1
    then IO.pure Option.none
    else match st.store {
        Option.none => IO.pure Option.none,
        Option.some s => next_linked s,
    }

// ── failed-turn retry ───────────────────────────────────────────────────

/// How many consecutive transient failures auto-with-plan retries before
/// leaving the turn to the human. A successful turn resets the count.
pub def AutoContinue.max_failures : I64 := 2

pub def AutoContinue.record_failure (st : WeaverState) : IO (Option I64) :=
    match st.auto_failures {
        Option.none => IO.pure Option.none,
        Option.some r => do {
            let n <- Ref.add_i64 r 1;
            IO.pure (Option.some n)
        },
    }

pub def AutoContinue.clear_failures (st : WeaverState) : IO Unit :=
    match st.auto_failures {
        Option.none => IO.pure unit,
        Option.some r => Ref.set r 0,
    }

// ── the budget stop line ────────────────────────────────────────────────

/// Whether a linked plan still has work (status not terminal).
def plan_active (s : StoreState) : IO Bool := do {
    let linked <- PlanFile.linked s;
    match linked {
        Option.none => IO.pure false,
        Option.some path => active_at path,
    }
}

def active_at (path : String) : IO Bool := do {
    let doc <- PlanFile.read path;
    match doc {
        Option.none => IO.pure false,
        Option.some d => IO.pure (Bool.not (AutoContinue.terminal d.meta.status)),
    }
}

/// A line for the human when auto-continue stopped only because the turn
/// budget is spent with a plan still unfinished; none for every other stop.
pub def AutoContinue.budget_note (st : WeaverState) (run : RunState) : IO (Option String) :=
    if Bool.not (Mode.is_auto st.mode)
    then IO.pure Option.none
    else if run.stopped
    then IO.pure Option.none
    else if I64.gt run.turns_left 0
    then IO.pure Option.none
    else match st.store {
        Option.none => IO.pure Option.none,
        Option.some s => budget_note_for run s,
    }

def budget_note_for (run : RunState) (s : StoreState) : IO (Option String) := do {
    let active <- plan_active s;
    if active
    then IO.pure (Option.some (String.concat_list ["[auto] turn budget spent (turns ",
        I64.to_string run.session.turns, ") -- the plan is not done; raise it with /budget <n>"]))
    else IO.pure Option.none
}

// ── the linked plan, as classifier context ──────────────────────────────

/// The linked plan's title, status and next action, shaped for the
/// classifier's intent (completion % is excluded so the verdict cache key
/// stays stable within one step). Empty when no plan is linked.
pub def AutoContinue.plan_context (store : Option StoreState) : IO String :=
    match store {
        Option.none => IO.pure "",
        Option.some s => context_linked s,
    }

def context_linked (s : StoreState) : IO String := do {
    let linked <- PlanFile.linked s;
    match linked {
        Option.none => IO.pure "",
        Option.some path => context_at path,
    }
}

def context_at (path : String) : IO String := do {
    let doc <- PlanFile.read path;
    match doc {
        Option.none => IO.pure "",
        Option.some d => IO.pure (context_of d),
    }
}

def context_of (d : PlanDoc) : String :=
    let title : String := if String.is_empty d.meta.title then "(untitled)" else d.meta.title in
    let next : String := if String.is_empty d.meta.next_action then "" else String.concat "; next action: " d.meta.next_action in
    String.concat_list ["title: ", title, "; status: ", d.meta.status, next]
