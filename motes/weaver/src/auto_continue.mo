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
use std::ref {Ref, Ref.add_i64, Ref.get, Ref.set}
use shuttle::message {Message}
use shuttle::message_types {Content, StopReason}

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
            else if String.is_empty d.meta.next_action
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

/// A line for the human when a turn ended only because the turn budget is
/// spent -- in EVERY mode: a manual-mode run that hits the cap otherwise
/// stops after a tool result with no reason. The linked-plan sentence is
/// added only when a plan is still unfinished.
pub def AutoContinue.budget_note (st : WeaverState) (run : RunState) : IO (Option String) :=
    if run.stopped
    then IO.pure Option.none
    else if I64.gt run.turns_left 0
    then IO.pure Option.none
    else match st.store {
        Option.none => IO.pure (Option.some budget_line),
        Option.some s => budget_note_for run s,
    }

def budget_line : String :=
    "[turn budget spent] raise it with /budget <n>, or /clear to start over"

def budget_note_for (run : RunState) (s : StoreState) : IO (Option String) := do {
    let active <- plan_active s;
    if active
    then IO.pure (Option.some (String.concat_list [budget_line,
        " (the linked plan is not done)"]))
    else IO.pure (Option.some budget_line)
}

// ── the two other stop lines ────────────────────────────────────────────

/// The reply was cut off by the output-token limit (or refused): a normal
/// finish, but never a silent one.
pub def AutoContinue.finish_note (run : RunState) : Option String :=
    match run.last_stop {
        Option.none => Option.none,
        Option.some s =>
            if StopReason.is_truncated s
            then Option.some "[reply cut off at the output limit] raise it with /settings max_tokens (a reasoning model spends the budget before it writes)"
            else if StopReason.is_refusal s
            then Option.some "[the model refused this turn]"
            else Option.none,
    }

/// A linked, unfinished plan whose `next_action` is empty cannot drive a
/// continuation; say so instead of silently ending the chain.
pub def AutoContinue.stall_note (st : WeaverState) : IO (Option String) :=
    match st.store {
        Option.none => IO.pure Option.none,
        Option.some s => stall_linked s,
    }

def stall_linked (s : StoreState) : IO (Option String) := do {
    let linked <- PlanFile.linked s;
    match linked {
        Option.none => IO.pure Option.none,
        Option.some path => stall_at path,
    }
}

def stall_at (path : String) : IO (Option String) := do {
    let doc <- PlanFile.read path;
    match doc {
        Option.none => IO.pure Option.none,
        Option.some d =>
            if Bool.or (AutoContinue.terminal d.meta.status) (Bool.not (String.is_empty d.meta.next_action))
            then IO.pure Option.none
            else IO.pure (Option.some (String.concat_list ["[auto] the linked plan has no next action (status ",
                d.meta.status, ", ", I64.to_string d.meta.completion,
                "%) -- not continuing; revise it with /plan or take over"]))
    }
}

// ── the no-progress guard ───────────────────────────────────────────────

/// Consecutive auto turns with no tool call and an unchanged plan before
/// the chain stops. A truncated reasoning turn is exactly this shape.
pub def AutoContinue.max_no_progress : I64 := 3

#[partial]
def has_tool_in (cs : List Content) : Bool :=
    match cs {
        List.empty => false,
        List.cons c rest => match c { Content.tool_use _ _ _ => true, _ => has_tool_in rest },
    }

#[partial]
pub def AutoContinue.delta_has_tool (ms : List Message) : Bool :=
    match ms {
        List.empty => false,
        List.cons m rest =>
            if has_tool_in m.content then true else AutoContinue.delta_has_tool rest,
    }

def fingerprint_of (d : PlanDoc) : String :=
    String.concat_list [d.meta.status, "|", I64.to_string d.meta.completion, "|", d.meta.next_action]

def linked_fingerprint (s : StoreState) : IO (Option String) := do {
    let linked <- PlanFile.linked s;
    match linked {
        Option.none => IO.pure Option.none,
        Option.some path => do {
            let doc <- PlanFile.read path;
            match doc {
                Option.none => IO.pure Option.none,
                Option.some d => IO.pure (Option.some (fingerprint_of d)),
            }
        },
    }
}

pub def AutoContinue.reset_progress (st : WeaverState) : IO Unit :=
    match st.auto_progress {
        Option.none => IO.pure unit,
        Option.some r => Ref.set r (Pair.pair 0 ""),
    }

/// One successful turn's progress bookkeeping. A turn made progress when
/// it called a tool OR the linked plan's (status, completion, next_action)
/// changed; `max_no_progress` unchanged turns stop the chain.
pub def AutoContinue.note_turn (st : WeaverState) (run : RunState) (delta : List Message) : IO (Option String) :=
    match st.auto_progress {
        Option.none => IO.pure Option.none,
        Option.some r => note_turn_at r run delta st,
    }

def note_turn_at (r : Ref (Pair I64 String)) (run : RunState) (delta : List Message) (st : WeaverState) : IO (Option String) := do {
    if Bool.not (Mode.is_auto st.mode)
    then do { let _ <- Ref.set r (Pair.pair 0 ""); IO.pure Option.none }
    else if run.stopped
    then IO.pure Option.none
    else if I64.lt run.turns_left 1
    then IO.pure Option.none
    else match st.store {
        Option.none => do { let _ <- Ref.set r (Pair.pair 0 ""); IO.pure Option.none },
        Option.some s => do {
            let fp <- linked_fingerprint s;
            match fp {
                Option.none => do { let _ <- Ref.set r (Pair.pair 0 ""); IO.pure Option.none },
                Option.some text => do {
                    let prev <- Ref.get r;
                    let had : Bool := AutoContinue.delta_has_tool delta;
                    // No baseline yet (`fresh`): record the fingerprint, but
                    // the turn still counts when it made no tool call, so the
                    // line's "after N turns" is the number actually spent.
                    // Only a plan CHANGE is progress. The empty sentinel is
                    // never COMPARED: `String.beq` on it dereferences a null
                    // payload and crashes the driver.
                    let fresh : Bool := String.is_empty prev.second;
                    let same : Bool := if fresh then false else String.beq prev.second text;
                    let moved : Bool := Bool.and (Bool.not fresh) (Bool.not same);
                    if Bool.or had moved
                    then do { let _ <- Ref.set r (Pair.pair 0 text); IO.pure Option.none }
                    else do {
                        let k : I64 := prev.first + 1;
                        let _ <- Ref.set r (Pair.pair k text);
                        if I64.lt (AutoContinue.max_no_progress - 1) k
                        then IO.pure (Option.some (String.concat_list ["[auto] stopped after ",
                            I64.to_string AutoContinue.max_no_progress,
                            " turns with no tool call and no plan change -- take over, or revise the plan with /plan"]))
                        else IO.pure Option.none
                    }
                },
            }
        },
    }
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
