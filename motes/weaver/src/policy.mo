/// Weaver's approval policy -- weaver.md Phase 2: the mode vocabulary,
/// the decision each mode maps a capability to, and the mode state
/// machine, all PURE. The policy is testable with no I/O; the
/// interactive gate (`gate.mo`) is the only piece that talks, and it
/// renders what this table decides.
///
/// The modes mirror Claude Code's: `manual` asks for everything;
/// `plan` refuses everything but reads (the agent produces a plan
/// document, the user approves, the mode drops); `allow_edit` lets
/// file edits through and still asks for code and network; `auto` runs
/// unattended (dangers are refused, not held; the `[auto]` chip is red).
use shuttle::gate {Capability}
use weaver::assess {Assessment, Reach.is_inside, Reach.is_scratch}

/// The approval mode -- what the user controls, one `/mode` away.
pub type Mode {
    manual,
    plan,
    allow_edit,
    auto,
}

/// What the policy says about one pick. `ask` is what the interactive
/// gate turns into a prompt; a headless consumer treats `ask` as a
/// refusal named the same way the plan mode's is.
pub type Decision {
    allow,
    ask,
    refuse (reason : String),
}

/// Tools that only change weaver's own session state (the todo list) or
/// ask the human a question run in every mode without a prompt: there is
/// nothing to approve.
pub def Policy.unguarded (tool : String) : Bool :=
    Bool.or (String.beq tool "todo_write") (String.beq tool "ask")

/// The decision table, the whole policy in one function. Every cell
/// of `Capability x Mode`, and each cell the assessment splits, is pinned
/// by `tests/policy_tests.mo` -- a change here without that file changing
/// is a contradiction. `a` is where the pick reaches (`Assess.pick`):
/// `allow_edit` lets an edit through only inside the workspace, and `auto`
/// still asks before a destructive pick or a write outside the workspace.
pub def Policy.decide (cap : Capability) (mode : Mode) (a : Assessment) : Decision :=
    match mode {
        Mode.manual => Decision.ask,
        Mode.plan =>
            match cap {
                Capability.read => Decision.allow,
                _ => Decision.refuse "plan mode: only read tools run; produce a plan, then switch with /mode",
            },
        Mode.allow_edit =>
            match cap {
                Capability.exec => Decision.ask,
                Capability.net => Decision.ask,
                Capability.write => if Reach.is_inside a.scope then Decision.allow else Decision.ask,
                Capability.read => Decision.allow,
            },
        Mode.auto =>
            // Auto is unattended: a flagged pick is REFUSED, never held for a
            // human. The refusal is a tool result the model reads and adapts
            // to; only `auto_on_danger = ask` (the classifier's dangerous
            // verdict, below) may still prompt.
            match a.danger {
                Option.some reason => Decision.refuse (String.concat "auto mode: refused a dangerous command: " reason),
                Option.none => match a.outside_write {
                    Option.some reason => Decision.refuse (String.concat "auto mode: refused: " reason),
                    Option.none => Decision.allow,
                },
            },
    }

// ── Auto mode's classifier ──────────────────────────────────────────────

/// A classifier model's reading of one pick (`classify.mo` asks for it).
pub type Verdict {
    safe,
    dangerous (reason : String),
}

/// What auto mode does with a `dangerous` verdict: refuse it (the model
/// reads the reason and adapts; the default) or ask the human. The
/// constructor names are distinct on purpose: a nullary `deny` beside
/// shuttle's `Approval.deny (reason)` is the shared-name match miscompile
/// (`plans/implementations/2026-11-05-shared-ctor-name-match-miscompile.md`)
/// on every nightly without the fix.
pub type AutoDanger {
    refuse_it,
    ask_human,
}

pub def AutoDanger.parse (s : String) : Option AutoDanger :=
    if s == "deny" then Option.some AutoDanger.refuse_it
    else if s == "ask" then Option.some AutoDanger.ask_human
    else Option.none

pub def AutoDanger.show (d : AutoDanger) : String :=
    match d {
        AutoDanger.refuse_it => "deny",
        AutoDanger.ask_human => "ask",
    }

/// The picks auto mode classifies: code that reaches OUTSIDE the workspace
/// (or somewhere it cannot resolve), the network, and a write outside the
/// workspace. Reads, in-workspace writes, in-workspace commands and picks
/// that stay in the session scratch dir need no verdict -- build/test work
/// in the repo is exactly what auto mode is for, and a classifier call per
/// command made it slow and unreliable. The static danger scan (the safety
/// net) still refuses flagged commands; `auto_safety = false` turns that
/// net off too.
pub def Policy.classified (cap : Capability) (a : Assessment) : Bool :=
    match cap {
        Capability.exec => Bool.not (Reach.is_inside a.scope),
        Capability.net => true,
        Capability.write => match a.outside_write { Option.some _ => true, Option.none => false },
        Capability.read => false,
    }

/// Auto mode with a verdict. `safe` runs, even a pick the static scanner
/// flagged (its flag was in the classifier's prompt); `dangerous` is
/// refused or asked per `on_danger`; no verdict (the call failed or timed
/// out) falls back to the static rule, so a failure is never less safe
/// than auto mode without a classifier. Every cell is pinned by
/// `tests/policy_tests.mo`.
pub def Policy.decide_auto (cap : Capability) (a : Assessment) (v : Option Verdict) (on_danger : AutoDanger) : Decision :=
    match v {
        Option.some verdict => match verdict {
            Verdict.safe => Decision.allow,
            Verdict.dangerous reason => match on_danger {
                AutoDanger.refuse_it => Decision.refuse (String.concat "auto mode: the classifier blocked this: " reason),
                AutoDanger.ask_human => Decision.ask,
            },
        },
        Option.none => Policy.decide cap Mode.auto a,
    }

// ── The mode state machine ──────────────────────────────────────────────

/// The `/mode` vocabulary: what the user types is what `Mode.show`
/// prints, and `parse (show m)` round-trips for every mode (pinned by
/// test).
pub def Mode.parse (s : String) : Option Mode :=
    if s == "manual" then Option.some Mode.manual
    else if s == "plan" then Option.some Mode.plan
    else if s == "allow_edit" then Option.some Mode.allow_edit
    else if s == "auto" then Option.some Mode.auto
    else Option.none

/// The startup mode: the `--mode` flag when given (a bad value is a
/// config error, never a silent fallback), else the settings' mode, else
/// manual.
pub def Mode.resolve (flag : Option String) (from_settings : Option Mode) : Result String Mode :=
    match flag {
        Option.some s => match Mode.parse s {
            Option.some m => Result.ok m,
            Option.none => Result.err "mode must be manual, plan, allow_edit or auto",
        },
        Option.none => Result.ok (match from_settings { Option.some m => m, Option.none => Mode.manual }),
    }

pub def Mode.is_auto (m : Mode) : Bool :=
    match m {
        Mode.auto => true,
        _ => false,
    }

/// The `/plan approve` drop -- the one CONSTRAINED transition: plan
/// mode ends at the mode the approving user names (`manual` for "go",
/// `allow_edit` for "go and let it edit"), and any other mode has no
/// plan to approve, so it stays put. `/mode <m>` is the unconstrained
/// edge: any mode is one command away, by design.
pub def Mode.approve_plan (target : Mode) (m : Mode) : Mode :=
    match m {
        Mode.plan => target,
        _ => m,
    }

/// The TUI's Tab key: the unconstrained `/mode`-equivalent edge,
/// cycling through every mode in the table's own display order
/// (manual -> plan -> allow_edit -> auto -> manual). Plain cycling, not
/// `/plan approve`'s constrained landing -- Tab is a shortcut for
/// `/mode <next>`, nothing more guarded.
pub def Mode.cycle (m : Mode) : Mode :=
    match m {
        Mode.manual => Mode.plan,
        Mode.plan => Mode.allow_edit,
        Mode.allow_edit => Mode.auto,
        Mode.auto => Mode.manual,
    }

/// The display name, and the string `/mode` accepts.
pub def Mode.show (m : Mode) : String :=
    match m {
        Mode.manual => "manual",
        Mode.plan => "plan",
        Mode.allow_edit => "allow_edit",
        Mode.auto => "auto",
    }
