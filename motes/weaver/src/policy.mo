/// Weaver's approval policy -- weaver.md Phase 2: the mode vocabulary,
/// the decision each mode maps a capability to, and the mode state
/// machine, all PURE. The policy is testable with no I/O; the
/// interactive gate (`gate.mo`) is the only piece that talks, and it
/// renders what this table decides.
///
/// The modes mirror Claude Code's: `manual` asks for everything;
/// `plan` refuses everything but reads (the agent produces a plan
/// document, the user approves, the mode drops); `allow_edit` lets
/// file edits through and still asks for code and network; `auto` is
/// the trust setting the status bar never stops warning about.
use shuttle::gate {Capability}

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

/// The decision table, the whole policy in one function. Every cell
/// of `Capability x Mode` is pinned by `tests/policy_tests.mo` -- a
/// change here without that file changing is a contradiction.
pub def Policy.decide (cap : Capability) (mode : Mode) : Decision :=
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
                _ => Decision.allow,
            },
        Mode.auto => Decision.allow,
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

/// The status bar's warning state: on exactly when the mode is `auto`.
/// `auto` is a trust setting, not a sandbox -- the UI must never let
/// it pass unremarked.
pub def Mode.warns_auto (m : Mode) : Bool :=
    match m {
        Mode.auto => true,
        _ => false,
    }

/// The display name, and the string `/mode` accepts.
pub def Mode.show (m : Mode) : String :=
    match m {
        Mode.manual => "manual",
        Mode.plan => "plan",
        Mode.allow_edit => "allow_edit",
        Mode.auto => "auto",
    }
