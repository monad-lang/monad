/// The policy engine tests -- weaver.md Phase 2's acceptance: every
/// cell of `Capability x Mode` pinned, the mode state machine's
/// transitions pinned, the `auto` warning flag pinned. All pure, no
/// I/O -- the point of the decision table being a function.
use weaver::policy {
    Mode, Decision, Policy.decide, Policy.decide_auto, Policy.classified, Verdict, AutoDanger,
    Mode.parse, Mode.approve_plan, Mode.resolve, Mode.is_auto, Mode.show, Mode.cycle,
}
use shuttle::gate {Capability}
use weaver::assess {Assessment, Reach}
use std::path {Path}

/// Structural equality on `Decision`, payload included: the refusal
/// reason is part of the contract (the model and the user both read it).
def decision_eq (a : Decision) (b : Decision) : Bool :=
    match a {
        Decision.allow => match b { Decision.allow => true, _ => false },
        Decision.ask => match b { Decision.ask => true, _ => false },
        Decision.refuse r => match b { Decision.refuse r2 => r == r2, _ => false },
    }

/// A pick inside the workspace, flagged by no rule: the plain cell.
def plain : Assessment :=
    let a : Assessment := { scope := Reach.inside, danger := Option.none, outside_write := Option.none } in
    a

def reaching (scope : Reach) : Assessment :=
    let a : Assessment := { scope := scope, danger := Option.none, outside_write := Option.none } in
    a

/// One cell of the table: the decision for (cap, mode) is `expected`.
def cell (cap : Capability) (mode : Mode) (expected : Decision) : Bool :=
    decision_eq (Policy.decide cap mode plain) expected

/// A cell the assessment splits.
def cell_at (cap : Capability) (mode : Mode) (a : Assessment) (expected : Decision) : Bool :=
    decision_eq (Policy.decide cap mode a) expected

/// The plan-mode refusal reason, exactly as `Policy.decide` spells it.
def plan_refusal : String :=
    "plan mode: only read tools run; produce a plan, then switch with /mode"

/// The decision table, all 16 cells (Capability x Mode), one test per
/// mode. Deliberately four short chains instead of one 16-term `&&`: the
/// self-hosted checker's cost grows sharply with chain length (a 16-term
/// chain of `cell` calls took minutes; four 4-term chains take seconds).
#[test]
def test_decision_table_manual : Bool :=
    // manual asks for everything
    cell Capability.read Mode.manual Decision.ask
        && cell Capability.write Mode.manual Decision.ask
        && cell Capability.exec Mode.manual Decision.ask
        && cell Capability.net Mode.manual Decision.ask

#[test]
def test_decision_table_plan : Bool :=
    // plan allows reads, refuses the rest
    cell Capability.read Mode.plan Decision.allow
        && cell Capability.write Mode.plan (Decision.refuse plan_refusal)
        && cell Capability.exec Mode.plan (Decision.refuse plan_refusal)
        && cell Capability.net Mode.plan (Decision.refuse plan_refusal)

#[test]
def test_decision_table_allow_edit : Bool :=
    // allow_edit passes read and write, asks for exec and net
    cell Capability.read Mode.allow_edit Decision.allow
        && cell Capability.write Mode.allow_edit Decision.allow
        && cell Capability.exec Mode.allow_edit Decision.ask
        && cell Capability.net Mode.allow_edit Decision.ask

#[test]
def test_decision_table_auto : Bool :=
    // auto allows everything
    cell Capability.read Mode.auto Decision.allow
        && cell Capability.write Mode.auto Decision.allow
        && cell Capability.exec Mode.auto Decision.allow
        && cell Capability.net Mode.auto Decision.allow

/// `allow_edit` lets an edit through only inside the workspace: an edit
/// outside it, or one whose target cannot be read, asks. The other modes
/// do not split on scope.
#[test]
def test_allow_edit_asks_for_an_edit_outside_the_workspace : Bool :=
    let out : Assessment := reaching (Reach.outside [Path.path "/etc/hosts"]) in
    let unknown : Assessment := reaching Reach.unknown in
    cell_at Capability.write Mode.allow_edit out Decision.ask
        && cell_at Capability.write Mode.allow_edit unknown Decision.ask
        && cell_at Capability.read Mode.allow_edit out Decision.allow
        && cell_at Capability.write Mode.manual out Decision.ask
        && cell_at Capability.write Mode.plan out (Decision.refuse plan_refusal)
        && cell_at Capability.read Mode.auto out Decision.allow

/// `auto` refuses a destructive pick or a write outside the workspace
/// outright -- no human is in the loop. Every other mode decides as it
/// would anyway (manual already asks, plan refuses).
#[test]
def test_auto_refuses_a_flagged_pick : Bool :=
    let flagged : Assessment := { scope := Reach.inside, danger := Option.some "git push --force rewrites remote history", outside_write := Option.none } in
    let writes_out : Assessment := { scope := Reach.outside [Path.path "/etc/motd"], danger := Option.none, outside_write := Option.some "writes outside the workspace: /etc/motd" } in
    cell_at Capability.exec Mode.auto flagged (Decision.refuse "auto mode: refused a dangerous command: git push --force rewrites remote history")
        && cell_at Capability.write Mode.auto writes_out (Decision.refuse "auto mode: refused: writes outside the workspace: /etc/motd")
        && cell_at Capability.write Mode.auto flagged (Decision.refuse "auto mode: refused a dangerous command: git push --force rewrites remote history")
        && cell_at Capability.exec Mode.manual flagged Decision.ask
        && cell_at Capability.exec Mode.plan flagged (Decision.refuse plan_refusal)

// ── The mode state machine ──────────────────────────────────────────────

/// `/plan approve` drops plan mode to the named target mode.
#[test]
def test_plan_approve_drops_plan_mode : Bool :=
    mode_eq (Mode.approve_plan Mode.manual Mode.plan) Mode.manual
        && mode_eq (Mode.approve_plan Mode.allow_edit Mode.plan) Mode.allow_edit

/// `/plan approve` outside plan mode is a no-op: there is no plan to
/// approve, and the command must not change the mode by accident.
#[test]
def test_plan_approve_is_noop_outside_plan_mode : Bool :=
    mode_eq (Mode.approve_plan Mode.manual Mode.manual) Mode.manual
        && mode_eq (Mode.approve_plan Mode.manual Mode.allow_edit) Mode.allow_edit
        && mode_eq (Mode.approve_plan Mode.manual Mode.auto) Mode.auto

/// `/mode` accepts exactly the four names and rejects everything else.
#[test]
def test_mode_parse : Bool :=
    mode_opt_eq (Mode.parse "manual") (Option.some Mode.manual)
        && mode_opt_eq (Mode.parse "plan") (Option.some Mode.plan)
        && mode_opt_eq (Mode.parse "allow_edit") (Option.some Mode.allow_edit)
        && mode_opt_eq (Mode.parse "auto") (Option.some Mode.auto)
        && mode_opt_eq (Mode.parse "Manual") Option.none
        && mode_opt_eq (Mode.parse "fast") Option.none
        && mode_opt_eq (Mode.parse "") Option.none

/// `parse (show m)` round-trips: what the status bar prints is what
/// `/mode` accepts.
#[test]
def test_mode_show_parse_roundtrip : Bool :=
    roundtrip Mode.manual && roundtrip Mode.plan
        && roundtrip Mode.allow_edit && roundtrip Mode.auto

// ── Tab's mode cycle ─────────────────────────────────────────────────────

/// Tab cycles through every mode in the table's display order and is
/// back where it started on the fifth press.
#[test]
def test_mode_cycle_order : Bool :=
    mode_eq (Mode.cycle Mode.manual) Mode.plan
        && mode_eq (Mode.cycle Mode.plan) Mode.allow_edit
        && mode_eq (Mode.cycle Mode.allow_edit) Mode.auto
        && mode_eq (Mode.cycle Mode.auto) Mode.manual

#[test]
def test_mode_cycle_is_a_full_loop : Bool :=
    mode_eq (Mode.cycle (Mode.cycle (Mode.cycle (Mode.cycle Mode.manual)))) Mode.manual

// ── Startup mode resolution ─────────────────────────────────────────────

#[test]
def test_mode_resolve_flag_beats_settings : Bool :=
    match Mode.resolve (Option.some "auto") (Option.some Mode.plan) {
        Result.ok m => Mode.is_auto m,
        Result.err _ => false,
    }

#[test]
def test_mode_resolve_settings_when_no_flag : Bool :=
    match Mode.resolve Option.none (Option.some Mode.allow_edit) {
        Result.ok m => mode_eq m Mode.allow_edit,
        Result.err _ => false,
    }

#[test]
def test_mode_resolve_defaults_to_manual : Bool :=
    match Mode.resolve Option.none Option.none {
        Result.ok m => mode_eq m Mode.manual,
        Result.err _ => false,
    }

#[test]
def test_mode_resolve_rejects_an_unknown_flag : Bool :=
    match Mode.resolve (Option.some "fast") Option.none {
        Result.ok _ => false,
        Result.err _ => true,
    }

// ── helpers ─────────────────────────────────────────────────────────────

def mode_eq (a : Mode) (b : Mode) : Bool :=
    match a {
        Mode.manual => match b { Mode.manual => true, _ => false },
        Mode.plan => match b { Mode.plan => true, _ => false },
        Mode.allow_edit => match b { Mode.allow_edit => true, _ => false },
        Mode.auto => match b { Mode.auto => true, _ => false },
    }

def mode_opt_eq (a : Option Mode) (b : Option Mode) : Bool :=
    match a {
        Option.none => match b { Option.none => true, _ => false },
        Option.some m => match b { Option.some m2 => mode_eq m m2, _ => false },
    }

def roundtrip (m : Mode) : Bool :=
    mode_opt_eq (Mode.parse (Mode.show m)) (Option.some m)

// ── auto mode with a classifier verdict ─────────────────────────────────

def flagged : Assessment :=
    let a : Assessment := { scope := Reach.inside, danger := Option.some "deletes files", outside_write := Option.none } in
    a

def outside_write : Assessment :=
    let a : Assessment := { scope := Reach.unknown, danger := Option.none, outside_write := Option.some "writes outside the workspace: /etc/x" } in
    a

def auto_cell (cap : Capability) (a : Assessment) (v : Option Verdict) (d : AutoDanger) (expected : Decision) : Bool :=
    decision_eq (Policy.decide_auto cap a v d) expected

/// Every verdict cell: safe runs (flagged or not), dangerous refuses with
/// the reason or asks, and no verdict is the static auto rule (which now
/// refuses a flagged or outside-write pick).
#[test]
def test_decide_auto_every_cell : Bool :=
    let r : String := "auto mode: the classifier blocked this: pushes" in
    let sd : String := "auto mode: refused a dangerous command: deletes files" in
    let so : String := "auto mode: refused: writes outside the workspace: /etc/x" in
    auto_cell Capability.exec plain (Option.some Verdict.safe) AutoDanger.refuse_it Decision.allow
        && auto_cell Capability.exec flagged (Option.some Verdict.safe) AutoDanger.refuse_it Decision.allow
        && auto_cell Capability.exec plain (Option.some (Verdict.dangerous "pushes")) AutoDanger.refuse_it (Decision.refuse r)
        && auto_cell Capability.exec plain (Option.some (Verdict.dangerous "pushes")) AutoDanger.ask_human Decision.ask
        && auto_cell Capability.exec plain Option.none AutoDanger.refuse_it Decision.allow
        && auto_cell Capability.exec flagged Option.none AutoDanger.refuse_it (Decision.refuse sd)
        && auto_cell Capability.write outside_write Option.none AutoDanger.refuse_it (Decision.refuse so)

/// What the classifier judges: code that reaches outside, the network, and
/// an outside write. In-repo code is NOT classified (auto runs it).
#[test]
def test_classified_picks : Bool :=
    Bool.not (Policy.classified Capability.exec plain)
        && Bool.not (Policy.classified Capability.exec (reaching Reach.scratch))
        && Bool.not (Policy.classified Capability.write plain)
        && Bool.not (Policy.classified Capability.read plain)

#[test]
def test_outside_code_and_the_net_are_classified : Bool :=
    let out : Assessment := reaching (Reach.outside [Path.path "/etc/hosts"]) in
    Policy.classified Capability.exec out
        && Policy.classified Capability.exec (reaching Reach.unknown)
        && Policy.classified Capability.net plain
        && Policy.classified Capability.write outside_write
