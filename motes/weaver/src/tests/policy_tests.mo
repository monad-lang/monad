/// The policy engine tests -- weaver.md Phase 2's acceptance: every
/// cell of `Capability x Mode` pinned, the mode state machine's
/// transitions pinned, the `auto` warning flag pinned. All pure, no
/// I/O -- the point of the decision table being a function.
use weaver::policy {
    Mode, Decision, Policy.decide,
    Mode.parse, Mode.approve_plan, Mode.warns_auto, Mode.show, Mode.cycle,
}
use shuttle::gate {Capability}

/// Structural equality on `Decision`, payload included: the refusal
/// reason is part of the contract (the model and the user both read it).
def decision_eq (a : Decision) (b : Decision) : Bool :=
    match a {
        Decision.allow => match b { Decision.allow => true, _ => false },
        Decision.ask => match b { Decision.ask => true, _ => false },
        Decision.refuse r => match b { Decision.refuse r2 => r == r2, _ => false },
    }

/// One cell of the table: the decision for (cap, mode) is `expected`.
def cell (cap : Capability) (mode : Mode) (expected : Decision) : Bool :=
    decision_eq (Policy.decide cap mode) expected

/// The plan-mode refusal reason, exactly as `Policy.decide` spells it.
def plan_refusal : String :=
    "plan mode: only read tools run; produce a plan, then switch with /mode"

/// All 16 cells, exhaustively. A new capability or mode that leaves
/// this test green is impossible: the table is total and the test is
/// the table.
#[test]
def test_decision_table_every_cell : Bool :=
    // manual asks for everything
    cell Capability.read Mode.manual Decision.ask
        && cell Capability.write Mode.manual Decision.ask
        && cell Capability.exec Mode.manual Decision.ask
        && cell Capability.net Mode.manual Decision.ask
        // plan allows reads, refuses the rest
        && cell Capability.read Mode.plan Decision.allow
        && cell Capability.write Mode.plan (Decision.refuse plan_refusal)
        && cell Capability.exec Mode.plan (Decision.refuse plan_refusal)
        && cell Capability.net Mode.plan (Decision.refuse plan_refusal)
        // allow_edit passes read and write, asks for exec and net
        && cell Capability.read Mode.allow_edit Decision.allow
        && cell Capability.write Mode.allow_edit Decision.allow
        && cell Capability.exec Mode.allow_edit Decision.ask
        && cell Capability.net Mode.allow_edit Decision.ask
        // auto allows everything
        && cell Capability.read Mode.auto Decision.allow
        && cell Capability.write Mode.auto Decision.allow
        && cell Capability.exec Mode.auto Decision.allow
        && cell Capability.net Mode.auto Decision.allow

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

// ── The auto warning flag ───────────────────────────────────────────────

/// The warning indicator is on for `auto` and only `auto`.
#[test]
def test_auto_warning_flag : Bool :=
    Bool.not (Mode.warns_auto Mode.manual)
        && Bool.not (Mode.warns_auto Mode.plan)
        && Bool.not (Mode.warns_auto Mode.allow_edit)
        && Mode.warns_auto Mode.auto

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
