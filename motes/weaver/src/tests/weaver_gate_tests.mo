use shuttle::gate {Capability}
use weaver::gate {PickAnswer, answer_line, gate_answer_feedback, gate_answer_prompt}
use shuttle::gate {Pick, Approval, Gate}
use weaver::gate {Gate.weaver}
use weaver::policy {Mode}
use weaver::permissions {PermGrant, PermScope, Permissions.add}
use std::ref {Ref}
use json::json {Json, Json.make_object, Json.make_str}
use std::map {Map, BTreeMap}

/// The dumb gate's answer line: y/r/a/n plus an optional note, and a
/// typo that re-prompts instead of silently denying. `r` is accepted
/// only when a repo scope was offered.

def note_of (got : Option (Pair PickAnswer String)) : String :=
    match got {
        Option.none => "",
        Option.some pr => match pr { Pair.pair _ note => note },
    }

def is_once (got : Option (Pair PickAnswer String)) : Bool :=
    match got {
        Option.none => false,
        Option.some pr => match pr {
            Pair.pair ans _ => match ans { PickAnswer.pick_once => true, _ => false },
        },
    }

def is_here (got : Option (Pair PickAnswer String)) : Bool :=
    match got {
        Option.none => false,
        Option.some pr => match pr {
            Pair.pair ans _ => match ans { PickAnswer.pick_here => true, _ => false },
        },
    }

def is_any (got : Option (Pair PickAnswer String)) : Bool :=
    match got {
        Option.none => false,
        Option.some pr => match pr {
            Pair.pair ans _ => match ans { PickAnswer.pick_any => true, _ => false },
        },
    }

def deny_reason (got : Option (Pair PickAnswer String)) : String :=
    match got {
        Option.none => "",
        Option.some pr => match pr {
            Pair.pair ans _ => match ans {
                PickAnswer.pick_deny reason => reason,
                _ => "",
            },
        },
    }

#[test]
def test_y_is_once_with_a_note : Bool :=
    let got := answer_line false "y keep going" in
    is_once got && String.beq (note_of got) "keep going"

#[test]
def test_plain_y_is_once : Bool :=
    is_once (answer_line false "y")

/// `a` is anywhere, even when a repo scope was offered.
#[test]
def test_a_is_anywhere : Bool :=
    is_any (answer_line true "a")

/// `r` records a repo-scoped grant when the pick is inside the root,
/// and is not an answer otherwise.
#[test]
def test_r_is_repo_scope_when_offered : Bool :=
    is_here (answer_line true "r")

#[test]
def test_r_is_refused_when_not_offered : Bool :=
    match answer_line false "r" {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_n_with_a_reason_denies_with_it : Bool :=
    String.beq (deny_reason (answer_line false "n because it is destructive")) "because it is destructive"

#[test]
def test_plain_n_denies : Bool :=
    String.beq (deny_reason (answer_line false "n")) "declined by user"

/// Anything else is not an answer: the prompt asks again.
#[test]
def test_garbage_is_not_an_answer : Bool :=
    match answer_line false "yes" {
        Option.none => true,
        Option.some _ => false,
    }

/// The prompt and the feedback name the scope: "all writes in this
/// repo" and "all writes anywhere" are different promises.
#[test]
def test_prompt_offers_r_only_for_a_repo_pick : Bool :=
    String.contains (gate_answer_prompt Capability.write true) "[r]"
        && Bool.not (String.contains (gate_answer_prompt Capability.write false) "[r]")

#[test]
def test_feedback_names_the_granted_scope : Bool :=
    String.contains (gate_answer_feedback Capability.write PickAnswer.pick_here) "workspace root"
        && String.contains (gate_answer_feedback Capability.write PickAnswer.pick_any) "anywhere"

// ── the grant precheck ────────────────────────────────────────────────

def write_pick (path : String) : Pick :=
    let input : Json := Json.make_object (Map.insert "path" (Json.make_str path) BTreeMap.empty) in
    { name := "write", cap := Capability.write, input := input }

def no_read (_ : Unit) : IO (Option String) := IO.pure Option.none

def no_write (_ : String) : IO Unit := IO.pure unit

def precheck_of (mode : Mode) (grants : Option (Ref (List PermGrant))) (root : Option String) (p : Pick) : IO (Option Approval) := do {
    let g : Gate := Gate.weaver mode grants root no_read no_write;
    let check : Pick -> IO (Option Approval) := g.precheck;
    let r <- check p;
    return r
}

/// A repo grant lets an in-repo write through without a prompt...
#[test]
def test_precheck_allows_a_granted_repo_write : IO Bool := do {
    let empty_grants : List PermGrant := List.empty;
    let r <- Ref.new empty_grants;
    let g : PermGrant := { cap := Capability.write, scope := PermScope.repo };
    let _ <- Permissions.add (Option.some r) g;
    let res <- precheck_of Mode.manual (Option.some r) (Option.some "/repo") (write_pick "src/a.mo");
    return (match res { Option.some _ => true, Option.none => false })
}

/// ...but not a write outside the root: that still asks.
#[test]
def test_precheck_does_not_cover_an_outside_write : IO Bool := do {
    let empty_grants : List PermGrant := List.empty;
    let r <- Ref.new empty_grants;
    let g : PermGrant := { cap := Capability.write, scope := PermScope.repo };
    let _ <- Permissions.add (Option.some r) g;
    let res <- precheck_of Mode.manual (Option.some r) (Option.some "/repo") (write_pick "/tmp/a.mo");
    return (match res { Option.none => true, Option.some _ => false })
}

/// Plan mode's refusal beats any grant, anywhere scope included.
#[test]
def test_precheck_refuses_a_granted_write_in_plan_mode : IO Bool := do {
    let empty_grants : List PermGrant := List.empty;
    let r <- Ref.new empty_grants;
    let g : PermGrant := { cap := Capability.write, scope := PermScope.anywhere };
    let _ <- Permissions.add (Option.some r) g;
    let res <- precheck_of Mode.plan (Option.some r) (Option.some "/repo") (write_pick "src/a.mo");
    return (match res {
        Option.some ap => match ap { Approval.deny _ => true, _ => false },
        Option.none => false,
    })
}
