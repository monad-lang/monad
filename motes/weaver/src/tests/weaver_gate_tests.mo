use shuttle::gate {Capability}
use std::path {Path}
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

def precheck_of (mode : Mode) (grants : Option (Ref (List PermGrant))) (root : Option Path) (p : Pick) : IO (Option Approval) := do {
    let g : Gate := Gate.weaver mode grants root Option.none no_read no_write;
    let check : Pick -> IO (Option Approval) := g.precheck;
    let r <- check p;
    return r
}

/// A repo grant lets an in-repo write through without a prompt -- and
/// with EXACTLY `once`: a deny here would otherwise pass a test that only
/// checks for "some decision".
#[test]
def test_precheck_allows_a_granted_repo_write : IO Bool := do {
    let empty_grants : List PermGrant := List.empty;
    let r <- Ref.new empty_grants;
    let g : PermGrant := { cap := Capability.write, scope := PermScope.repo };
    let _ <- Permissions.add (Option.some r) g;
    let res <- precheck_of Mode.manual (Option.some r) (Option.some (Path.path "/repo")) (write_pick "src/a.mo");
    return (match res {
        Option.some ap => match ap { Approval.once => true, _ => false },
        Option.none => false,
    })
}

/// An anywhere grant matches too, and also answers `once`.
#[test]
def test_precheck_allows_a_granted_anywhere_write : IO Bool := do {
    let empty_grants : List PermGrant := List.empty;
    let r <- Ref.new empty_grants;
    let g : PermGrant := { cap := Capability.write, scope := PermScope.anywhere };
    let _ <- Permissions.add (Option.some r) g;
    let res <- precheck_of Mode.manual (Option.some r) (Option.some (Path.path "/repo")) (write_pick "/tmp/a.mo");
    return (match res {
        Option.some ap => match ap { Approval.once => true, _ => false },
        Option.none => false,
    })
}

/// ...but not a write outside the root: that still asks.
#[test]
def test_precheck_does_not_cover_an_outside_write : IO Bool := do {
    let empty_grants : List PermGrant := List.empty;
    let r <- Ref.new empty_grants;
    let g : PermGrant := { cap := Capability.write, scope := PermScope.repo };
    let _ <- Permissions.add (Option.some r) g;
    let res <- precheck_of Mode.manual (Option.some r) (Option.some (Path.path "/repo")) (write_pick "/tmp/a.mo");
    return (match res { Option.none => true, Option.some _ => false })
}

/// Plan mode's refusal beats any grant, anywhere scope included.
#[test]
def test_precheck_refuses_a_granted_write_in_plan_mode : IO Bool := do {
    let empty_grants : List PermGrant := List.empty;
    let r <- Ref.new empty_grants;
    let g : PermGrant := { cap := Capability.write, scope := PermScope.anywhere };
    let _ <- Permissions.add (Option.some r) g;
    let res <- precheck_of Mode.plan (Option.some r) (Option.some (Path.path "/repo")) (write_pick "src/a.mo");
    return (match res {
        Option.some ap => match ap { Approval.deny _ => true, _ => false },
        Option.none => false,
    })
}

// ── commands scoped to the workspace ──────────────────────────────────

def shell_pick (command : String) : Pick :=
    let input : Json := Json.make_object (Map.insert "command" (Json.make_str command) BTreeMap.empty) in
    { name := "shell", cap := Capability.exec, input := input }

def exec_repo_precheck (command : String) : IO (Option Approval) := do {
    let empty_grants : List PermGrant := List.empty;
    let r <- Ref.new empty_grants;
    let g : PermGrant := { cap := Capability.exec, scope := PermScope.repo };
    let _ <- Permissions.add (Option.some r) g;
    precheck_of Mode.manual (Option.some r) (Option.some (Path.path "/repo")) (shell_pick command)
}

/// A repo exec grant now covers a command that stays in the workspace...
#[test]
def test_repo_exec_grant_covers_an_inside_command : IO Bool := do {
    let res <- exec_repo_precheck "cargo test -p core && ls src/";
    return (match res {
        Option.some ap => match ap { Approval.once => true, _ => false },
        Option.none => false,
    })
}

/// ...but not one that reaches outside it, or one it cannot read.
#[test]
def test_repo_exec_grant_does_not_cover_an_outside_command : IO Bool := do {
    let a <- exec_repo_precheck "cat /etc/hosts";
    let b <- exec_repo_precheck "cd .. && ls";
    let c <- exec_repo_precheck "ls $HOME/x";
    let none_a : Bool := match a { Option.none => true, Option.some _ => false };
    let none_b : Bool := match b { Option.none => true, Option.some _ => false };
    let none_c : Bool := match c { Option.none => true, Option.some _ => false };
    return (none_a && none_b && none_c)
}

/// No grant covers a flagged command, not even an anywhere grant: it is
/// asked about every time.
#[test]
def test_grants_never_cover_a_flagged_command : IO Bool := do {
    let empty_grants : List PermGrant := List.empty;
    let r <- Ref.new empty_grants;
    let g : PermGrant := { cap := Capability.exec, scope := PermScope.anywhere };
    let _ <- Permissions.add (Option.some r) g;
    let flagged <- precheck_of Mode.manual (Option.some r) (Option.some (Path.path "/repo")) (shell_pick "git push --force");
    let plain <- precheck_of Mode.manual (Option.some r) (Option.some (Path.path "/repo")) (shell_pick "git push");
    let asks : Bool := match flagged { Option.none => true, Option.some _ => false };
    let granted : Bool := match plain { Option.some ap => match ap { Approval.once => true, _ => false }, Option.none => false };
    return (asks && granted)
}

/// In auto mode the precheck lets a plain command through (no decision:
/// the ask cell answers once) and leaves a flagged one to the prompt.
#[test]
def test_auto_mode_holds_a_flagged_command_for_the_prompt : IO Bool := do {
    let empty_grants : List PermGrant := List.empty;
    let r <- Ref.new empty_grants;
    let g : Gate := Gate.weaver Mode.auto (Option.some r) (Option.some (Path.path "/repo")) Option.none no_read no_write;
    let ask : Pick -> IO Approval := g.ask;
    let plain <- ask (shell_pick "ls src");
    let flagged <- ask (shell_pick "rm -rf /");
    let plain_ok : Bool := match plain { Approval.once => true, _ => false };
    let flagged_denied : Bool := match flagged { Approval.deny _ => true, _ => false };
    return (plain_ok && flagged_denied)
}

/// todo_write never asks, in manual mode or any other.
#[test]
def test_todo_write_is_unguarded : IO Bool := do {
    let input : Json := Json.make_object (Map.insert "todos" (Json.make_str "x") BTreeMap.empty);
    let p : Pick := { name := "todo_write", cap := Capability.read, input := input };
    let res <- precheck_of Mode.manual Option.none (Option.some (Path.path "/repo")) p;
    return (match res {
        Option.some ap => match ap { Approval.once => true, _ => false },
        Option.none => false,
    })
}
