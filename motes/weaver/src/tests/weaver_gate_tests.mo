/// The dumb gate's answer line: y/a/n plus an optional note, and a typo
/// that re-prompts instead of silently denying.
use shuttle::gate {Approval, Capability}
use weaver::gate {answer_line, gate_answer_feedback, cap_name}

#[test]
def test_y_with_a_note : Bool :=
    match answer_line "y keep going" {
        Option.none => false,
        Option.some ap => match ap {
            Approval.once_note note => note == "keep going",
            _ => false,
        }
    }

#[test]
def test_plain_y_is_once : Bool :=
    match answer_line "y" {
        Option.none => false,
        Option.some ap => match ap { Approval.once => true, _ => false },
    }

#[test]
def test_a_is_always : Bool :=
    match answer_line "a" {
        Option.none => false,
        Option.some ap => match ap { Approval.always => true, _ => false },
    }

#[test]
def test_n_with_a_reason_denies_with_it : Bool :=
    match answer_line "n because it is destructive" {
        Option.some ap => match ap {
            Approval.deny reason => reason == "because it is destructive",
            _ => false,
        },
        Option.none => false,
    }

#[test]
def test_plain_n_denies : Bool :=
    match answer_line "n" {
        Option.some ap => match ap { Approval.deny _ => true, _ => false },
        Option.none => false,
    }

/// Anything else is not an answer: the prompt asks again.
#[test]
def test_garbage_is_not_an_answer : Bool :=
    match answer_line "yes" {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_feedback_names_the_note : Bool :=
    String.contains (gate_answer_feedback Capability.write (Approval.once_note "x")) "note"
