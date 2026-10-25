/// The per-turn usage tracker: shuttle reports CUMULATIVE spend, so the
/// last call's request size (context) and the turn's delta (the live
/// row) are both differences the tracker owns.
use weaver::usage {UsageTracker, UsageTracker.start, UsageTracker.note, UsageTracker.last, Usage.delta}
use shuttle::message {Usage}

#[test]
def test_delta_is_field_wise_and_clamps : Bool :=
    let now : Usage := { input_tokens := 5, output_tokens := 2, cached_tokens := 1 } in
    let before : Usage := { input_tokens := 8, output_tokens := 1, cached_tokens := 3 } in
    match Usage.delta now before {
        Usage.mk i o c => i == 0 && o == 1 && c == 0,
    }

/// Two reports in one turn: the turn-to-date delta is measured from the
/// turn's start, the last call from the previous report.
#[test]
def test_tracker_turn_delta_and_last_call : IO Bool := do {
    let base : Usage := { input_tokens := 100, output_tokens := 10, cached_tokens := 40 };
    let r <- UsageTracker.start base;
    let u1 : Usage := { input_tokens := 150, output_tokens := 20, cached_tokens := 60 };
    let _ <- UsageTracker.note r u1;
    let u2 : Usage := { input_tokens := 220, output_tokens := 30, cached_tokens := 90 };
    let since <- UsageTracker.note r u2;
    let last <- UsageTracker.last r;
    return (since.input_tokens == 120 && since.output_tokens == 20 && since.cached_tokens == 50
        && last.input_tokens == 70 && last.output_tokens == 10 && last.cached_tokens == 30)
}

/// Before any report the last call is zero -- the status line must not
/// read an uninitialised slot.
#[test]
def test_tracker_starts_at_zero : IO Bool := do {
    let base : Usage := { input_tokens := 7, output_tokens := 3, cached_tokens := 1 };
    let r <- UsageTracker.start base;
    let last <- UsageTracker.last r;
    return (last.input_tokens == 0 && last.output_tokens == 0 && last.cached_tokens == 0)
}
