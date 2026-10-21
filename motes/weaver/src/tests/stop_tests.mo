/// The cooperative stop signal: reset/request/round-trip and the
/// generation guard (a stale request never stops a later turn).
use weaver::stop {Stop.reset, Stop.request, Stop.write, Stop.read, Stop.predicate}

#[test]
def test_stop_reset_reads_a_clear_state : IO Bool := do {
    Stop.reset Option.none;
    let r <- Stop.read Option.none;
    return (match r {
        Option.some s => Bool.not s.stop && s.gen == 0,
        Option.none => false,
    })
}

#[test]
def test_stop_write_roundtrip : IO Bool := do {
    Stop.write Option.none 7 true;
    let r <- Stop.read Option.none;
    Stop.reset Option.none;
    return (match r {
        Option.some s => s.gen == 7 && s.stop,
        Option.none => false,
    })
}

#[test]
def test_stop_predicate_matches_only_its_generation : IO Bool := do {
    Stop.request Option.none 3;
    let mine <- Stop.predicate Option.none 3 unit;
    let other <- Stop.predicate Option.none 4 unit;
    Stop.reset Option.none;
    return (Bool.and mine (Bool.not other))
}
