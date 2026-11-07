/// `Signal` is the one place the numbers live; these pin the table against
/// the platform's own values so a typo cannot silently send the wrong one.

use sys::signal {Signal, Signal.name, Signal.number}

#[test]
def test_signal_numbers : Bool :=
    I64.beq (Signal.number Signal.kill) 9
    && I64.beq (Signal.number Signal.term) 15
    && I64.beq (Signal.number Signal.winch) 28
    && I64.beq (Signal.number (Signal.other 64)) 64

#[test]
def test_signal_names : Bool :=
    String.beq (Signal.name Signal.hup) "HUP"
    && String.beq (Signal.name (Signal.other 64)) "SIG64"
