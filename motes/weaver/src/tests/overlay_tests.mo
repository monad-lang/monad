/// The dialog/stdin handshake file: reset, acknowledgement, and the
/// close sequence bump that makes the main loop repaint.
use weaver::overlay {
    OverlayState, Overlay.reset, Overlay.read, Overlay.write_state, Overlay.ack, Overlay.finish,
}

#[test]
def test_overlay_reset_is_closed : IO Bool := do {
    Overlay.reset Option.none;
    let r <- Overlay.read Option.none;
    return (match r {
        Option.some s => Bool.not s.want && Bool.not s.ack && s.seq == 0,
        Option.none => false,
    })
}

#[test]
def test_overlay_ack_sets_ack_only_when_wanted : IO Bool := do {
    let w : OverlayState := { want := true, ack := false, seq := 4 };
    Overlay.write_state Option.none w;
    Overlay.ack Option.none;
    let a <- Overlay.read Option.none;
    Overlay.reset Option.none;
    return (match a {
        Option.some s => s.ack && s.want && s.seq == 4,
        Option.none => false,
    })
}

#[test]
def test_overlay_finish_releases_and_bumps_seq : IO Bool := do {
    let w : OverlayState := { want := true, ack := true, seq := 4 };
    Overlay.write_state Option.none w;
    Overlay.finish Option.none;
    let a <- Overlay.read Option.none;
    Overlay.reset Option.none;
    return (match a {
        Option.some s => Bool.not s.want && Bool.not s.ack && s.seq == 5,
        Option.none => false,
    })
}
