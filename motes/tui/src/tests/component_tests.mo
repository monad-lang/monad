/// Tests for the component helpers (`motes/tui/src/component.mo`):
/// `Cmd.map`, `Subs.map`, and which messages a subscription delivers on a
/// given frame.

use lib::component {Cmd.map, Subs, Subs.map, Subs.active, Subs.on_tick}
use lib::tui {Cmd}
use std::list {}

type Kid { ping, pong (n : I64) }
type Host { child (c : Kid), many (ms : List Host) }

def wrap (c : Kid) : Host := Host.child c

def is_ping (p : Host) : Bool :=
    match p {
        Host.child c => match c { Kid.ping => true, _ => false },
        _ => false,
    }

def pong_of (p : Host) : I64 :=
    match p {
        Host.child c => match c { Kid.pong n => n, _ => 0 - 1 },
        _ => 0 - 1,
    }

#[test]
def test_cmd_map_lifts_a_dispatch : Bool :=
    match Cmd.map wrap (Cmd.dispatch Kid.ping) {
        Cmd.dispatch p => is_ping p,
        _ => false,
    }

#[test]
def test_cmd_map_keeps_none_and_quit : Bool :=
    let a : Bool := match Cmd.map wrap (Cmd.none : Cmd Kid) { Cmd.none => true, _ => false } in
    let b : Bool := match Cmd.map wrap (Cmd.quit : Cmd Kid) { Cmd.quit => true, _ => false } in
    a && b

#[test]
def test_cmd_map_lifts_a_perform_result : IO Bool := do {
    let c : Cmd Host := Cmd.map wrap (Cmd.perform (fn (_ : Unit) => IO.pure (Kid.pong 7)));
    match c {
        Cmd.perform action => do {
            let p <- action unit;
            IO.pure (pong_of p == 7)
        },
        _ => IO.pure false,
    }
}

def msgs_on (frame : I64) (s : Subs Host) : List Host :=
    match Subs.on_tick frame s Host.many { Pair.pair ms _ => ms }

def cmd_on (frame : I64) (s : Subs Host) : Cmd Host :=
    match Subs.on_tick frame s Host.many { Pair.pair _ c => c }

def child_subs : Subs Kid :=
    let a : Subs Kid := Subs.every 1 Kid.ping in
    let b : Subs Kid := Subs.every 3 (Kid.pong 3) in
    Subs.batch (List.cons a (List.cons b List.empty))

#[test]
def test_sub_none_is_inactive : Bool :=
    let idle : List (Subs Kid) := [Subs.none, Subs.none] in
    Bool.not (Subs.active (Subs.none : Subs Kid)) && Subs.active child_subs
        && Bool.not (Subs.active (Subs.batch idle))

#[test]
def test_every_frame_and_every_third : Bool :=
    let f1 : List Host := msgs_on 1 (Subs.map wrap child_subs) in
    let f3 : List Host := msgs_on 3 (Subs.map wrap child_subs) in
    List.length f1 == 1 && List.length f3 == 2

#[test]
def test_pure_messages_keep_subscription_order : Bool :=
    match msgs_on 3 (Subs.map wrap child_subs) {
        List.cons a rest => match rest {
            List.cons b _ => is_ping a && pong_of b == 3,
            _ => false,
        },
        _ => false,
    }

#[test]
def test_no_poll_is_no_command : Bool :=
    match cmd_on 3 (Subs.map wrap child_subs) {
        Cmd.none => true,
        _ => false,
    }

#[test]
def test_a_due_poll_runs_in_one_inspect : IO Bool := do {
    let xs : List (Subs Host) := [
        Subs.map wrap (Subs.poll 2 (fn (_ : Unit) => IO.pure (Kid.pong 1))),
        Subs.map wrap (Subs.poll 2 (fn (_ : Unit) => IO.pure (Kid.pong 2))),
        Subs.map wrap (Subs.poll 5 (fn (_ : Unit) => IO.pure (Kid.pong 5))),
    ];
    let s : Subs Host := Subs.batch xs;
    match cmd_on 4 s {
        Cmd.inspect action => do {
            let msg <- action unit;
            match msg {
                Host.many ms => match ms {
                    List.cons a rest => match rest {
                        List.cons b more => IO.pure (pong_of a == 1 && pong_of b == 2 && List.is_empty more),
                        _ => IO.pure false,
                    },
                    _ => IO.pure false,
                },
                _ => IO.pure false,
            }
        },
        _ => IO.pure false,
    }
}
