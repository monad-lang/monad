/// Pure tests for the /try page: its state machine and its view.

use lib::app {TryEffect, TryModel, TryMsg, try_init, try_subscriptions, try_update, try_view}
use oak::app {Command}
use oak::typed {Oak.to_html}
use xml_html::html {Html.to_string}

def started_source (msg : TryMsg) : Option String :=
    match try_update try_init msg {
        Pair.pair _ cmd =>
            match cmd {
                Command.perform e =>
                    match e {
                        TryEffect.start s => Option.some s,
                        _ => Option.none,
                    },
                _ => Option.none,
            },
    }

def cancel_requested (cmd : Command TryEffect TryMsg) : Bool :=
    match cmd {
        Command.perform e =>
            match e {
                TryEffect.cancel => true,
                _ => false,
            },
        _ => false,
    }

#[test]
def test_run_starts_the_worker_with_the_source : Bool :=
    let m : TryModel := try_init
    in
    match started_source TryMsg.run {
        Option.some s => String.beq s m.source,
        Option.none => false,
    }

#[test]
def test_run_marks_running_and_subscribes_to_frames : Bool :=
    match try_update try_init TryMsg.run {
        Pair.pair m _cmd =>
            m.running && Bool.not (List.is_empty (try_subscriptions m)),
    }

#[test]
def test_finished_clears_running_and_keeps_the_result : Bool :=
    match try_update try_init (TryMsg.finished "ok" "5" "I64" "" "") {
        Pair.pair m _cmd =>
            Bool.not m.running
                && String.beq m.value "5"
                && String.beq m.typ "I64"
                && List.is_empty (try_subscriptions m),
    }

#[test]
def test_source_change_keeps_the_editor_text : Bool :=
    let m0 : TryModel := try_init
    in
    match try_update m0 (TryMsg.source_changed "def main : I64 := 1\n") {
        Pair.pair m _cmd =>
            String.beq m.source "def main : I64 := 1\n"
                && String.beq m.editor_text m0.editor_text,
    }

#[test]
def test_example_load_replaces_both_source_and_editor : Bool :=
    let m0 : TryModel := try_init
    in
    match try_update m0 (TryMsg.load_example 1) {
        Pair.pair m _cmd =>
            String.beq m.source m.editor_text
                && Bool.not (String.beq m.editor_key m0.editor_key),
    }

#[test]
def test_reloading_the_same_example_bumps_the_editor_key : Bool :=
    match try_update try_init (TryMsg.load_example 1) {
        Pair.pair first _cmd =>
            match try_update first (TryMsg.load_example 1) {
                Pair.pair second _cmd =>
                    Bool.not (String.beq first.editor_key second.editor_key),
            },
    }

#[test]
def test_loading_an_example_while_running_cancels_the_worker : Bool :=
    match try_update { try_init with running := true } (TryMsg.load_example 1) {
        Pair.pair m cmd => Bool.not m.running && cancel_requested cmd,
    }

#[test]
def test_cancel_requests_cancel_and_stops_running : Bool :=
    match try_update { try_init with running := true } TryMsg.cancel {
        Pair.pair m cmd => Bool.not m.running && cancel_requested cmd,
    }

// ─── View ─────────────────────────────────────────────────────────────

def view_html (m : TryModel) : String :=
    Html.to_string (Oak.to_html (try_view m))

/// The page must say what it is: the evaluator interprets the program
/// with no optimisation, and users should not read its speed as the
/// language's.
#[test]
def test_view_marks_the_evaluator_experimental : Bool :=
    let html : String := view_html try_init
    in
    String.contains html "Experimental and unoptimised"
