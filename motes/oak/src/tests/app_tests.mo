// Command/Program tests over a write-logging mock monad and a mock host.
//
// The host monad and its helpers are prefixed `AppM`/`app_`: the Rust host
// flattens the directory's test modules into one program scope, so the
// `RenderM` helpers in html_t_tests.mo must not collide with these.

use std::list {List.length}
use lib::app {Program, Program.run_batch, Program.step, Program.view, Command, Host}
use lib::elements {Html.li, Html.text, Html.ul}
use lib::typed {Oak.Node, Oak.to_html}
use xml_html::html {Html.to_string}

// ═══ A write-logging base monad ═══

type AppM A {
    app_m (log : List String) (a : A)
}

def app_pure {A : Type} (a : A) : AppM A :=
    AppM.app_m List.empty a

def app_bind_run {A : Type} {B : Type} (f : A -> AppM B) (log : List String) (a : A) : AppM B :=
    match f a {
        AppM.app_m log2 b => AppM.app_m (List.append log log2) b
    }

pub instance Monad AppM {
    def pure (a : A) : AppM A := app_pure a
    def bind (ma : AppM A) (f : A -> AppM B) : AppM B :=
        match ma { app_m log a => app_bind_run f log a }
}

def app_log {A : Type} (m : AppM A) : List String :=
    match m { AppM.app_m log _ => log }

// ═══ The mock host and app ═══

def effect_run (effect : String) : AppM (Option String) :=
    if String.beq effect "silent"
    then AppM.app_m (List.cons "effect:silent" List.empty) Option.none
    else AppM.app_m
        (List.cons (String.concat "effect:" effect) List.empty)
        (Option.some (String.concat "done:" effect))

def app_mock_host : Host AppM String String :=
    Host.host effect_run

def log_add (log : List String) (s : String) : List String :=
    List.append log (List.cons s List.empty)

def app_update (log : List String) (m : String) : Pair (List String) (Command String String) :=
    if String.beq m "dispatch"
    then Pair.pair (log_add log "dispatch") (Command.dispatch "next")
    else if String.beq m "effect"
    then Pair.pair (log_add log "effect") (Command.perform "effect")
    else if String.beq m "silent"
    then Pair.pair (log_add log "silent") (Command.perform "silent")
    else if String.beq m "quit"
    then Pair.pair (log_add log "quit") Command.quit
    else Pair.pair (log_add log m) Command.none

def log_item (s : String) : Oak.Node String :=
    Html.li List.empty [Html.text s]

#[terminating]
def log_items (log : List String) : List (Oak.Node String) :=
    match log {
        List.empty => List.empty,
        List.cons s rest => List.cons (log_item s) (log_items rest),
    }

def app_view (log : List String) : Oak.Node String :=
    Html.ul List.empty (log_items log)

def app_under_test : Program (List String) String String :=
    Program.app List.empty app_update app_view

// ═══ Reading the result back ═══

def app_run (msgs : List String) : AppM (Pair (List String) Bool) :=
    Program.run_batch app_under_test app_mock_host List.empty msgs

def pair_log (p : Pair (List String) Bool) : List String :=
    match p { Pair.pair log _ => log }

def pair_quit (p : Pair (List String) Bool) : Bool :=
    match p { Pair.pair _ quit => quit }

def app_result_log (msgs : List String) : List String :=
    match app_run msgs { AppM.app_m _ p => pair_log p }

def app_result_quit (msgs : List String) : Bool :=
    match app_run msgs { AppM.app_m _ p => pair_quit p }

def app_effects (msgs : List String) : List String :=
    app_log (app_run msgs)

def app_strs_eq (a : List String) (b : List String) : Bool :=
    match a {
        empty => List.length b == 0,
        cons x xs => match b {
            empty => false,
            cons y ys => x == y && app_strs_eq xs ys
        }
    }

def cmd_is_none (c : Command String String) : Bool :=
    match c { Command.none => true, _ => false }

// ═══ Tests ═══

#[test]
def test_message_order : Bool :=
    app_strs_eq (app_result_log ["a", "b"]) ["a", "b"]
    && Bool.not (app_result_quit ["a", "b"])
    && app_strs_eq (app_effects ["a", "b"]) List.empty

#[test]
def test_deferred_dispatch_drains : Bool :=
    app_strs_eq (app_result_log ["a", "dispatch", "b"]) ["a", "dispatch", "b", "next"]
    && app_strs_eq (app_effects ["a", "dispatch", "b"]) List.empty

#[test]
def test_dispatch_keeps_source_order : Bool :=
    app_strs_eq (app_result_log ["dispatch", "dispatch"]) ["dispatch", "dispatch", "next", "next"]

#[test]
def test_perform_folds_current_batch : Bool :=
    app_strs_eq (app_result_log ["effect", "z"]) ["effect", "done:effect", "z"]
    && app_strs_eq (app_effects ["effect", "z"]) ["effect:effect"]

#[test]
def test_perform_none : Bool :=
    app_strs_eq (app_result_log ["silent", "z"]) ["silent", "z"]
    && app_strs_eq (app_effects ["silent", "z"]) ["effect:silent"]

#[test]
def test_quit_stops_batch : Bool :=
    app_strs_eq (app_result_log ["quit", "after"]) ["quit"]
    && app_result_quit ["quit", "after"]
    && app_strs_eq (app_effects ["quit", "after"]) List.empty

#[test]
def test_empty_batch : Bool :=
    app_strs_eq (app_result_log List.empty) List.empty
    && Bool.not (app_result_quit List.empty)

#[test]
def test_step_is_pure : Bool :=
    let p : Pair (List String) (Command String String) := Program.step app_under_test List.empty "a" in
    match p {
        Pair.pair log cmd => app_strs_eq log ["a"] && cmd_is_none cmd
    }

#[test]
def test_golden_view : Bool :=
    String.beq (Html.to_string (Oak.to_html (Program.view app_under_test ["a", "b"])))
        "<ul><li>a</li><li>b</li></ul>"

#[test]
def test_init : Bool :=
    app_strs_eq (Program.init app_under_test) List.empty
