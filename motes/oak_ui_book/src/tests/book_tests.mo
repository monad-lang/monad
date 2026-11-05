/// The explorer's pure parts: stories, inspection and the update.

use std::list {List.length, List.intercalate}
use xml_html::html {Html.Node, Html.Attr, Html.to_string}
use oak::typed {Oak.Node, Oak.to_html}
use oak::elements {Html.div, Html.button, Html.input, Html.label, Html.img, Html.text, Html.id_, Html.for_, Html.aria, Html.attr}
use oak::app {Command}
use lib::story {
    Book.Story, Book.Msg, Book.Ctx, Book.Story.id, Book.Story.render, Book.Story.title, Book.default_ctx,
    Book.ctx_for, Book.knob_text, Book.knob_int, Book.state, Book.parse_int,
}
use lib::inspect {Book.pretty_html, Book.a11y_lint, Book.listeners}
use lib::app {Book.Model, Book.Effect, Book.init, Book.update, Book.scoped, Book.log_limit, Book.view}
use lib::stories::all {Book.all_stories}

// ─── Stories ───

#[terminating]
def ids (stories : List Book.Story) : List String :=
    match stories {
        List.empty => List.empty,
        List.cons s rest => List.cons (Book.Story.id s) (ids rest),
    }

#[terminating]
def member (xs : List String) (x : String) : Bool :=
    match xs {
        List.empty => false,
        List.cons y rest => if String.beq x y then true else member rest x,
    }

#[terminating]
def all_unique (xs : List String) : Bool :=
    match xs {
        List.empty => true,
        List.cons x rest => Bool.not (member rest x) && all_unique rest,
    }

#[test]
def test_story_ids_unique : Bool :=
    let xs : List String := ids Book.all_stories in
    I64.lt 20 (List.length xs) && all_unique xs

/// `story-id: finding` for every lint finding of every story at its
/// default knobs. Empty is the gate: oak_ui's components must lint clean.
#[terminating]
def findings (stories : List Book.Story) : List String :=
    match stories {
        List.empty => List.empty,
        List.cons s rest =>
            List.append (prefix_all (Book.Story.id s) (Book.a11y_lint (Oak.to_html (Book.Story.render s (Book.default_ctx s)))))
                (findings rest),
    }

#[terminating]
def prefix_all (p : String) (xs : List String) : List String :=
    match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons (String.concat_list [p, ": ", x]) (prefix_all p rest),
    }

#[test]
def test_every_story_lints_clean : Bool :=
    List.is_empty (findings Book.all_stories)

// ─── Knob context ───

#[terminating]
def story_named (id : String) (stories : List Book.Story) : Option Book.Story :=
    match stories {
        List.empty => Option.none,
        List.cons s rest => if String.beq (Book.Story.id s) id then Option.some s else story_named id rest,
    }

#[test]
def test_ctx_overlays_knob_defaults : Bool :=
    match story_named "layout-grid" Book.all_stories {
        Option.none => false,
        Option.some s =>
            let d : Book.Ctx := Book.default_ctx s in
            let c : Book.Ctx := Book.ctx_for s [Pair.pair "cols" "5"] List.empty in
            I64.beq (Book.knob_int d "cols") 3 && I64.beq (Book.knob_int c "cols") 5
                && I64.beq (Book.knob_int c "items") 6,
    }

#[test]
def test_parse_int : Bool :=
    I64.beq (Book.parse_int "42") 42 && I64.beq (Book.parse_int "-7") (-7) && I64.beq (Book.parse_int "12px") 12
        && I64.beq (Book.parse_int "") 0

// ─── Inspection ───

def bad_tree : Oak.Node Unit :=
    Html.div [Html.id_ "dup"]
        [Html.div [Html.id_ "dup"] List.empty,
            Html.button List.empty List.empty,
            Html.input [Html.attr "type" "text"],
            Html.img [Html.attr "src" "/x.png"],
            Html.div [Html.aria "describedby" "nope"] List.empty,
            Html.div [Html.attr "role" "dialog"] List.empty]

def good_tree : Oak.Node Unit :=
    Html.div List.empty
        [Html.label [Html.for_ "n"] [Html.text "Name"],
            Html.input [Html.id_ "n", Html.attr "type" "text"],
            Html.label List.empty [Html.input [Html.attr "type" "checkbox"], Html.text "Remember"],
            Html.button [Html.aria "label" "Close"] [Html.div [Html.aria "hidden" "true"] [Html.text "x"]],
            Html.img [Html.attr "src" "/x.png", Html.attr "alt" ""]]

#[test]
def test_lint_finds_each_problem : Bool :=
    let fs : List String := Book.a11y_lint (Oak.to_html bad_tree) in
    let all : String := List.intercalate "|" fs in
    I64.beq (List.length fs) 6
        && String.contains all "<button> has no accessible name"
        && String.contains all "<input> has no label"
        && String.contains all "<img> has no alt text"
        && String.contains all "aria-describedby points at missing id \"nope\""
        && String.contains all "role=\"dialog\" has no aria-label"
        && String.contains all "id \"dup\" is used more than once"

#[test]
def test_lint_accepts_good_tree : Bool :=
    List.is_empty (Book.a11y_lint (Oak.to_html good_tree))

#[test]
def test_icon_only_button_without_name_is_flagged : Bool :=
    let t : Oak.Node Unit := Html.button List.empty [Html.div [Html.aria "hidden" "true"] [Html.text "x"]] in
    I64.beq (List.length (Book.a11y_lint (Oak.to_html t))) 1

#[test]
def test_pretty_html : Bool :=
    let t : Oak.Node Unit :=
        Html.div [Html.attr "class" "a"] [Html.div List.empty [Html.text "x"], Html.input [Html.attr "value" "<"]] in
    String.beq (Book.pretty_html (Oak.to_html t))
        "<div class=\"a\">\n  <div>x</div>\n  <input value=\"&lt;\">\n</div>"

#[test]
def test_listeners : Bool :=
    let lowered : Html.Node :=
        Html.Node.node_element "div" List.empty
            [Html.Node.node_element "button" [Html.Attr.attr "data-oak-on-click" "0x1"] List.empty] in
    String.beq (List.intercalate "," (Book.listeners lowered)) "<button> click"

// ─── Update ───

def step (m : Book.Model) (msg : Book.Msg) : Book.Model :=
    match Book.update Book.all_stories m msg { Pair.pair next _ => next }

def start : Book.Model := Book.init Book.all_stories

#[test]
def test_knobs_and_state_are_scoped_per_story : Bool :=
    let a : Book.Model := step (step start (Book.Msg.book_select "button")) (Book.Msg.book_knob "label" "Go") in
    let b : Book.Model := step (step a (Book.Msg.book_set "x" "1")) (Book.Msg.book_select "alert") in
    I64.beq (List.length (Book.scoped b.knobs "button")) 1
        && I64.beq (List.length (Book.scoped b.knobs "alert")) 0
        && I64.beq (List.length (Book.scoped b.state "button")) 1

#[test]
def test_reset_drops_only_the_selected_story : Bool :=
    let a : Book.Model := step (step start (Book.Msg.book_select "button")) (Book.Msg.book_knob "label" "Go") in
    let b : Book.Model := step (step a (Book.Msg.book_select "alert")) (Book.Msg.book_knob "title" "T") in
    let c : Book.Model := step b Book.Msg.book_reset in
    I64.beq (List.length (Book.scoped c.knobs "alert")) 0 && I64.beq (List.length (Book.scoped c.knobs "button")) 1

/// Reset re-keys the story frames and knob controls, so the runtime
/// replaces their inputs instead of patching values an edit has detached.
#[test]
def test_reset_rekeys_the_story_dom : Bool :=
    let a : Book.Model := step start (Book.Msg.book_select "button") in
    let b : Book.Model := step a Book.Msg.book_reset in
    let before : String := Html.to_string (Oak.to_html (Book.view Book.all_stories a)) in
    let after : String := Html.to_string (Oak.to_html (Book.view Book.all_stories b)) in
    String.contains before "data-oak-key=\"light/button/0\""
        && String.contains after "data-oak-key=\"light/button/1\""
        && String.contains after "data-oak-key=\"button/1\""

#[terminating]
def log_many (m : Book.Model) (n : I64) : Book.Model :=
    if I64.lt n 1 then m else log_many (step m (Book.Msg.book_action "tick" (I64.to_string n))) (n - 1)

#[test]
def test_action_log_is_bounded_newest_first : Bool :=
    let m : Book.Model := log_many start 60 in
    I64.beq (List.length m.log) Book.log_limit
        && (match m.log { List.cons first _ => String.beq first "tick: 1", List.empty => false })

#[test]
def test_set_and_log : Bool :=
    let m : Book.Model := step start (Book.Msg.book_set_and_log "open" "true" "open modal") in
    (match m.log { List.cons first _ => String.beq first "open modal: true", List.empty => false })
        && I64.beq (List.length (Book.scoped m.state m.selected)) 1

#[test]
def test_prefs_ignore_unknown_story : Bool :=
    let s0 : Book.Model := start in
    let m : Book.Model := step s0 (Book.Msg.book_prefs "no-such-story" "dark") in
    String.beq m.selected "layout-stack" && String.beq m.theme "dark"

#[test]
def test_load_prefs_runs_once : Bool :=
    match Book.update Book.all_stories start Book.Msg.book_load_prefs {
        Pair.pair m cmd =>
            m.prefs_loaded && (match cmd { Command.perform e => (match e { Book.Effect.book_fx_load => true, _ => false }), _ => false })
    }
