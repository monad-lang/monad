// The explorer: a pure Oak program over a list of stories.
//
// Layout (built from oak_ui itself): a header with the theme and viewport
// controls, a sidebar of stories grouped and filtered by a search box, the
// canvas (the story rendered inside one or two themed frames), and an addon
// panel of tabs: Controls, Actions, Source, A11y, Tokens.
//
// Knob values and story state are kept per story, in flat association
// lists keyed `"<story id>/<name>"`. The selected story and theme persist
// through the `Book.Effect` host (browser storage, in `main.mo`); the app
// asks for them once, on the first animation frame.

use std::list {List.length, List.intercalate}
use web_event::event {WebEvent}
use xml_html::html {Html.Node}
use oak::typed {Oak.Node, Oak.Attr, Oak.Lowered, Oak.lower, Oak.to_html}
use oak::elements {
    Html.div, Html.span, Html.p, Html.strong, Html.text, Html.class_, Html.class_list, Html.attr,
    Html.aria, Html.style_attr, Html.id_, Html.placeholder, Html.key,
}
use oak::events {Html.on_click, Subscription, Subscription.animation_frame_msg}
use oak::app {Command, Program}
use oak_ui::vocab {
    Ui.Opt, Ui.primary, Ui.success, Ui.danger, Ui.info, Ui.small, Ui.ghost, Ui.outline, Ui.soft,
    Ui.full, Ui.cls, Ui.gap,
}
use oak_ui::theme {Ui.Theme, Ui.Theme.light, Ui.Theme.dark, Ui.Theme.tokens}
use oak_ui::layout {Ui.stack, Ui.row, Ui.cluster, Ui.app_shell, Ui.spacer}
use oak_ui::typography {Ui.heading, Ui.muted, Ui.code_block, Ui.code, Ui.text}
use oak_ui::button {Ui.button, Ui.icon_button, Ui.button_group, Ui.icon}
use oak_ui::form {Ui.field, Ui.text_input, Ui.input, Ui.select, Ui.switch}
use oak_ui::feedback {Ui.alert, Ui.badge, Ui.empty_state}
use oak_ui::data {Ui.list_group, Ui.description_list}
use oak_ui::nav {Ui.NavGroup, Ui.NavItem, Ui.nav_item, Ui.nav_group, Ui.sidebar_nav, Ui.tabs, Ui.tab}
use lib::story {
    Book.Story, Book.Msg, Book.Knob, Book.Ctx, Book.Story.id, Book.Story.group, Book.Story.title,
    Book.Story.notes, Book.Story.knobs, Book.Story.render, Book.Knob.name, Book.ctx_for, Book.lookup_or,
    Book.assoc,
}
use lib::inspect {Book.pretty_html, Book.a11y_lint, Book.listeners}

// ═══ Model, effects ═══

pub struct Book.Model {
    selected : String,
    query : String,
    knobs : List (Pair String String),
    state : List (Pair String String),
    log : List String,
    theme : String,
    viewport : String,
    panel : String,
    nav_open : Bool,
    prefs_loaded : Bool,
    /// Bumped by Reset. The runtime patches `value`/`checked` as
    /// attributes, which an edited input ignores, so the story frames and
    /// the knob controls are keyed by story and generation: a reset or a
    /// story switch replaces them instead of patching stale inputs.
    generation : I64
}

pub type Book.Effect {
    book_fx_load,
    book_fx_save (story : String) (theme : String)
}

/// The model for `stories`: the first story selected, light theme.
pub def Book.init (stories : List Book.Story) : Book.Model :=
    { selected := first_id stories, query := "", knobs := List.empty, state := List.empty,
        log := List.empty, theme := "light", viewport := "full", panel := "controls",
        nav_open := false, prefs_loaded := false, generation := 0 }

def first_id (stories : List Book.Story) : String :=
    match stories {
        List.cons s _ => Book.Story.id s,
        List.empty => "",
    }

/// The most recent entries the Actions panel keeps.
pub def Book.log_limit : I64 := 50

// ═══ Scoped association lists ═══

def scoped_key (story : String) (name : String) : String := String.concat_list [story, "/", name]

/// The entries under `story/`, with the prefix stripped.
#[terminating]
pub def Book.scoped (pairs : List (Pair String String)) (story : String) : List (Pair String String) :=
    match pairs {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Pair.pair k v =>
                    let prefix : String := String.concat story "/" in
                    if String.starts_with prefix k
                    then List.cons (Pair.pair (String.drop (String.length prefix) k) v) (Book.scoped rest story)
                    else Book.scoped rest story
            },
    }

#[terminating]
def drop_scope (pairs : List (Pair String String)) (story : String) : List (Pair String String) :=
    match pairs {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Pair.pair k _ =>
                    if String.starts_with (String.concat story "/") k
                    then drop_scope rest story
                    else List.cons p (drop_scope rest story)
            },
    }

#[terminating]
def take (n : I64) (xs : List String) : List String :=
    if I64.lt n 1 then List.empty
    else
        match xs {
            List.empty => List.empty,
            List.cons x rest => List.cons x (take (n - 1) rest),
        }

def log_entry (m : Book.Model) (entry : String) : Book.Model :=
    { m with log := take Book.log_limit (List.cons entry m.log) }

// ═══ Update ═══

def stay (m : Book.Model) : Pair Book.Model (Command Book.Effect Book.Msg) := Pair.pair m Command.none

def save (m : Book.Model) : Pair Book.Model (Command Book.Effect Book.Msg) :=
    Pair.pair m (Command.perform (Book.Effect.book_fx_save m.selected m.theme))

#[terminating]
def has_story (stories : List Book.Story) (id : String) : Bool :=
    match stories {
        List.empty => false,
        List.cons s rest => if String.beq (Book.Story.id s) id then true else has_story rest id,
    }

pub def Book.update (stories : List Book.Story) (m : Book.Model) (msg : Book.Msg)
    : Pair Book.Model (Command Book.Effect Book.Msg) :=
    match msg {
        Book.Msg.book_select id => save { m with selected := id, nav_open := false },
        Book.Msg.book_search q => stay { m with query := q },
        Book.Msg.book_knob name value =>
            stay { m with knobs := Book.assoc m.knobs (scoped_key m.selected name) value },
        Book.Msg.book_set key value =>
            stay { m with state := Book.assoc m.state (scoped_key m.selected key) value },
        Book.Msg.book_action name payload =>
            stay (log_entry m (if String.is_empty payload then name else String.concat_list [name, ": ", payload])),
        Book.Msg.book_set_and_log key value name =>
            stay (log_entry { m with state := Book.assoc m.state (scoped_key m.selected key) value }
                (String.concat_list [name, ": ", value])),
        Book.Msg.book_theme t => save { m with theme := t },
        Book.Msg.book_viewport v => stay { m with viewport := v },
        Book.Msg.book_panel p => stay { m with panel := p },
        Book.Msg.book_reset =>
            stay
                { m with
                    knobs := drop_scope m.knobs m.selected,
                    state := drop_scope m.state m.selected,
                    generation := m.generation + 1 },
        Book.Msg.book_clear_log => stay { m with log := List.empty },
        Book.Msg.book_toggle_nav => stay { m with nav_open := Bool.not m.nav_open },
        Book.Msg.book_load_prefs =>
            Pair.pair { m with prefs_loaded := true } (Command.perform Book.Effect.book_fx_load),
        Book.Msg.book_prefs story theme =>
            stay
                { m with
                    selected := (if has_story stories story then story else m.selected),
                    theme := (if String.is_empty theme then m.theme else theme) },
    }

pub def Book.subscriptions (m : Book.Model) : List (Subscription Book.Msg) :=
    if m.prefs_loaded then List.empty else [Subscription.animation_frame_msg Book.Msg.book_load_prefs]

// ═══ View: sidebar ═══

def matches (query : String) (s : Book.Story) : Bool :=
    let q : String := String.to_lowercase (String.trim query) in
    String.is_empty q
        || String.contains (String.to_lowercase (Book.Story.title s)) q
        || String.contains (String.to_lowercase (Book.Story.group s)) q

#[terminating]
def filter_stories (query : String) (stories : List Book.Story) : List Book.Story :=
    match stories {
        List.empty => List.empty,
        List.cons s rest => if matches query s then List.cons s (filter_stories query rest) else filter_stories query rest,
    }

#[terminating]
def group_names (stories : List Book.Story) (seen : List String) : List String :=
    match stories {
        List.empty => List.empty,
        List.cons s rest =>
            let g : String := Book.Story.group s in
            if contains_name seen g
            then group_names rest seen
            else List.cons g (group_names rest (List.cons g seen)),
    }

#[terminating]
def contains_name (xs : List String) (x : String) : Bool :=
    match xs {
        List.empty => false,
        List.cons y rest => if String.beq x y then true else contains_name rest x,
    }

#[terminating]
def items_in (group : String) (stories : List Book.Story) : List Ui.NavItem :=
    match stories {
        List.empty => List.empty,
        List.cons s rest =>
            if String.beq (Book.Story.group s) group
            then List.cons (Ui.nav_item (Book.Story.id s) (Book.Story.title s) (String.concat "#" (Book.Story.id s)))
                (items_in group rest)
            else items_in group rest,
    }

#[terminating]
def nav_groups (groups : List String) (stories : List Book.Story) : List Ui.NavGroup :=
    match groups {
        List.empty => List.empty,
        List.cons g rest => List.cons (Ui.nav_group g (items_in g stories)) (nav_groups rest stories),
    }

def search_msg (q : String) : Book.Msg := Book.Msg.book_search q

def select_msg (id : String) : Book.Msg := Book.Msg.book_select id

def sidebar (stories : List Book.Story) (m : Book.Model) : List (Oak.Node Book.Msg) :=
    let shown : List Book.Story := filter_stories m.query stories in
    [Html.div [Html.class_ ["book-search"]]
        [Ui.text_input [Ui.full, Ui.small] m.query search_msg
            [Html.placeholder "Search stories", Html.aria "label" "Search stories"]],
        if List.is_empty shown
        then Html.div [Html.class_ ["book-search-empty"]] [Ui.muted [Ui.small] List.empty [Html.text "No stories match."]]
        else Ui.sidebar_nav List.empty "Stories" (nav_groups (group_names shown List.empty) shown) m.selected
            (Option.some select_msg)]

// ═══ View: header ═══

def theme_button (current : String) (value : String) (label : String) : Oak.Node Book.Msg :=
    let active : Bool := String.beq current value in
    Ui.button [Ui.small, if active then Ui.primary else Ui.outline]
        [Html.aria "pressed" (if active then "true" else "false"), Html.on_click (Book.Msg.book_theme value)]
        [Html.text label]

def viewport_msg (v : String) : Book.Msg := Book.Msg.book_viewport v

def header (m : Book.Model) : List (Oak.Node Book.Msg) :=
    [Ui.row [Ui.gap 3, Ui.cls ["book-header"]] List.empty
        [Ui.icon_button [Ui.ghost, Ui.cls ["book-menu"]] "Toggle stories" (Ui.icon "menu")
            [Html.aria "expanded" (if m.nav_open then "true" else "false"), Html.on_click Book.Msg.book_toggle_nav],
            Html.strong [Html.class_ ["book-brand"]] [Html.text "oak_ui book"],
            Ui.spacer,
            Ui.button_group List.empty "Theme" List.empty
                [theme_button m.theme "light" "Light", theme_button m.theme "dark" "Dark", theme_button m.theme "both" "Both"],
            Ui.select [Ui.small]
                [Pair.pair "full" "Full width", Pair.pair "desktop" "Desktop 1200", Pair.pair "tablet" "Tablet 768",
                    Pair.pair "mobile" "Mobile 375"]
                m.viewport viewport_msg [Html.aria "label" "Viewport"],
            Ui.button [Ui.small, Ui.ghost] [Html.on_click Book.Msg.book_reset] [Html.text "Reset story"]]]

// ═══ View: canvas ═══

def viewport_width (v : String) : String :=
    if String.beq v "mobile" then "375px"
    else if String.beq v "tablet" then "768px"
    else if String.beq v "desktop" then "1200px"
    else "none"

/// The key that forces fresh story DOM on a story switch or a reset.
def story_key (m : Book.Model) : String := String.concat_list [m.selected, "/", I64.to_string m.generation]

def frame (scope : String) (theme : String) (viewport : String) (node : Oak.Node Book.Msg) : Oak.Node Book.Msg :=
    Html.div
        [Html.key (String.concat_list [theme, "/", scope]), Html.class_ ["book-frame"], Html.attr "data-theme" theme,
            Html.style_attr (String.concat "max-width: " (viewport_width viewport))]
        [Html.div [Html.class_ ["book-frame__label"]] [Html.text theme], node]

def canvas (m : Book.Model) (story : Book.Story) (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    let frames : List (Oak.Node Book.Msg) :=
        if String.beq m.theme "both"
        then [frame (story_key m) "light" m.viewport (Book.Story.render story ctx),
            frame (story_key m) "dark" m.viewport (Book.Story.render story ctx)]
        else [frame (story_key m) m.theme m.viewport (Book.Story.render story ctx)] in
    Html.div [Html.class_list [Pair.pair "book-canvas" true, Pair.pair "book-canvas--both" (String.beq m.theme "both")]]
        frames

// ═══ View: addon panels ═══

def knob_msg (name : String) : String -> Book.Msg := fn (v : String) => Book.Msg.book_knob name v

def knob_bool_msg (name : String) : Bool -> Book.Msg :=
    fn (b : Bool) => Book.Msg.book_knob name (if b then "true" else "false")

#[terminating]
def choice_pairs (xs : List String) : List (Pair String String) :=
    match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons (Pair.pair x x) (choice_pairs rest),
    }

def knob_control (ctx : Book.Ctx) (k : Book.Knob) : Oak.Node Book.Msg :=
    let name : String := Book.Knob.name k in
    let value : String := Book.lookup_or ctx.knobs name "" in
    let id : String := String.concat "knob-" name in
    match k {
        Book.Knob.knob_text _ _ => Ui.field List.empty id name "" "" (Ui.text_input [Ui.full] value (knob_msg name)),
        Book.Knob.knob_bool _ _ => Ui.switch List.empty name (String.beq value "true") (knob_bool_msg name) List.empty,
        Book.Knob.knob_choice _ options _ =>
            Ui.field List.empty id name "" "" (Ui.select List.empty (choice_pairs options) value (knob_msg name)),
        Book.Knob.knob_int _ _ => Ui.field List.empty id name "" "" (Ui.input List.empty "number" value (knob_msg name)),
    }

#[terminating]
def knob_controls (ctx : Book.Ctx) (ks : List Book.Knob) : List (Oak.Node Book.Msg) :=
    match ks {
        List.empty => List.empty,
        List.cons k rest => List.cons (knob_control ctx k) (knob_controls ctx rest),
    }

def controls_panel (scope : String) (story : Book.Story) (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    let ks : List Book.Knob := Book.Story.knobs story in
    if List.is_empty ks
    then Ui.muted List.empty List.empty [Html.text "This story has no knobs."]
    else Html.div [Html.key scope, Html.class_ ["book-controls"]] (knob_controls ctx ks)

#[terminating]
def text_items (xs : List String) : List (Oak.Node Book.Msg) :=
    match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons (Ui.code x) (text_items rest),
    }

def actions_panel (m : Book.Model) : Oak.Node Book.Msg :=
    if List.is_empty m.log
    then Ui.muted List.empty List.empty [Html.text "Interact with the story; the messages it sends appear here."]
    else
        Ui.stack [Ui.gap 2] List.empty
            [Ui.row List.empty List.empty
                [Ui.muted [Ui.small] List.empty
                    [Html.text (String.concat_list [I64.to_string (List.length m.log), " message(s), newest first"])],
                    Ui.spacer,
                    Ui.button [Ui.small, Ui.ghost] [Html.on_click Book.Msg.book_clear_log] [Html.text "Clear"]],
                Ui.list_group List.empty (text_items m.log)]

#[terminating]
def badges (xs : List String) : List (Oak.Node Book.Msg) :=
    match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons (Ui.badge [Ui.info] x) (badges rest),
    }

def source_panel (node : Oak.Node Book.Msg) : Oak.Node Book.Msg :=
    let events : List String :=
        match Oak.lower node { Oak.Lowered.lowered tree _ => Book.listeners tree } in
    Ui.stack [Ui.gap 3] List.empty
        [Ui.cluster List.empty List.empty
            (List.cons (Ui.muted [Ui.small] List.empty
                [Html.text (if List.is_empty events then "No listeners." else "Listeners:")])
                (badges events)),
            Ui.code_block List.empty (Book.pretty_html (Oak.to_html node))]

#[terminating]
def finding_alerts (xs : List String) : List (Oak.Node Book.Msg) :=
    match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons (Ui.alert [Ui.danger] "" Option.none List.empty [Html.text x]) (finding_alerts rest),
    }

def a11y_panel (node : Oak.Node Book.Msg) : Oak.Node Book.Msg :=
    let findings : List String := Book.a11y_lint (Oak.to_html node) in
    if List.is_empty findings
    then Ui.alert [Ui.success] "No issues found" Option.none List.empty
        [Html.text "Labels, names, alt text, ARIA id references and id uniqueness all check out."]
    else Ui.stack [Ui.gap 2] List.empty (finding_alerts findings)

def is_colour (v : String) : Bool := String.starts_with "#" v || String.starts_with "rgb" v

def swatch (v : String) : Oak.Node Book.Msg :=
    if is_colour v
    then Html.span [Html.class_ ["book-swatch"], Html.style_attr (String.concat "background: " v), Html.aria "hidden" "true"] List.empty
    else Html.span List.empty List.empty

def token_value (v : String) : Oak.Node Book.Msg :=
    Html.span [Html.class_ ["book-token"]] [swatch v, Ui.code v]

#[terminating]
def token_rows (light : List (Pair String String)) (dark : List (Pair String String)) : List (Pair String (Oak.Node Book.Msg)) :=
    match light {
        List.empty => List.empty,
        List.cons p rest =>
            match p {
                Pair.pair name v =>
                    List.cons
                        (Pair.pair (String.concat "--oak-" name)
                            (Html.span [Html.class_ ["book-token-pair"]] [token_value v, token_value (Book.lookup_or dark name "")]))
                        (token_rows rest dark)
            },
    }

def tokens_panel : Oak.Node Book.Msg :=
    Ui.stack [Ui.gap 3] List.empty
        [Ui.muted [Ui.small] List.empty [Html.text "Each token: light value, then dark value."],
            Ui.description_list List.empty (token_rows (Ui.Theme.tokens Ui.Theme.light) (Ui.Theme.tokens Ui.Theme.dark))]

def panel_msg (p : String) : Book.Msg := Book.Msg.book_panel p

def addons (m : Book.Model) (story : Book.Story) (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    let node : Oak.Node Book.Msg := Book.Story.render story ctx in
    Ui.tabs [Ui.cls ["book-addons"]] "addons"
        [Ui.tab "controls" "Controls" (controls_panel (story_key m) story ctx),
            Ui.tab "actions" (String.concat "Actions" (if List.is_empty m.log then "" else String.concat_list [" (", I64.to_string (List.length m.log), ")"]))
                (actions_panel m),
            Ui.tab "source" "Source" (source_panel node),
            Ui.tab "a11y" "A11y" (a11y_panel node),
            Ui.tab "tokens" "Tokens" tokens_panel]
        m.panel panel_msg

// ═══ View ═══

#[terminating]
def find_story (stories : List Book.Story) (id : String) : Option Book.Story :=
    match stories {
        List.empty => Option.none,
        List.cons s rest => if String.beq (Book.Story.id s) id then Option.some s else find_story rest id,
    }

def story_view (m : Book.Model) (story : Book.Story) : List (Oak.Node Book.Msg) :=
    let ctx : Book.Ctx := Book.ctx_for story (Book.scoped m.knobs m.selected) (Book.scoped m.state m.selected) in
    [Ui.stack [Ui.gap 1, Ui.cls ["book-title"]] List.empty
        [Ui.muted [Ui.small] List.empty [Html.text (Book.Story.group story)],
            Ui.heading 1 List.empty List.empty [Html.text (Book.Story.title story)],
            Ui.text List.empty List.empty [Html.text (Book.Story.notes story)]],
        canvas m story ctx,
        addons m story ctx]

pub def Book.view (stories : List Book.Story) (m : Book.Model) : Oak.Node Book.Msg :=
    let content : List (Oak.Node Book.Msg) :=
        match find_story stories m.selected {
            Option.some story => story_view m story,
            Option.none => [Ui.empty_state List.empty "No story selected" "Pick one from the sidebar." List.empty],
        } in
    Ui.app_shell [Ui.cls ["book"]] m.nav_open (header m) (sidebar stories m) content
        [Ui.muted [Ui.small] List.empty [Html.text "oak_ui \u{00B7} components for Oak"]]

/// The explorer as an Oak program.
pub def Book.program (stories : List Book.Story) : Program Book.Model Book.Msg Book.Effect :=
    Program.with_subs (Book.init stories) (Book.update stories) (Book.view stories) Book.subscriptions

// ═══ The explorer's own chrome ═══

/// Layout for the explorer around the stories (components style
/// themselves through `Ui.css_all`).
pub def Book.css : String := r#"
.book .oak-shell__main { display: flex; flex-direction: column; gap: calc(var(--oak-space) * 5); }
.book-header { padding: calc(var(--oak-space) * 2) calc(var(--oak-space) * 4); }
.book-brand { font-size: 1.0625em; }
.book-menu { display: none; }
@media (max-width: 768px) { .book-menu { display: inline-flex; } }
.book-search { padding: calc(var(--oak-space) * 3) calc(var(--oak-space) * 3) 0; }
.book-search-empty { padding: calc(var(--oak-space) * 4); }
.book-canvas { display: flex; flex-direction: column; gap: calc(var(--oak-space) * 4); }
.book-canvas--both { flex-direction: row; flex-wrap: wrap; }
.book-canvas--both .book-frame { flex: 1 1 22rem; }
.book-frame {
  position: relative; transform: translateZ(0); overflow: auto; min-height: 16rem; width: 100%; box-sizing: border-box;
  padding: calc(var(--oak-space) * 8) calc(var(--oak-space) * 6) calc(var(--oak-space) * 6);
  border: 1px solid var(--oak-border); border-radius: var(--oak-radius-lg);
  background: var(--oak-bg); color: var(--oak-text);
}
.book-frame__label {
  position: absolute; top: calc(var(--oak-space) * 2); right: calc(var(--oak-space) * 3);
  font-size: 0.6875em; text-transform: uppercase; letter-spacing: 0.08em; color: var(--oak-muted);
}
.book-controls { display: grid; grid-template-columns: repeat(auto-fill, minmax(14rem, 1fr)); gap: calc(var(--oak-space) * 4); }
.book-token-pair { display: inline-flex; gap: calc(var(--oak-space) * 4); flex-wrap: wrap; }
.book-token { display: inline-flex; align-items: center; gap: calc(var(--oak-space) * 2); }
.book-tile {
  padding: calc(var(--oak-space) * 3); border-radius: var(--oak-radius-md);
  background: var(--oak-primary-soft); color: var(--oak-primary); font-weight: 550; text-align: center;
}
.book-pad { padding: calc(var(--oak-space) * 3); }
.book-shell-demo { height: 22rem; overflow: hidden; border: 1px solid var(--oak-border); border-radius: var(--oak-radius-md); }
.book-shell-demo .oak-shell { min-height: 100%; height: 100%; }
.book-swatch { width: 1em; height: 1em; border-radius: var(--oak-radius-sm); border: 1px solid var(--oak-border-strong); }
"#
