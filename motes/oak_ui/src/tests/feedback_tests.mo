/// Goldens and behaviour for feedback components.

use web_event::event {WebEvent}
use oak::typed {Oak.Node}
use oak::elements {Html.text}
use lib::tests::support {ui_renders, ui_has, ui_first_msg, ui_handler_count}
use lib::vocab {Ui.Tone, Ui.danger, Ui.success, Ui.solid, Ui.small}
use lib::feedback {
    Ui.Toast, Ui.alert, Ui.badge, Ui.tag, Ui.spinner, Ui.progress, Ui.skeleton, Ui.empty_state,
    Ui.toast, Ui.toast_region,
}

type FeedbackTestMsg { closed, removed, dismissed (id : String) }

def dismissed_id (m : Option FeedbackTestMsg) : String :=
    match m {
        Option.some msg =>
            match msg {
                FeedbackTestMsg.dismissed id => id,
                FeedbackTestMsg.closed => "closed",
                FeedbackTestMsg.removed => "removed",
            },
        Option.none => "",
    }

def click : WebEvent := { kind := "click" }

#[test]
def test_alert_info_is_status : Bool :=
    let a : Oak.Node FeedbackTestMsg := Ui.alert List.empty "Heads up" Option.none List.empty [Html.text "Body"] in
    ui_renders a
        "<div class=\"oak-alert oak-tone-info\" role=\"status\"><div class=\"oak-alert__content\"><strong class=\"oak-alert__title\">Heads up</strong><div class=\"oak-alert__body\">Body</div></div></div>"

#[test]
def test_alert_danger_is_alert_and_dismissable : Bool :=
    let a : Oak.Node FeedbackTestMsg :=
        Ui.alert [Ui.danger] "" (Option.some FeedbackTestMsg.closed) List.empty [Html.text "Failed"] in
    ui_has a "<div class=\"oak-alert oak-tone-danger\" role=\"alert\">"
        && ui_has a "aria-label=\"Dismiss\""
        && String.beq (dismissed_id (ui_first_msg a click)) "closed"

#[test]
def test_badge_variants : Bool :=
    ui_renders (Ui.badge [Ui.success] "Active") "<span class=\"oak-badge oak-tone-success\">Active</span>"
        && ui_renders (Ui.badge [Ui.danger, Ui.solid, Ui.small] "3")
            "<span class=\"oak-badge oak-badge--solid oak-badge--sm oak-tone-danger\">3</span>"

#[test]
def test_tag_removable : Bool :=
    let t : Oak.Node FeedbackTestMsg := Ui.tag List.empty "rust" (Option.some FeedbackTestMsg.removed) in
    ui_has t "<span class=\"oak-tag oak-tone-neutral\"><span class=\"oak-tag__label\">rust</span>"
        && ui_has t "aria-label=\"Remove rust\""
        && String.beq (dismissed_id (ui_first_msg t click)) "removed"

#[test]
def test_tag_static_has_no_handler : Bool :=
    let t : Oak.Node FeedbackTestMsg := Ui.tag List.empty "rust" Option.none in
    I64.beq (ui_handler_count t) 0

#[test]
def test_spinner_announces : Bool :=
    ui_renders (Ui.spinner List.empty "Loading")
        "<span class=\"oak-spinner oak-tone-neutral\" role=\"status\"><span class=\"oak-sr-only\">Loading</span></span>"

#[test]
def test_progress_determinate_and_not : Bool :=
    ui_renders (Ui.progress List.empty "Upload" 3 10)
        "<progress class=\"oak-progress oak-tone-primary\" aria-label=\"Upload\" value=\"3\" max=\"10\"></progress>"
        && ui_renders (Ui.progress List.empty "Working" 0 0)
            "<progress class=\"oak-progress oak-tone-primary\" aria-label=\"Working\"></progress>"

#[test]
def test_skeleton_lines : Bool :=
    ui_renders (Ui.skeleton List.empty 2)
        "<div class=\"oak-skeleton\" aria-hidden=\"true\"><div class=\"oak-skeleton__line\"></div><div class=\"oak-skeleton__line\"></div></div>"

#[test]
def test_empty_state_without_actions : Bool :=
    ui_renders (Ui.empty_state List.empty "No tasks" "Add one to start." List.empty)
        "<div class=\"oak-empty\"><p class=\"oak-empty__title\">No tasks</p><p class=\"oak-empty__description\">Add one to start.</p></div>"

#[test]
def test_toast_region_keys_and_dismiss : Bool :=
    let ts : List Ui.Toast :=
        [Ui.toast "t1" Ui.Tone.tone_success "Saved" "", Ui.toast "t2" Ui.Tone.tone_danger "Oops" "Try again"] in
    let r : Oak.Node FeedbackTestMsg := Ui.toast_region List.empty ts FeedbackTestMsg.dismissed in
    ui_has r "<div class=\"oak-toasts\" role=\"region\" aria-label=\"Notifications\" aria-live=\"polite\">"
        && ui_has r "<div data-oak-key=\"t1\" class=\"oak-toast oak-tone-success\" role=\"status\">"
        && ui_has r "<div data-oak-key=\"t2\" class=\"oak-toast oak-tone-danger\" role=\"alert\">"
        && ui_has r "<p class=\"oak-toast__body\">Try again</p>"
        && String.beq (dismissed_id (ui_first_msg r click)) "t1"
        && I64.beq (ui_handler_count r) 2
