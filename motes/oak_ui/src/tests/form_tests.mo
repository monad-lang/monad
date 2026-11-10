/// Goldens and behaviour for fields and controls.

use std::list {}
use web_event::event {WebEvent, FileInfo}
use oak::typed {Oak.Node}
use oak::elements {Html.text, Html.placeholder, Html.action, Html.method_}
use lib::tests::support {ui_renders, ui_has, ui_first_msg, ui_first_prevents}
use lib::vocab {Ui.required, Ui.inactive, Ui.small, Ui.full}
use lib::form {
    Ui.field, Ui.input, Ui.text_input, Ui.textarea, Ui.select, Ui.checkbox, Ui.switch,
    Ui.radio_group, Ui.range, Ui.file_input, Ui.input_group, Ui.form,
}

type FormTestMsg {
    typed (s : String),
    toggled (b : Bool),
    picked (s : String),
    got_files (n : I64),
    submitted,
}

def count_files (fs : List FileInfo) : FormTestMsg := FormTestMsg.got_files (List.length fs)

def typed_text (m : Option FormTestMsg) : String :=
    match m {
        Option.some msg =>
            match msg {
                FormTestMsg.typed s => s,
                FormTestMsg.picked s => String.concat "picked:" s,
                FormTestMsg.toggled b => if b then "on" else "off",
                FormTestMsg.got_files n => String.concat "files:" (I64.to_string n),
                FormTestMsg.submitted => "submitted",
            },
        Option.none => "",
    }

// ─── Field wiring ───

#[test]
def test_field_plain : Bool :=
    ui_renders (Ui.field List.empty "name" "Name" "" "" (Ui.text_input List.empty "Ada" FormTestMsg.typed))
        "<div class=\"oak-field\"><label class=\"oak-field__label\" for=\"name\">Name</label><input class=\"oak-input\" type=\"text\" value=\"Ada\" id=\"name\"></div>"

#[test]
def test_field_help_error_required : Bool :=
    let f : Oak.Node FormTestMsg :=
        Ui.field [Ui.required] "email" "Email" "We never share it." "Required"
            (Ui.input List.empty "email" "" FormTestMsg.typed) in
    ui_renders f
        "<div class=\"oak-field oak-field--invalid\"><label class=\"oak-field__label\" for=\"email\">Email<span class=\"oak-field__required\" aria-hidden=\"true\">*</span></label><input class=\"oak-input\" type=\"email\" value=\"\" id=\"email\" aria-describedby=\"email-help email-error\" aria-invalid=\"true\" required><p class=\"oak-field__help\" id=\"email-help\">We never share it.</p><p class=\"oak-field__error\" id=\"email-error\">Required</p></div>"

#[test]
def test_field_disabled_passes_to_control : Bool :=
    ui_has (Ui.field [Ui.inactive] "x" "X" "" "" (Ui.text_input List.empty "" FormTestMsg.typed)) "id=\"x\" disabled>"

// ─── Controls ───

#[test]
def test_text_input_attrs_last : Bool :=
    ui_renders (Ui.text_input [Ui.small, Ui.full] "v" FormTestMsg.typed [Html.placeholder "p"])
        "<input class=\"oak-input oak-input--sm oak-input--full\" type=\"text\" value=\"v\" placeholder=\"p\">"

#[test]
def test_input_reports_value : Bool :=
    let i : Oak.Node FormTestMsg := Ui.text_input List.empty "" FormTestMsg.typed List.empty in
    let e : WebEvent := { kind := "input", value := "hello" } in
    String.beq (typed_text (ui_first_msg i e)) "hello"

#[test]
def test_textarea : Bool :=
    ui_renders (Ui.textarea List.empty "a<b" FormTestMsg.typed List.empty)
        "<textarea class=\"oak-input oak-input--textarea\">a&lt;b</textarea>"

#[test]
def test_select_marks_current : Bool :=
    ui_renders (Ui.select List.empty [Pair.pair "a" "Apple", Pair.pair "b" "Banana"] "b" FormTestMsg.picked List.empty)
        "<select class=\"oak-input oak-input--select\"><option value=\"a\">Apple</option><option value=\"b\" selected>Banana</option></select>"

#[test]
def test_checkbox_markup_and_toggle : Bool :=
    let c : Oak.Node FormTestMsg := Ui.checkbox List.empty "Remember me" true FormTestMsg.toggled List.empty in
    let e : WebEvent := { kind := "change", checked := false } in
    ui_renders c
        "<label class=\"oak-check\"><input class=\"oak-check__box\" type=\"checkbox\" checked><span class=\"oak-check__label\">Remember me</span></label>"
        && String.beq (typed_text (ui_first_msg c e)) "off"

#[test]
def test_switch_has_role : Bool :=
    ui_has (Ui.switch List.empty "Dark mode" false FormTestMsg.toggled List.empty)
        "<label class=\"oak-check oak-check--switch\"><input class=\"oak-check__box\" type=\"checkbox\" role=\"switch\">"

#[test]
def test_radio_group : Bool :=
    let g : Oak.Node FormTestMsg :=
        Ui.radio_group List.empty "size" "Size" [Pair.pair "s" "Small", Pair.pair "l" "Large"] "l" FormTestMsg.picked List.empty in
    ui_has g "<div class=\"oak-radio-group\" role=\"radiogroup\" aria-label=\"Size\">"
        && ui_has g "type=\"radio\" name=\"size\" value=\"l\" checked>"
        && String.beq (typed_text (ui_first_msg g { kind := "change", value := "s" })) "picked:s"

#[test]
def test_range : Bool :=
    ui_renders (Ui.range List.empty 0 10 2 4 FormTestMsg.typed List.empty)
        "<input class=\"oak-range\" type=\"range\" min=\"0\" max=\"10\" step=\"2\" value=\"4\">"

#[test]
def test_file_input_reports_files : Bool :=
    let f : Oak.Node FormTestMsg := Ui.file_input List.empty "image/*" count_files List.empty in
    let one : FileInfo := { name := "a.png", size := 3, mime_type := "image/png", last_modified := 0 } in
    let e : WebEvent := { kind := "change", files := [one] } in
    ui_has f "type=\"file\" accept=\"image/*\"" && String.beq (typed_text (ui_first_msg f e)) "files:1"

#[test]
def test_input_group_in_field : Bool :=
    let f : Oak.Node FormTestMsg :=
        Ui.field List.empty "price" "Price" "" ""
            (Ui.input_group List.empty [Html.text "$"] (Ui.text_input List.empty "5" FormTestMsg.typed) List.empty) in
    ui_has f "<div class=\"oak-input-group\"><span class=\"oak-input-group__addon\">$</span><input class=\"oak-input\" type=\"text\" value=\"5\" id=\"price\"></div>"

#[test]
def test_form_prevents_and_falls_back : Bool :=
    let f : Oak.Node FormTestMsg :=
        Ui.form List.empty FormTestMsg.submitted [Html.action "/save", Html.method_ "post"] List.empty in
    let e : WebEvent := { kind := "submit" } in
    ui_renders f "<form class=\"oak-form\" action=\"/save\" method=\"post\"></form>"
        && ui_first_prevents f e
        && String.beq (typed_text (ui_first_msg f e)) "submitted"
