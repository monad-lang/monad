// Stories: buttons and forms.

use std::list {}
use oak::typed {Oak.Node, Oak.Attr}
use oak::elements {Html.text, Html.placeholder}
use oak::events {Html.on_click}
use oak_ui::vocab {
    Ui.Opt, Ui.primary, Ui.danger, Ui.success, Ui.neutral, Ui.solid, Ui.outline, Ui.soft, Ui.ghost, Ui.plain, Ui.small,
    Ui.large, Ui.full, Ui.busy, Ui.inactive, Ui.required, Ui.gap,
}
use oak_ui::layout {Ui.stack, Ui.cluster}
use oak_ui::button {Ui.button, Ui.submit_button, Ui.link_button, Ui.icon_button, Ui.button_group, Ui.icon}
use oak_ui::form {
    Ui.field, Ui.input, Ui.text_input, Ui.textarea, Ui.select, Ui.checkbox, Ui.switch, Ui.radio_group, Ui.range,
    Ui.file_input, Ui.input_group, Ui.form,
}
use web_event::event {FileInfo}
use lib::story {
    Book.Story, Book.Ctx, Book.Msg, Book.story, Book.text, Book.flag, Book.knob_text, Book.knob_bool,
    Book.tone_opt, Book.size_opt, Book.variant_opt, Book.tone_knob, Book.size_knob, Book.variant_knob,
    Book.action, Book.state, Book.state_bool, Book.state_int, Book.setter, Book.bool_setter, Book.logger,
}

def button_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    let mods : List Ui.Opt :=
        List.append [Book.tone_opt ctx, Book.variant_opt ctx, Book.size_opt ctx]
            (List.append (if Book.knob_bool ctx "loading" then [Ui.busy] else List.empty)
                (List.append (if Book.knob_bool ctx "disabled" then [Ui.inactive] else List.empty)
                    (if Book.knob_bool ctx "full width" then [Ui.full] else List.empty))) in
    Ui.button mods [Html.on_click (Book.action "click" (Book.knob_text ctx "label"))] [Html.text (Book.knob_text ctx "label")]

def tone_row (variant : Ui.Opt) : Oak.Node Book.Msg :=
    Ui.cluster List.empty List.empty
        [Ui.button [variant, Ui.neutral] List.empty [Html.text "Neutral"],
            Ui.button [variant, Ui.primary] List.empty [Html.text "Primary"],
            Ui.button [variant, Ui.success] List.empty [Html.text "Success"],
            Ui.button [variant, Ui.danger] List.empty [Html.text "Danger"]]

def matrix_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.stack [Ui.gap 3] List.empty [tone_row Ui.solid, tone_row Ui.soft, tone_row Ui.outline, tone_row Ui.ghost, tone_row Ui.plain]

def icon_buttons_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.stack [Ui.gap 3] List.empty
        [Ui.cluster List.empty List.empty
            [Ui.icon_button [Ui.ghost] "Search" (Ui.icon "search") [Html.on_click (Book.action "search" "")],
                Ui.icon_button [Ui.outline] "Add" (Ui.icon "plus") [Html.on_click (Book.action "add" "")],
                Ui.icon_button [Ui.danger, Ui.soft] "Delete" (Ui.icon "close") [Html.on_click (Book.action "delete" "")]],
            Ui.button_group List.empty "Alignment" List.empty
                [Ui.button [Ui.outline] [Html.on_click (Book.action "align" "left")] [Html.text "Left"],
                    Ui.button [Ui.outline] [Html.on_click (Book.action "align" "center")] [Html.text "Center"],
                    Ui.button [Ui.outline] [Html.on_click (Book.action "align" "right")] [Html.text "Right"]],
            Ui.link_button [Ui.primary, Ui.soft] "#" List.empty [Html.text "A link styled as a button", Ui.icon "external"]]

def email_error (ctx : Book.Ctx) : String :=
    let v : String := Book.state ctx "email" "" in
    if Book.knob_bool ctx "show error" && Bool.not (String.contains v "@") then "Enter an email address with an @." else ""

def field_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.field (if Book.knob_bool ctx "required" then [Ui.required] else List.empty)
        "story-email" (Book.knob_text ctx "label") (Book.knob_text ctx "help") (email_error ctx)
        (Ui.input [Ui.full] "email" (Book.state ctx "email" "") (Book.setter "email"))

def controls_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.stack [Ui.gap 4] List.empty
        [Ui.field List.empty "c-name" "Name" "" "" (Ui.text_input [Ui.full] (Book.state ctx "name" "") (Book.setter "name")),
            Ui.field List.empty "c-bio" "Bio" "A few words." "" (Ui.textarea [Ui.full] (Book.state ctx "bio" "") (Book.setter "bio")),
            Ui.field List.empty "c-plan" "Plan" "" ""
                (Ui.select [Ui.full] [Pair.pair "free" "Free", Pair.pair "pro" "Pro", Pair.pair "team" "Team"]
                    (Book.state ctx "plan" "pro") (Book.setter "plan")),
            Ui.checkbox List.empty "Email me about updates" (Book.state_bool ctx "updates") (Book.bool_setter "updates") List.empty,
            Ui.switch List.empty "Dark mode" (Book.state_bool ctx "dark") (Book.bool_setter "dark") List.empty,
            Ui.radio_group List.empty "story-size" "Size" [Pair.pair "s" "Small", Pair.pair "m" "Medium", Pair.pair "l" "Large"]
                (Book.state ctx "size" "m") (Book.setter "size") List.empty,
            Ui.field List.empty "c-volume" "Volume" "" ""
                (Ui.range List.empty 0 100 5 (Book.state_int ctx "volume" 40) (Book.setter "volume")),
            Ui.field List.empty "c-price" "Price" "" ""
                (Ui.input_group List.empty [Html.text "$"] (Ui.input List.empty "number" (Book.state ctx "price" "10") (Book.setter "price")) [Html.text ".00"]),
            Ui.field List.empty "c-file" "Attachment" "" "" (Ui.file_input List.empty "image/*" files_msg)]

def files_msg (fs : List FileInfo) : Book.Msg := Book.action "files" (I64.to_string (List.length fs))

def form_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.form List.empty (Book.action "submit" (Book.state ctx "title" "")) List.empty
        [Ui.field [Ui.required] "f-title" "Title" "" "" (Ui.text_input [Ui.full] (Book.state ctx "title" "") (Book.setter "title")),
            Ui.cluster List.empty List.empty
                [Ui.submit_button [Ui.primary] List.empty [Html.text "Create"],
                    Ui.button [Ui.ghost] [Html.on_click (Book.action "cancel" "")] [Html.text "Cancel"]]]

pub def control_stories : List Book.Story :=
    [Book.story "button" "Actions" "Button" "Tone, variant and size are independent modifiers. A busy button is disabled and aria-busy."
        [Book.text "label" "Save changes", Book.tone_knob, Book.variant_knob, Book.size_knob,
            Book.flag "loading" false, Book.flag "disabled" false, Book.flag "full width" false] button_story,
        Book.story "button-matrix" "Actions" "Tones and variants" "Every tone in every variant." List.empty matrix_story,
        Book.story "icon-buttons" "Actions" "Icon buttons and groups" "Icon-only buttons carry their name in aria-label." List.empty icon_buttons_story,
        Book.story "field" "Forms" "Field" "Label, help and error are wired to the control (for, aria-describedby, aria-invalid)."
            [Book.text "label" "Email", Book.text "help" "We never share it.", Book.flag "required" true, Book.flag "show error" true]
            field_story,
        Book.story "controls" "Forms" "Controls" "Every input type, controlled by story state." List.empty controls_story,
        Book.story "form" "Forms" "Form" "Submit is prevented and becomes a message; action/method keep a no-JS fallback." List.empty form_story]
