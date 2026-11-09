#![mote { name := "oak_ui_page", deps := [oak, oak_ui, xml_html] }]

// A server-rendered page built from oak_ui components: a themed document
// (light/dark from the OS, overridable with data-theme), a card with a
// form, an alert and a table. Build it and redirect the binary's output
// (`monad run` prints its own progress line on stdout first):
//     monad build examples/oak_ui_page.mo -o oak_ui_page && ./oak_ui_page > page.html

use oak::typed {Oak.Node, Oak.to_html}
use oak::elements {Html.document_utf8, Html.title, Html.style, Html.text, Html.action, Html.method_}
use xml_html::html {Html.to_string}
use oak_ui::vocab {Ui.primary, Ui.success, Ui.ghost, Ui.small, Ui.full, Ui.gap, Ui.required}
use oak_ui::theme {Ui.Theme.light, Ui.Theme.dark}
use oak_ui::base {Ui.style_tag_auto}
use oak_ui::css {Ui.css_reset}
use oak_ui::layout {Ui.container, Ui.stack, Ui.cluster}
use oak_ui::typography {Ui.heading, Ui.muted}
use oak_ui::button {Ui.submit_button, Ui.button}
use oak_ui::form {Ui.field, Ui.input, Ui.form}
use oak_ui::feedback {Ui.alert}
use oak_ui::data {Ui.card, Ui.Column, Ui.SortState.none, Ui.column, Ui.table}

/// A page with no client runtime has no messages to send.
type PageMsg { page_noop, page_typed (s : String) }

struct Member {
    name : String,
    role : String
}

def member_name (m : Member) : Oak.Node PageMsg := Html.text m.name

def member_role (m : Member) : Oak.Node PageMsg := Html.text m.role

def member_key (m : Member) : String := m.name

def ada : Member := { name := "Ada", role := "Engineer" }

def grace : Member := { name := "Grace", role := "Admiral" }

def columns : List (Ui.Column Member PageMsg) := [Ui.column "name" "Name" member_name, Ui.column "role" "Role" member_role]

def ignore_sort (_k : String) : PageMsg := PageMsg.page_noop

def invite_form : Oak.Node PageMsg :=
    Ui.form [Ui.gap 3] PageMsg.page_noop [Html.action "/invite", Html.method_ "post"]
        [Ui.field [Ui.required] "email" "Email" "We send one invitation." ""
            (Ui.input [Ui.full] "email" "" PageMsg.page_typed),
            Ui.cluster List.empty List.empty
                [Ui.submit_button [Ui.primary] List.empty [Html.text "Invite"],
                    Ui.button [Ui.ghost] List.empty [Html.text "Cancel"]]]

def body : List (Oak.Node PageMsg) :=
    [Ui.container List.empty List.empty
        [Ui.stack [Ui.gap 5] List.empty
            [Ui.heading 1 List.empty List.empty [Html.text "Team"],
                Ui.alert [Ui.success] "Saved" Option.none List.empty [Html.text "Your changes are live."],
                Ui.card List.empty [Html.text "Invite a member"] [invite_form] List.empty,
                Ui.table [Ui.small] "Members" columns [ada, grace] member_key Ui.SortState.none ignore_sort List.empty,
                Ui.muted List.empty List.empty [Html.text "Rendered on the server; no JavaScript needed."]]]]

def page : Oak.Node PageMsg :=
    Html.document_utf8
        [Html.title List.empty [Html.text "Team"], Ui.style_tag_auto Ui.Theme.light Ui.Theme.dark,
            Html.style List.empty Ui.css_reset] body

def main : IO Unit := IO.println (Html.to_string (Oak.to_html page))
