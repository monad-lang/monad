// The static gallery: every story rendered with its default knobs, as
// plain server-rendered HTML (no handlers, no runtime).

use std::list {List.intercalate}
use xml_html::html {Html.to_string}
use oak::typed {Oak.Node, Oak.to_html}
use oak::elements {
    Html.document_utf8, Html.document_with, Html.title, Html.meta, Html.link, Html.name_, Html.attr, Html.rel,
    Html.href, Html.charset, Html.div, Html.section, Html.text, Html.class_, Html.id_, Html.a,
}
use oak_ui::theme {Ui.Theme.light, Ui.Theme.dark}
use oak_ui::css {Ui.stylesheet_auto, Ui.css_reset}
use oak_ui::layout {Ui.stack, Ui.container}
use oak_ui::typography {Ui.heading, Ui.text, Ui.muted}
use oak_ui::vocab {Ui.gap, Ui.cls, Ui.small}
use lib::story {Book.Story, Book.Msg, Book.Story.id, Book.Story.group, Book.Story.title, Book.Story.notes, Book.Story.render, Book.default_ctx}
use lib::app {Book.css}

/// The stylesheet both the gallery and the live explorer load: light/dark
/// variables, the component sheet, a page reset and the explorer chrome.
pub def Book.stylesheet : String :=
    String.concat_list [Ui.stylesheet_auto Ui.Theme.light Ui.Theme.dark, Ui.css_reset, Book.css]

def page {Msg : Type} (title : String) (body : List (Oak.Node Msg)) : String :=
    Html.to_string (Oak.to_html
        (Html.document_with [Html.attr "lang" "en"] List.empty List.empty
            [Html.meta [Html.charset "utf-8"],
                Html.meta [Html.name_ "viewport", Html.attr "content" "width=device-width, initial-scale=1"],
                Html.title List.empty [Html.text title],
                Html.link [Html.rel "stylesheet", Html.href "oak-ui.css"]]
            body))

def frame (theme : String) (story : Book.Story) : Oak.Node Book.Msg :=
    Html.div [Html.class_ ["book-frame"], Html.attr "data-theme" theme]
        [Html.div [Html.class_ ["book-frame__label"]] [Html.text theme], Book.Story.render story (Book.default_ctx story)]

def story_section (story : Book.Story) : Oak.Node Book.Msg :=
    Html.section [Html.id_ (Book.Story.id story), Html.class_ ["book-gallery__story"]]
        [Ui.stack [Ui.gap 1] List.empty
            [Ui.muted [Ui.small] List.empty [Html.text (Book.Story.group story)],
                Ui.heading 2 List.empty List.empty
                    [Html.a [Html.class_ ["oak-link"], Html.href (String.concat (Book.Story.id story) ".html")] [Html.text (Book.Story.title story)]],
                Ui.text List.empty List.empty [Html.text (Book.Story.notes story)]],
            Html.div [Html.class_ ["book-canvas", "book-canvas--both"]] [frame "light" story, frame "dark" story]]

#[terminating]
def sections (stories : List Book.Story) : List (Oak.Node Book.Msg) :=
    match stories {
        List.empty => List.empty,
        List.cons s rest => List.cons (story_section s) (sections rest),
    }

/// `index.html`: every story, light and dark side by side.
pub def Book.gallery_page (stories : List Book.Story) : String :=
    page "oak_ui gallery"
        [Ui.container [Ui.cls ["book-gallery"]] List.empty
            (List.cons (Ui.heading 1 List.empty List.empty [Html.text "oak_ui gallery"]) (sections stories))]

/// `<id>.html`: one story alone (a stable target for visual snapshots).
pub def Book.story_page (story : Book.Story) : String :=
    page (String.concat (Book.Story.title story) " \u{00B7} oak_ui")
        [Ui.container [Ui.cls ["book-gallery"]] List.empty [story_section story]]
