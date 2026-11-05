// Stories: layout and typography.

use oak::typed {Oak.Node}
use oak::elements {Html.div, Html.text, Html.class_}
use oak_ui::vocab {Ui.Opt, Ui.gap, Ui.cols, Ui.wrapping, Ui.small, Ui.cls}
use oak_ui::layout {Ui.stack, Ui.row, Ui.cluster, Ui.grid, Ui.container, Ui.center, Ui.spacer, Ui.divider, Ui.app_shell}
use oak_ui::typography {Ui.heading, Ui.text, Ui.muted, Ui.inline, Ui.code, Ui.code_block, Ui.kbd, Ui.link}
use oak_ui::button {Ui.button}
use oak_ui::data {Ui.card}
use lib::story {
    Book.Story, Book.Ctx, Book.Msg, Book.story, Book.int, Book.flag, Book.text, Book.knob_int, Book.knob_bool,
    Book.knob_text, Book.tone_opt, Book.size_opt, Book.tone_knob, Book.size_knob,
}

def tile (label : String) : Oak.Node Book.Msg :=
    Html.div [Html.class_ ["book-tile"]] [Html.text label]

#[terminating]
def tiles (i : I64) (n : I64) : List (Oak.Node Book.Msg) :=
    if I64.lt n i then List.empty else List.cons (tile (String.concat "Item " (I64.to_string i))) (tiles (i + 1) n)

def stack_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.stack [Ui.gap (Book.knob_int ctx "gap")] List.empty (tiles 1 (Book.knob_int ctx "items"))

def row_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    let opts : List Ui.Opt := if Book.knob_bool ctx "wrap" then [Ui.gap (Book.knob_int ctx "gap"), Ui.wrapping] else [Ui.gap (Book.knob_int ctx "gap")] in
    Ui.row opts List.empty (List.append (tiles 1 3) (List.cons Ui.spacer (tiles 4 (Book.knob_int ctx "items"))))

def grid_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.grid [Ui.cols (Book.knob_int ctx "cols"), Ui.gap 3] List.empty (tiles 1 (Book.knob_int ctx "items"))

def shell_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    let sidebar : List (Oak.Node Book.Msg) :=
        if Book.knob_bool ctx "sidebar" then [Ui.stack [Ui.gap 2, Ui.cls ["book-pad"]] List.empty (tiles 1 4)] else List.empty in
    Html.div [Html.class_ ["book-shell-demo"]]
        [Ui.app_shell List.empty false
            [Ui.row [Ui.cls ["book-pad"]] List.empty [Ui.heading 5 List.empty List.empty [Html.text "Acme"], Ui.spacer, Ui.button [Ui.small] List.empty [Html.text "Sign in"]]]
            sidebar
            [Ui.card List.empty [Html.text "Dashboard"] [Ui.text List.empty List.empty [Html.text "Main content."]] List.empty]
            [Html.text "\u{00A9} Acme"]]

def headings_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.stack [Ui.gap 2] List.empty
        [Ui.heading 1 List.empty List.empty [Html.text "Heading 1"],
            Ui.heading 2 List.empty List.empty [Html.text "Heading 2"],
            Ui.heading 3 List.empty List.empty [Html.text "Heading 3"],
            Ui.heading 4 List.empty List.empty [Html.text "Heading 4"],
            Ui.heading 5 List.empty List.empty [Html.text "Heading 5"],
            Ui.heading 6 List.empty List.empty [Html.text "Heading 6"]]

def text_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.stack [Ui.gap 3] List.empty
        [Ui.text [Book.size_opt ctx, Book.tone_opt ctx] List.empty [Html.text (Book.knob_text ctx "text")],
            Ui.muted List.empty List.empty [Html.text "Muted secondary text."],
            Ui.text List.empty List.empty
                [Html.text "Press ", Ui.kbd "Ctrl", Html.text " + ", Ui.kbd "K", Html.text " or call ",
                    Ui.code "Ui.button", Html.text ". Read the ", Ui.link List.empty "#" List.empty [Html.text "docs"], Html.text "."],
            Ui.code_block List.empty "def main : IO Unit :=\n    IO.println \"Hello, oak_ui\""]

pub def foundation_stories : List Book.Story :=
    [Book.story "layout-stack" "Layout" "Stack" "A vertical flex column. Gap is a step on the theme's spacing scale."
        [Book.int "gap" 3, Book.int "items" 3] stack_story,
        Book.story "layout-row" "Layout" "Row" "A horizontal row; `Ui.spacer` pushes the rest to the end."
            [Book.int "gap" 2, Book.int "items" 6, Book.flag "wrap" false] row_story,
        Book.story "layout-grid" "Layout" "Grid" "Equal columns that collapse on narrow screens; 0 columns auto-fits."
            [Book.int "cols" 3, Book.int "items" 6] grid_story,
        Book.story "layout-shell" "Layout" "App shell" "Header, optional sidebar, main and footer."
            [Book.flag "sidebar" true] shell_story,
        Book.story "type-headings" "Typography" "Headings" "Levels 1-6." List.empty headings_story,
        Book.story "type-text" "Typography" "Text" "Paragraphs, muted text, inline code, keys, links and code blocks."
            [Book.text "text" "The quick brown fox jumps over the lazy dog.", Book.tone_knob, Book.size_knob] text_story]
