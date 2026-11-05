/// Goldens for layout and typography.

use oak::elements {Html.text, Html.id_}
use lib::tests::support {ui_renders, ui_has}
use lib::vocab {Ui.gap, Ui.cols, Ui.cls, Ui.small, Ui.danger, Ui.wrapping}
use lib::layout {Ui.stack, Ui.row, Ui.grid, Ui.container, Ui.divider, Ui.app_shell}
use lib::typography {Ui.heading, Ui.text, Ui.muted, Ui.code_block, Ui.kbd, Ui.link}

#[test]
def test_stack_default : Bool :=
    ui_renders (Ui.stack List.empty List.empty [Html.text "a"])
        "<div class=\"oak-stack oak-gap-3 oak-align-stretch oak-justify-start\">a</div>"

#[test]
def test_row_gap_wrap_and_attrs : Bool :=
    ui_renders (Ui.row [Ui.gap 1, Ui.wrapping, Ui.cls ["mine"]] [Html.id_ "r"] List.empty)
        "<div class=\"oak-row oak-row--wrap oak-gap-1 oak-align-center oak-justify-start mine\" id=\"r\"></div>"

#[test]
def test_gap_clamps : Bool :=
    ui_has (Ui.stack [Ui.gap 99] List.empty List.empty) "oak-gap-8"

#[test]
def test_grid_cols : Bool :=
    ui_renders (Ui.grid [Ui.cols 3] List.empty List.empty)
        "<div class=\"oak-grid oak-grid--cols-3 oak-gap-3\"></div>"
        && ui_has (Ui.grid [Ui.cols 0] List.empty List.empty) "oak-grid--auto"
        && ui_renders (Ui.grid List.empty List.empty List.empty) "<div class=\"oak-grid oak-gap-3\"></div>"

#[test]
def test_container_sizes : Bool :=
    ui_renders (Ui.container [Ui.small] List.empty List.empty)
        "<div class=\"oak-container oak-container--sm\"></div>"

#[test]
def test_divider : Bool :=
    ui_renders (Ui.divider List.empty) "<hr class=\"oak-divider\">"

#[test]
def test_app_shell_without_sidebar : Bool :=
    ui_renders (Ui.app_shell List.empty false [Html.text "h"] List.empty [Html.text "m"] [Html.text "f"])
        "<div class=\"oak-shell oak-shell--no-sidebar\"><header class=\"oak-shell__header\">h</header><main class=\"oak-shell__main\">m</main><footer class=\"oak-shell__footer\">f</footer></div>"

#[test]
def test_app_shell_sidebar_open : Bool :=
    ui_has (Ui.app_shell List.empty true List.empty [Html.text "s"] List.empty List.empty)
        "<div class=\"oak-shell oak-shell--nav-open\"><header class=\"oak-shell__header\"></header><aside class=\"oak-shell__sidebar\">s</aside>"

#[test]
def test_heading_level_clamped : Bool :=
    ui_renders (Ui.heading 2 List.empty List.empty [Html.text "T"])
        "<h2 class=\"oak-heading oak-heading--2\">T</h2>"
        && ui_has (Ui.heading 9 List.empty List.empty List.empty) "<h6 class=\"oak-heading oak-heading--6\">"

#[test]
def test_text_modifiers : Bool :=
    ui_renders (Ui.text [Ui.small, Ui.danger] List.empty [Html.text "x"])
        "<p class=\"oak-text oak-text--sm oak-text--danger\">x</p>"
        && ui_renders (Ui.muted List.empty List.empty List.empty) "<p class=\"oak-text oak-text--muted\"></p>"

#[test]
def test_code_block_escapes : Bool :=
    ui_renders (Ui.code_block List.empty "a < b")
        "<pre class=\"oak-code-block\"><code>a &lt; b</code></pre>"

#[test]
def test_kbd_and_link : Bool :=
    ui_renders (Ui.kbd "Ctrl") "<kbd class=\"oak-kbd\">Ctrl</kbd>"
        && ui_renders (Ui.link List.empty "/x" List.empty [Html.text "go"])
            "<a class=\"oak-link\" href=\"/x\">go</a>"
