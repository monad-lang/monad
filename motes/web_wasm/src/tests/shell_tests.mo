/// The shell generator is pure, so it tests natively.

use lib::shell {ShellOptions, Shell.default_options, Shell.index_html}

#[test]
def test_shell_has_the_loader_and_mount : Bool :=
    let html : String := Shell.index_html (Shell.default_options "app.wasm") in
    String.contains html "start('./app.wasm', '#app')"
        && String.contains html "<div id=\"app\"></div>"
        && String.contains html "./web.js"

#[test]
def test_shell_escapes_nothing_but_takes_a_title_and_css : Bool :=
    let o : ShellOptions :=
        { wasm := "game.wasm", selector := "#board", title := "Game", css := "body{margin:0}" } in
    let html : String := Shell.index_html o in
    String.contains html "<title>Game</title>"
        && String.contains html "<style>\nbody{margin:0}\n</style>"
        && String.contains html "start('./game.wasm', '#board')"

#[test]
def test_shell_without_css_has_no_style_block : Bool :=
    Bool.not (String.contains (Shell.index_html (Shell.default_options "a.wasm")) "<style>")
