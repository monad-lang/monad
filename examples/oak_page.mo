// An oak page printed to stdout. This is the program the wasm web proof
// compiles to wasm32-unknown-unknown and renders in the browser.
//
// It goes through the builder surface and the shared serializer only: the
// `HtmlT`/`Render` stack is exercised by motes/oak's tests, but a
// Monad-dictionary-capturing closure stored in a constructor currently
// segfaults in both compiled backends (see
// plans/implementations/dict-capturing-closure-segfault.md), so a compiled
// page program stays on the pure API until that is fixed.
//
// The trailing newline is deliberate: wasm/web/smoke.mjs asserts stdout is
// the expected document plus exactly one newline.
#![mote { name := "oak_page", deps := [oak, xml_html] }]

use oak::elements {Html.card, Html.document, Html.navbar, Html.text, Html.title}
use xml_html::html {Html.Node, Html.to_string}

def links : List (Pair String String) :=
    [Pair.pair "/" "Home", Pair.pair "/docs" "Docs"]

def page : Html.Node :=
    Html.document
        [Html.title List.empty [Html.text "Oak"]]
        [Html.navbar links, Html.card "Oak" "Declarative HTML in Monad"]

def main (args : List String) : IO Unit := do {
    let _ <- IO.write_stdout (Html.to_string page);
    let _ <- IO.println "";
    return Unit.unit
}
