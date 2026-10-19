// An oak page built through the production stack and printed to stdout.
// This is the program the wasm web proof compiles to wasm32-unknown-unknown
// and runs in the browser: same builders, same HtmlT, same Render.io.
//
// The trailing newline is deliberate: wasm/web/smoke.mjs asserts stdout is
// the expected document plus exactly one newline.
#![mote { name := "oak_page", deps := [oak] }]

use oak::elements {Html.card, Html.navbar, Html.text, Html.title}
use oak::html_t {
    Page.empty, Emitted, HtmlT, HtmlT.and_then, HtmlT.body_nodes,
    HtmlT.emit, HtmlT.head_nodes, HtmlT.run, HtmlT.seal,
    Open, Render.io, Sealed
}

def links : List (Pair String String) :=
    [Pair.pair "/" "Home", Pair.pair "/docs" "Docs"]

def page_open [Monad M] : HtmlT M Open Open Unit :=
    let head : HtmlT M Open Open Unit :=
        HtmlT.head_nodes [Html.title List.empty [Html.text "Oak"]] in
    let body : HtmlT M Open Open Unit :=
        HtmlT.body_nodes
            [Html.navbar links, Html.card "Oak" "Declarative HTML in Monad"] in
    HtmlT.and_then head body

def page [Monad M] : HtmlT M Open Emitted Unit :=
    let open_phase : HtmlT M Open Open Unit := page_open in
    let seal_phase : HtmlT M Open Sealed Unit := HtmlT.seal in
    let emit_phase : HtmlT M Sealed Emitted Unit := HtmlT.emit in
    HtmlT.and_then open_phase (HtmlT.and_then seal_phase emit_phase)

def main (args : List String) : IO Unit := do {
    let prog : HtmlT IO Open Emitted Unit := page;
    let _ <- HtmlT.run prog Render.io Page.empty;
    let _ <- IO.println "";
    return Unit.unit
}
