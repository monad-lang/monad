/// Server-side rendering: turn Oak pages into `http.Response`s.
///
/// Oak owns the page and the serializer; `moon` owns the wire. Keeping the
/// adapter here means a JSON API server that depends on `moon` never pulls
/// `xml_html`/`parsec` into its closure, and Oak never depends on the server.
///
/// `Render`'s type stays `String -> M Unit`: the response sink is a `Ref`
/// captured by a `Render PageM`, so `HtmlT`/`PageM` programs compose exactly
/// as they do against stdout.

use std::ref {Ref, Ref.get, Ref.new, Ref.set}
use init::transformers {ResultT}
use http::types {Response, Response.html}
use lib::elements {Html.document}
use lib::html_t {
  Emitted, HtmlT, HtmlT.run, Open, Page, Page.empty, PageM, Render,
}
use xml_html::html {Html.Node, Html.RenderOpts, Html.to_string, Html.to_string_with}

/// Render a page as a document with the given options.
pub def Ssr.render_page (opts : Html.RenderOpts) (page : Page) : String :=
  Html.to_string_with opts (Html.document page.head page.body)

/// Render a single node (a body fragment, a component) without a document
/// wrapper.
pub def Ssr.render_body (node : Html.Node) : String :=
  Html.to_string node

pub def Ssr.to_response (status : U16) (opts : Html.RenderOpts) (page : Page) : Response :=
  Response.html status (Ssr.render_page opts page)

pub def Ssr.to_response_node (status : U16) (node : Html.Node) : Response :=
  Response.html status (Html.to_string node)

/// A 200 HTML response for a fragment (no doctype/html wrapper).
pub def Ssr.fragment_response (node : Html.Node) : Response :=
  Ssr.to_response_node 200u16 node

/// Capture one write into `buf`.
def Ssr.capture (buf : Ref String) (s : String) : IO (Result String Unit) := do {
  Ref.set buf s;
  return (Result.ok Unit.unit)
}

/// Run a `PageM` page program and return the emitted document as an HTML
/// response. A generation failure is `Err`; a successful run whose `emit`
/// never wrote returns an empty document (the program's own choice).
pub def Ssr.render_io (page_m : HtmlT PageM Open Emitted Unit) : IO (Result String Response) := do {
  let buf <- Ref.new "";
  let sink : Render PageM :=
    Render.render (fn (s : String) => PageM.page_m (ResultT.mk (Ssr.capture buf s)));
  let ran <- ResultT.run (PageM.run (HtmlT.run page_m sink Page.empty));
  match ran {
    Result.err e => return (Result.err e),
    Result.ok _ => do {
      let html <- Ref.get buf;
      return (Result.ok (Response.html 200u16 html))
    }
  }
}
