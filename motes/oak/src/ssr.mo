/// Server-side rendering: turn Oak pages into `http.Response`s.
///
/// Oak owns the page and the serializer; `moon` owns the wire. Keeping the
/// adapter here means a JSON API server that depends on `moon` never pulls
/// `xml_html`/`parsec` into its closure, and Oak never depends on the server.
///
/// `Render`'s type stays `String -> M Unit`: the response sink is a `Ref`
/// captured by a `Render PageM`, so `HtmlT`/`PageM` programs compose exactly
/// as they do against stdout.

use init::transformers {ResultT, ResultT.lift}
use http::types {Response, Response.html}
use lib::elements {Html.document, Html.document_utf8}
use lib::html_t {
  Emitted, HtmlT, HtmlT.run, Open, Page, Page.empty, PageM, Render,
}
use lib::typed {Oak.Node, Oak.to_html}
use xml_html::html {
  Html.RenderOpts, Html.default_opts, Html.to_string, Html.to_string_with,
}

/// Render a page as a document with the given options. `charset` prepends
/// `<meta charset="utf-8">` to the head; without it the document is the same
/// one `Html.document` always produced.
pub def Ssr.render_page (opts : Html.RenderOpts) (page : Page) : String :=
  if opts.charset
  then Html.to_string_with opts (Oak.to_html (Html.document_utf8 page.head page.body))
  else Html.to_string_with opts (Oak.to_html (Html.document page.head page.body))

/// Render a single node (a body fragment, a component) without a document
/// wrapper.
pub def Ssr.render_body (node : Oak.Node Msg) : String :=
  Html.to_string (Oak.to_html node)

pub def Ssr.to_response (status : U16) (opts : Html.RenderOpts) (page : Page) : Response :=
  Response.html status (Ssr.render_page opts page)

pub def Ssr.to_response_node (status : U16) (node : Oak.Node Msg) : Response :=
  Response.html status (Html.to_string (Oak.to_html node))

/// A 200 HTML response for a fragment (no doctype/html wrapper).
pub def Ssr.fragment_response (node : Oak.Node Msg) : Response :=
  Ssr.to_response_node 200u16 node

/// A sink that discards writes. `render_io` renders the final `Page` itself,
/// so it neither needs a `Ref` nor retains a rendered string in the
/// interpreter's append-only cell registry.
pub def Ssr.render_io (page_m : HtmlT PageM Open Emitted Unit) : IO (Result String Response) := do {
  let sink : Render PageM :=
    Render.render (fn (_ : String) => PageM.page_m (ResultT.lift (IO.pure Unit.unit)));
  let ran <- ResultT.run (PageM.run (HtmlT.run page_m sink Page.empty));
  match ran {
    Result.err e => return (Result.err e),
    Result.ok pr =>
      match pr {
        Pair.pair page _ =>
          return (Result.ok (Response.html 200u16 (Ssr.render_page Html.default_opts page)))
      }
  }
}
