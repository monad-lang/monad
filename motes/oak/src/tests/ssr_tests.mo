/// SSR adapter tests: response construction and the `PageM` capture sink.
///
/// The `PageM` case now compiles and passes on both backends; it is part of
/// the self-hosted gate as well as the Rust-host run.

use http::body {Body.to_bytes_pure}
use http::types {Headers.get, Response, Status.ok}
use lib::elements {Html.p, Html.text, Html.title}
use lib::html_t {
  Emitted, HtmlT, HtmlT.and_then, HtmlT.body_node, HtmlT.emit, HtmlT.head_node,
  HtmlT.seal, Open, Page, Page.append_body, Page.append_head, Page.empty,
  PageM, Sealed,
}
use lib::ssr {Ssr.render_body, Ssr.render_io, Ssr.render_page, Ssr.to_response}
use xml_html::html {Html.default_opts, Html.RenderOpts}

def test_page : Page :=
  let with_head := Page.append_head Page.empty (Html.title List.empty [Html.text "T"]) in
  let with_body := Page.append_body with_head (Html.p List.empty [Html.text "B"]) in
  with_body

def page_program : HtmlT PageM Open Emitted Unit :=
  let open_phase : HtmlT PageM Open Open Unit := do {
    let _ <- HtmlT.head_node (Html.title List.empty [Html.text "T"]);
    let _ <- HtmlT.body_node (Html.p List.empty [Html.text "B"]);
    return Unit.unit
  } in
  let seal_phase : HtmlT PageM Open Sealed Unit := HtmlT.seal in
  let emit_phase : HtmlT PageM Sealed Emitted Unit := HtmlT.emit in
  HtmlT.and_then open_phase (HtmlT.and_then seal_phase emit_phase)

def body_text (res : Response) : String :=
  String.from_list (Body.to_bytes_pure res.body)

#[test]
def test_to_response_content_type : Bool :=
  let res := Ssr.to_response 200u16 Html.default_opts test_page in
  let ct := match Headers.get "Content-Type" res.headers {
    Option.some v => v,
    Option.none => ""
  } in
  Bool.and (U16.beq res.status Status.ok)
    (Bool.and (String.beq ct "text/html; charset=utf-8")
      (String.beq (body_text res) (Ssr.render_page Html.default_opts test_page)))

#[test]
def test_render_body_fragment : Bool :=
  String.beq (Ssr.render_body (Html.p List.empty [Html.text "B"])) "<p>B</p>"

#[test]
def test_render_io_captures_document : IO Bool := do {
  let r <- Ssr.render_io page_program;
  match r {
    Result.err _ => return false,
    Result.ok res =>
      return (String.beq (body_text res)
        "<!DOCTYPE html><html><head><title>T</title></head><body><p>B</p></body></html>")
  }
}

#[test]
def test_render_page_charset : Bool :=
  let base := Html.default_opts in
  let opts : Html.RenderOpts := { base with charset := true } in
  String.beq (Ssr.render_page opts test_page)
    "<!DOCTYPE html><html><head><meta charset=\"utf-8\"><title>T</title></head><body><p>B</p></body></html>"
