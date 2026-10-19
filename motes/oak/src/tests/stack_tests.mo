// The production stack: `HtmlT PageM` writing through
// `Render.lift_page Render.io`, captured with a file-backed sink so a
// test can read the document back.
//
// Two properties are pinned: the success path writes exactly the
// serialized document, and an error lifted before `seal` short-circuits
// `ResultT` so no write ever reaches the sink (the file keeps SENTINEL).
//
// PageM, not `ResultT String IO` directly: passing the latter as a
// `Monad` dictionary through the polymorphic HtmlT ops does not resolve
// (see PageM's declaration in html_t.mo).

use init::transformers {ResultT.run, mk}
use std::io {IO.read_file, IO.write_file}
use std::path {Path, Path.of}
use std::process {process_id}
use lib::elements {Html.card, Html.navbar, Html.text, Html.title}
use lib::html_t {
    Page, Page.empty, Emitted, HtmlT, HtmlT.and_then, HtmlT.body_nodes,
    HtmlT.emit, HtmlT.head_nodes, HtmlT.lift, HtmlT.run, HtmlT.seal,
    Open, PageM, Render, Render.io, Render.lift_page, Render.write, Sealed
}

// ═══ Page programs ═══

def stack_links : List (Pair String String) :=
    [Pair.pair "/" "Home", Pair.pair "/docs" "Docs"]

def stack_open : HtmlT PageM Open Open Unit :=
    let head : HtmlT PageM Open Open Unit :=
        HtmlT.head_nodes [Html.title List.empty [Html.text "Oak"]] in
    let body : HtmlT PageM Open Open Unit :=
        HtmlT.body_nodes [Html.navbar stack_links, Html.card "Hi" "Body"] in
    HtmlT.and_then head body

def stack_page : HtmlT PageM Open Emitted Unit :=
    let open_phase : HtmlT PageM Open Open Unit := stack_open in
    let seal_phase : HtmlT PageM Open Sealed Unit := HtmlT.seal in
    let emit_phase : HtmlT PageM Sealed Emitted Unit := HtmlT.emit in
    HtmlT.and_then open_phase (HtmlT.and_then seal_phase emit_phase)

def stack_failing_open : HtmlT PageM Open Open Unit :=
    let err : PageM Unit :=
        PageM.page_m (ResultT.mk (IO.pure (Result.err "boom"))) in
    HtmlT.lift err

def stack_fail_page : HtmlT PageM Open Emitted Unit :=
    let open_phase : HtmlT PageM Open Open Unit := stack_failing_open in
    let seal_phase : HtmlT PageM Open Sealed Unit := HtmlT.seal in
    let emit_phase : HtmlT PageM Sealed Emitted Unit := HtmlT.emit in
    HtmlT.and_then open_phase (HtmlT.and_then seal_phase emit_phase)

def stack_expected : String :=
    "<!DOCTYPE html><html><head><title>Oak</title></head><body><nav class=\"navbar\"><ul><li><a href=\"/\">Home</a></li><li><a href=\"/docs\">Docs</a></li></ul></nav><div class=\"card\"><h2>Hi</h2><p>Body</p></div></body></html>"

// ═══ A file-backed sink ═══

def render_file (p : Path) : Render IO :=
    Render.render (fn (s : String) => IO.write_file p s)

def stack_path_string (tag : String) : String :=
    String.concat "/tmp/oak_stack_"
        (String.concat tag
            (String.concat "_" (String.concat (I64.to_string process_id) ".html")))

// ═══ Result predicates ═══

def stack_ok (r : Result String (Pair Page Unit)) : Bool :=
    match r { Result.ok _ => true, Result.err _ => false }

def stack_is_boom (r : Result String (Pair Page Unit)) : Bool :=
    match r { Result.ok _ => false, Result.err e => String.beq e "boom" }

// ═══ IO bodies ═══
//
// Each test gets a Path from Path.of, whose only failure is an empty
// string; the fallback keeps the match total without the package-private
// Path.path constructor.

def stack_success_at (p : Path) : IO Bool := do {
    let _ <- IO.write_file p "SENTINEL";
    let sink : Render IO := render_file p;
    let stack_sink : Render PageM := Render.lift_page sink;
    let prog : HtmlT PageM Open Emitted Unit := stack_page;
    let r : Result String (Pair Page Unit) <- ResultT.run (PageM.run (HtmlT.run prog stack_sink Page.empty));
    let out <- IO.read_file p;
    return (stack_ok r && String.beq out stack_expected)
}

def stack_error_at (p : Path) : IO Bool := do {
    let _ <- IO.write_file p "SENTINEL";
    let sink : Render IO := render_file p;
    let stack_sink : Render PageM := Render.lift_page sink;
    let prog : HtmlT PageM Open Emitted Unit := stack_fail_page;
    let r : Result String (Pair Page Unit) <- ResultT.run (PageM.run (HtmlT.run prog stack_sink Page.empty));
    let out <- IO.read_file p;
    return (stack_is_boom r && String.beq out "SENTINEL")
}

// ═══ Tests ═══

#[test]
def test_stack_success_writes_document : IO Bool :=
    match Path.of (stack_path_string "success") {
        Result.ok p => stack_success_at p,
        Result.err _ => IO.pure false
    }

#[test]
def test_stack_error_short_circuits : IO Bool :=
    match Path.of (stack_path_string "error") {
        Result.ok p => stack_error_at p,
        Result.err _ => IO.pure false
    }

#[test]
def test_render_io_smoke : IO Bool := do {
    let _ <- Render.write Render.io "";
    return true
}
