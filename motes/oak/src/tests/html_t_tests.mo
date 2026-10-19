// HtmlT tests over a write-logging mock monad, adapted from
// motes/tui/src/tests/tuit_tests.mo.
//
// The point of the suite is state threading: unlike TuiT (stateless), a
// `map` or `and_then` that forgets to pass the updated `Page` drops nodes.
// The two regression tests below would pass on a stateless implementation
// and fail on a broken stateful one.

use std::list {List.length}
use lib::elements {Html.document, Html.text, Html.title}
use lib::html_t {
    Page, Page.empty, Emitted, HtmlT, HtmlT.and_then, HtmlT.body_node,
    HtmlT.body_nodes, HtmlT.emit, HtmlT.head_node, HtmlT.lift, HtmlT.map,
    HtmlT.run, HtmlT.seal, Open, Render, Sealed
}
use xml_html::html {Html.to_string}

// ═══ A write-logging base monad ═══

type RenderM A {
    render_m (log : List String) (a : A)
}

def render_pure {A : Type} (a : A) : RenderM A :=
    RenderM.render_m List.empty a

def render_bind_run {A : Type} {B : Type} (f : A -> RenderM B) (log : List String) (a : A) : RenderM B :=
    match f a {
        RenderM.render_m log2 b => RenderM.render_m (List.append log log2) b
    }

instance Monad RenderM {
    def pure (a : A) : RenderM A := render_pure a
    def bind (ma : RenderM A) (f : A -> RenderM B) : RenderM B :=
        match ma { render_m log a => render_bind_run f log a }
}

def render_log {A : Type} (m : RenderM A) : List String :=
    match m { RenderM.render_m log _ => log }

def mock_write (s : String) : RenderM Unit :=
    RenderM.render_m (List.cons s List.empty) Unit.unit

def mock_render : Render RenderM := Render.render mock_write

// ═══ Reading the state back ═══

def pair_doc {A : Type} (p : Pair Page A) : Page :=
    match p { Pair.pair d _ => d }

def mock_doc {A : Type} (m : RenderM (Pair Page A)) : Page :=
    match m { RenderM.render_m _ p => pair_doc p }

def doc_string (d : Page) : String :=
    Html.to_string (Html.document d.head d.body)

def html_t_strs_eq (a : List String) (b : List String) : Bool :=
    match a {
        empty => List.length b == 0,
        cons x xs => match b {
            empty => false,
            cons y ys => x == y && html_t_strs_eq xs ys
        }
    }

// ═══ Programs ═══

def prog_head_body : HtmlT RenderM Open Open Unit :=
    let a : HtmlT RenderM Open Open Unit :=
        HtmlT.head_node (Html.title List.empty [Html.text "T"]) in
    let b : HtmlT RenderM Open Open Unit :=
        HtmlT.body_nodes [Html.text "a", Html.text "b"] in
    HtmlT.and_then a b

def prog_do_open : HtmlT RenderM Open Open Unit := do {
    let _ <- HtmlT.head_node (Html.text "h");
    let _ <- HtmlT.body_node (Html.text "b");
    return Unit.unit
}

def prog_lift : HtmlT RenderM Open Open Unit :=
    let before : HtmlT RenderM Open Open Unit := HtmlT.lift (mock_write "before") in
    let head : HtmlT RenderM Open Open Unit := HtmlT.head_node (Html.text "h") in
    HtmlT.and_then before head

def prog_map_thread : HtmlT RenderM Open Open Unit :=
    let first : HtmlT RenderM Open Open Unit :=
        HtmlT.map (fn (u : Unit) => u) (HtmlT.body_node (Html.text "a")) in
    let second : HtmlT RenderM Open Open Unit := HtmlT.body_node (Html.text "b") in
    HtmlT.and_then first second

def prog_and_then_thread : HtmlT RenderM Open Open Unit :=
    let first : HtmlT RenderM Open Open Unit :=
        HtmlT.body_nodes [Html.text "a", Html.text "b"] in
    let second : HtmlT RenderM Open Open Unit := HtmlT.body_node (Html.text "c") in
    HtmlT.and_then first second

def prog_indexed_map : HtmlT RenderM Open Open Unit :=
    let first : HtmlT RenderM Open Open Unit :=
        IndexedMonad.map (fn (u : Unit) => u) (HtmlT.body_node (Html.text "a")) in
    let second : HtmlT RenderM Open Open Unit := HtmlT.body_node (Html.text "b") in
    HtmlT.and_then first second

def prog_emit : HtmlT RenderM Open Emitted Unit :=
    let open_phase : HtmlT RenderM Open Open Unit := prog_head_body in
    let seal_phase : HtmlT RenderM Open Sealed Unit := HtmlT.seal in
    let emit_phase : HtmlT RenderM Sealed Emitted Unit := HtmlT.emit in
    HtmlT.and_then open_phase (HtmlT.and_then seal_phase emit_phase)

def run_prog {A : Type} (prog : HtmlT RenderM Open A Unit) : RenderM (Pair Page Unit) :=
    HtmlT.run prog mock_render Page.empty

// ═══ Tests ═══

#[test]
def test_pure_empty_doc : Bool :=
    let prog : HtmlT RenderM Open Open Unit := HtmlT.pure Unit.unit in
    let m : RenderM (Pair Page Unit) := HtmlT.run prog mock_render Page.empty in
    let d : Page := mock_doc m in
    String.beq (doc_string d) "<!DOCTYPE html><html><head></head><body></body></html>"
    && html_t_strs_eq (render_log m) List.empty

#[test]
def test_head_and_body : Bool :=
    let d : Page := mock_doc (run_prog prog_head_body) in
    String.beq (doc_string d)
        "<!DOCTYPE html><html><head><title>T</title></head><body>ab</body></html>"

#[test]
def test_do_notation_open_open : Bool :=
    let d : Page := mock_doc (run_prog prog_do_open) in
    String.beq (doc_string d)
        "<!DOCTYPE html><html><head>h</head><body>b</body></html>"

#[test]
def test_lift_interleaves : Bool :=
    let m : RenderM (Pair Page Unit) := run_prog prog_lift in
    let d : Page := mock_doc m in
    String.beq (doc_string d)
        "<!DOCTYPE html><html><head>h</head><body></body></html>"
    && html_t_strs_eq (render_log m) ["before"]

#[test]
def test_map_threads_doc : Bool :=
    let d : Page := mock_doc (run_prog prog_map_thread) in
    String.beq (doc_string d)
        "<!DOCTYPE html><html><head></head><body>ab</body></html>"

#[test]
def test_and_then_threads_doc : Bool :=
    let d : Page := mock_doc (run_prog prog_and_then_thread) in
    String.beq (doc_string d)
        "<!DOCTYPE html><html><head></head><body>abc</body></html>"

#[test]
def test_indexed_map_threads_doc : Bool :=
    let d : Page := mock_doc (run_prog prog_indexed_map) in
    String.beq (doc_string d)
        "<!DOCTYPE html><html><head></head><body>ab</body></html>"

#[test]
def test_emit_writes_document : Bool :=
    let m : RenderM (Pair Page Unit) := run_prog prog_emit in
    html_t_strs_eq (render_log m)
        ["<!DOCTYPE html><html><head><title>T</title></head><body>ab</body></html>"]
