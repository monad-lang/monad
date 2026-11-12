/// Renderer tests: the page path, the anchors, and the HTML a page bodies
/// carries -- all pure, so they run without a checkout or a write.
use acorn::config {SiteConfig}
use acorn::site {Built}
use lib::extract {DocExtract.extract_source}
use lib::model {DocItem, DocModule}
use lib::render {DocRender.anchor_of, DocRender.module_page, DocRender.page_path, root_for}
use xml_html::html {Html.to_string}

def cfg : SiteConfig :=
    { title := "Monad language", base_url := "/", book_src := "docs/src",
        book_dir := "docs", out_dir := "out" }

/// A page path turns a module path into directories, and always ends in
/// `.html`: `init::string` is `api/init/string.html`.
#[test]
def test_page_path_is_mote_then_module : Bool :=
    String.beq (DocRender.page_path "init" "init::string") "api/init/string.html"

/// A flat module name stays at the mote's own level.
#[test]
def test_page_path_flat_module : Bool :=
    String.beq (DocRender.page_path "acorn" "config") "api/acorn/config.html"

/// A nested module gets one directory per segment.
#[test]
def test_page_path_nested_module : Bool :=
    String.beq (DocRender.page_path "lang" "lang::typecheck::affine")
        "api/lang/typecheck/affine.html"

/// An anchor is the source's own `<kind>.<name>` spelling.
#[test]
def test_anchor_is_kind_dot_name : Bool :=
    let src : String := "pub def List.map (f : A -> B) : List B := f\n" in
    match DocExtract.extract_source "x.mo" src {
        { items, .. } =>
            match items {
                List.empty => false,
                List.cons i rest => String.beq (DocRender.anchor_of i) "def.List.map",
            },
    }

/// The rendered page carries its path, the item's anchor, its signature and
/// its doc prose.
#[test]
def test_module_page_carries_items : Bool :=
    let src : String := "/// Get at an index.\npub def List.get (index : I64) : Option A := 1\n" in
    let html : String := RenderPage (DocExtract.extract_source "init/src/list.mo" src) in
    String.contains html "id=\"def.List.get\""
        && String.contains html "pub def List.get (index : I64) : Option A"
        && String.contains html "Get at an index."
        && String.contains html "language-monad"

/// Render one module through the page builder and serialize it. Split out of
/// the test body: the `Built` match and the serialize are two steps, and the
/// arm-with-several-statements shape wants its own def on some paths.
def RenderPage (md : DocModule) : String :=
    match DocRender.module_page cfg "init" md {
        { doc, .. } => Html.to_string doc,
    }

/// A def's body is not in its signature: the page shows the header only.
#[test]
def test_signature_has_no_body : Bool :=
    let src : String := "pub def f (x : I64) : I64 := x + 41\n" in
    let html : String := RenderPage (DocExtract.extract_source "x.mo" src) in
    String.contains html "pub def f (x : I64) : I64"
        && Bool.not (String.contains html "x + 41")

/// An item with no doc comment renders without a doc div.
#[test]
def test_undocumented_item_has_no_doc_div : Bool :=
    let src : String := "pub def bare : I64 := 1\n" in
    let html : String := RenderPage (DocExtract.extract_source "x.mo" src) in
    Bool.not (String.contains html "class=\"item-doc\"")

/// A page's root climbs to `api/`, one level per directory between it and
/// the file: a flat module page climbs one, a nested one climbs two. The hub
/// reaches the shell's `index.html` brand from either.
#[test]
def test_root_matches_page_depth : Bool :=
    String.beq (root_for "api/std/list.html") "../"
        && String.beq (root_for "api/std/concurrent/channel.html") "../../"

/// A nested module page is written one directory per module segment, and its
/// path carries the nesting the hub's link needs.
#[test]
def test_nested_module_page_path : Bool :=
    String.beq (DocRender.page_path "std" "std::concurrent::channel")
        "api/std/concurrent/channel.html"
