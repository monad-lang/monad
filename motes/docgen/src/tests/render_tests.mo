/// Renderer tests: the page path, the anchors, the page chrome and the HTML
/// a page body carries -- all pure, so they run without a checkout or a
/// write.
use acorn::config {SiteConfig}
use acorn::site {Built}
use lib::extract {DocExtract.extract_source}
use lib::model {DocItem, DocModule, DocMote}
use lib::render {
    DocRender.anchor_of, DocRender.css_page, DocRender.css_path, DocRender.hub_page,
    kind_class, DocRender.module_page, DocRender.nav_modules, DocRender.page_path,
    DocRender.mote_of_module, module_short, root_for,
}
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

/// Render one module through the page builder and serialize it. The mote's
/// module list is just this page, so its sidebar has one entry.
def RenderPage (md : DocModule) : String :=
    let path : String := md.module in
    match DocRender.module_page cfg (Shared.of [md]) "init" path {
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

// --- The design: stylesheet, kinds, anchors, sidebar ---------------------

/// Every page links the reference stylesheet, and the link is root-relative
/// so `Passes.prefix_root` gives it the page's own depth.
#[test]
def test_page_links_the_stylesheet : Bool :=
    let src : String := "pub def f : I64 := 1\n" in
    let html : String := RenderPage (DocExtract.extract_source "x.mo" src) in
    String.contains html "rel=\"stylesheet\""
        && String.contains html "href=\"../api.css\""

/// A nested page climbs one directory further to the same stylesheet.
#[test]
def test_nested_page_stylesheet_depth : Bool :=
    let md : DocModule := DocExtract.extract_source "std/src/concurrent/channel.mo" "pub def f : I64 := 1\n" in
    let html : String := RenderNested md in
    String.contains html "href=\"../../api.css\""

def RenderNested (md : DocModule) : String :=
    let path : String := md.module in
    match DocRender.module_page cfg (Shared.of [md]) "std" path {
        { doc, .. } => Html.to_string doc,
    }

/// The stylesheet file is part of the build, at the path every page links.
#[test]
def test_css_page_is_written_at_the_linked_path : Bool :=
    match DocRender.css_page {
        { paths, .. } =>
            match paths {
                List.empty => false,
                List.cons p rest => String.beq p DocRender.css_path,
            },
    }

/// The stylesheet is real CSS: the palette the book uses, and the rules the
/// page's own markup depends on.
#[test]
def test_stylesheet_defines_the_site_palette_and_api_rules : Bool :=
    let css : String := StyleCss in
    String.contains css "--bg:"
        && String.contains css "--accent:"
        && String.contains css ".item-kind"
        && String.contains css ".api-sidebar"
        && String.contains css ".item-anchor"

def StyleCss : String :=
    match DocRender.css_page {
        { doc, .. } => Html.to_string doc,
    }

/// A declaration's badge carries `item-kind` plus a per-kind colour class, so
/// the stylesheet can colour it the way the highlighter colours that keyword.
#[test]
def test_kind_classes_colour_the_badge : Bool :=
    String.beq (kind_class "def") "item-kind kind-def"
        && String.beq (kind_class "struct") "item-kind kind-struct"
        && String.beq (kind_class "class") "item-kind kind-class"
        && String.beq (kind_class "instance") "item-kind kind-instance"

/// A kind with no colour rule still gets a badge rather than a class nothing
/// styles.
#[test]
def test_unknown_kind_takes_the_fallback_class : Bool :=
    String.beq (kind_class "widget") "item-kind kind-other"

/// Each declaration has its own deep link, so a signature can be pointed at.
#[test]
def test_item_carries_a_deep_link : Bool :=
    let src : String := "pub def f (x : I64) : I64 := x\n" in
    let html : String := RenderPage (DocExtract.extract_source "x.mo" src) in
    String.contains html "class=\"item-anchor\""
        && String.contains html "href=\"#def.f\""

/// The page opens with the module path and the source file it came from.
#[test]
def test_page_names_its_module_and_source : Bool :=
    let md : DocModule := DocExtract.extract_source "init/src/list.mo" "pub def f : I64 := 1\n" in
    let html : String := RenderPage md in
    String.contains html "class=\"module-head\""
        && String.contains html "init::list"
        && String.contains html "init/src/list.mo"

/// The page carries the module sidebar, and marks its own module `current`.
#[test]
def test_page_sidebar_marks_the_current_module : Bool :=
    let md : DocModule := DocExtract.extract_source "init/src/list.mo" "pub def f : I64 := 1\n" in
    let html : String := RenderPage md in
    String.contains html "class=\"api-sidebar\""
        && String.contains html "class=\"current\""

/// The sidebar lists every module of the mote, not just the current one: the
/// nav is built from the mote's whole module list.
#[test]
def test_sidebar_lists_every_module : Bool :=
    let one : DocModule := DocExtract.extract_source "init/src/list.mo" "pub def a : I64 := 1\n" in
    let two : DocModule := DocExtract.extract_source "init/src/string.mo" "pub def b : I64 := 2\n" in
    let html : String := RenderFirst [one, two] "init::list" in
    String.contains html "init::list"
        && String.contains html "init::string"

def RenderFirst (mods : List DocModule) (module : String) : String :=
    match DocRender.module_page cfg (Shared.of mods) "init" module {
        { doc, .. } => Html.to_string doc,
    }

/// A nav entry's href is the module's page under `api/`, which is what the
/// sidebar's own `root` prefix turns into a working link.
#[test]
def test_nav_entry_href_is_api_relative : Bool :=
    let md : DocModule := DocExtract.extract_source "init/src/list.mo" "pub def a : I64 := 1\n" in
    match DocRender.nav_modules [md] {
        List.empty => false,
        List.cons first rest => String.beq first.href "init/list.html",
    }

/// A module with no declarations of its own says so rather than rendering a
/// blank page: a re-export hub's whole surface is `use` lines.
#[test]
def test_empty_module_says_it_has_no_declarations : Bool :=
    let md : DocModule := DocExtract.extract_source "init/src/lib.mo" "use init::list {}\n" in
    String.contains (RenderPage md) "no-items"

/// A module that does have declarations carries no such note.
#[test]
def test_non_empty_module_has_no_empty_note : Bool :=
    let md : DocModule := DocExtract.extract_source "init/src/list.mo" "pub def a : I64 := 1\n" in
    Bool.not (String.contains (RenderPage md) "no-items")

// --- The hub -------------------------------------------------------------

/// The hub names each mote, counts its modules, and links every one of them
/// under `api/`.
#[test]
def test_hub_lists_every_module_with_a_count : Bool :=
    let one : DocModule := DocExtract.extract_source "init/src/list.mo" "pub def a : I64 := 1\n" in
    let two : DocModule := DocExtract.extract_source "init/src/string.mo" "pub def b : I64 := 2\n" in
    let mote : DocMote := { mote := "init", modules := [one, two] } in
    let html : String := RenderHub [mote] in
    String.contains html "class=\"api-mote\""
        && String.contains html "2 modules"
        && String.contains html "init/list.html"
        && String.contains html "init/string.html"

def RenderHub (motes : List DocMote) : String :=
    match DocRender.hub_page cfg motes {
        { doc, .. } => Html.to_string doc,
    }

/// A mote with one module is counted in the singular.
#[test]
def test_hub_counts_a_single_module_in_the_singular : Bool :=
    let one : DocModule := DocExtract.extract_source "init/src/list.mo" "pub def a : I64 := 1\n" in
    let mote : DocMote := { mote := "init", modules := [one] } in
    String.contains (RenderHub [mote]) "1 module"

/// The hub's own document is styled by the same stylesheet link.
#[test]
def test_hub_links_the_stylesheet : Bool :=
    String.contains (RenderHub List.empty) "href=\"api.css\""

/// A module's mote is its first `::` segment; the hub derives the directory
/// from it.
#[test]
def test_mote_of_module_is_the_first_segment : Bool :=
    String.beq (DocRender.mote_of_module "std::concurrent::channel") "std"
        && String.beq (DocRender.mote_of_module "config") "config"

/// A page shows the module without its mote prefix, so a nested module reads
/// `typecheck::affine` on the `lang` mote rather than repeating the mote.
#[test]
def test_module_short_drops_the_mote_prefix : Bool :=
    String.beq (module_short "lang" "lang::typecheck::affine") "typecheck::affine"
        && String.beq (module_short "init" "init::list") "list"
