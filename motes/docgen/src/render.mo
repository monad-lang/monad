/// Rendering: the page model to acorn `Built` pages.
///
/// One page per module under `api/<mote>/<module>.html`, plus a hub at
/// `api/index.html` listing every mote's modules. The pages are built here
/// and handed to `Site.write_pages`, so they pass the same broken-link and
/// duplicate-path gate the book's own pages do: a doc page that links to a
/// module with no page is a build error, not a 404.
///
/// ANCHORS are `<kind>.<name>` -- `def.List.map`, `struct.Point` -- the
/// source's own spelling, so a link is predictable and reads like the `use`
/// line that reaches the declaration.
///
/// A declaration's doc comment is markdown, rendered with the book's own
/// site options so a doc page's prose looks like a chapter's.

use acorn::config {SiteConfig}
use acorn::layout {PageSpec, Shell, Layout.document_with}
use acorn::site {Built}
use markdown::html {Markdown.to_html_nodes_with}
use markdown::parse {Markdown.parse_with}
use markdown::types {Markdown.Document}
use markdown::options {Markdown.HtmlOptions, Markdown.default_html_options, Markdown.site_options}
use xml_html::html {Html.Attr, Html.Node}
use lib::model {DocItem, DocModule, DocMote}

/// How a doc comment's markdown is rendered: the book's site options, with
/// heading ids on so a `## Sections` comment gets anchors. Raw HTML stays
/// off -- a doc comment is prose, not markup.
def doc_html_options : Markdown.HtmlOptions :=
    { Markdown.default_html_options with heading_ids := true }

/// One item's anchor id: `<kind>.<name>`, the source's own spelling.
pub def DocRender.anchor_of (i : DocItem) : String :=
    String.concat i.kind (String.concat "." i.name)

/// The page path one module writes to: `api/<mote>/<module>.html`. The
/// module path's own mote prefix is dropped -- the directory already names
/// the mote -- and its `::` becomes `/`, so `init::string` is
/// `api/init/string.html` and `lang::typecheck::affine` is
/// `api/lang/typecheck/affine.html`: the shape a reader's `use` line has.
pub def DocRender.page_path (mote : String) (module : String) : String :=
    String.concat "api/"
        (String.concat mote
            (String.concat "/" (String.concat (slash_module (drop_mote_prefix mote module)) ".html")))

/// `init::string` with the `init::` mote prefix removed -> `string`. A module
/// that does not start with the mote's name (the tests' synthetic ones) comes
/// back unchanged.
def drop_mote_prefix (mote : String) (module : String) : String :=
    let prefix : String := String.concat mote "::" in
    if String.starts_with prefix module
    then String.drop (String.length prefix) module
    else module

/// `string::inner` -> `string/inner`; a bare `string` stays `string`.
def slash_module (module : String) : String :=
    let shared : Shared String := Shared.of module in
    slash_chars (String.to_list (Shared.get shared)) List.empty

def is_colon (c : U8) : Bool := U8.beq c (58u8)

#[partial]
def slash_chars (cs : List U8) (acc : List U8) : String :=
    match cs {
        List.empty => String.from_list (List.reverse acc),
        List.cons c rest =>
            if is_colon c then slash_chars (drop_colon rest) (List.cons (47u8) acc)
            else slash_chars rest (List.cons c acc),
    }

/// A `::` is two colons: consume the second one too, so `a::b` becomes
/// `a/b` and not `a//b`.
#[partial]
def drop_colon (cs : List U8) : List U8 :=
    match cs {
        List.empty => List.empty,
        List.cons c rest => if is_colon c then rest else List.cons c rest,
    }

/// The whole mote's pages, in module order, each ready to write.
pub def DocRender.mote_pages (cfg : SiteConfig) (m : DocMote) : List Built :=
    match m {
        { mote, modules, .. } => List.map (fn (md : DocModule) => DocRender.module_page cfg mote md) modules,
    }

/// One module's page. The page's `root` is computed from its own path's
/// depth: `api/std/list.html` climbs one level to `api/`, and
/// `api/std/concurrent/channel.html` climbs two, so the shell's `index.html`
/// brand reaches the hub from either.
pub def DocRender.module_page (cfg : SiteConfig) (mote : String) (md : DocModule) : Built :=
    match md {
        { module, doc, items, .. } =>
            let path : String := DocRender.page_path mote module in
            Built.page path
                (Layout.document_with cfg (Shared.of doc_shell)
                    (module_spec path module doc items)),
    }

/// The `api/index.html` hub: every mote with a link to each of its modules.
pub def DocRender.hub_page (cfg : SiteConfig) (motes : List DocMote) : Built :=
    let spec : PageSpec := { title := "API reference", root := "", body := hub_body motes, book := Option.none } in
    Built.page "api/index.html" (Layout.document_with cfg (Shared.of doc_shell) spec)

/// The chrome an API page wears. The brand's `index.html` is resolved
/// against the page's own `root`, which `root_for` computes per depth: the
/// hub (`api/index.html`) has `root := ""` and links itself, a flat module
/// page climbs one level to `api/`, a nested one two.
///
/// The book's `Shell.default` points its brand at `docs/index.html`, which
/// an API-only build does not write; the link gate refuses that, correctly,
/// so the chrome is docgen's own.
def doc_shell : Shell :=
    { head := List.empty,
        header := [element "header" [attr "class" "site-header"]
            [element "a" [attr "class" "brand", attr "href" "index.html"]
                [text "Monad API reference"]]],
        footer := [element "footer" [attr "class" "site-footer"]
            [text "Generated by docgen."]] }

// --- Page bodies ---------------------------------------------------------

/// The module page's `PageSpec`: the module doc at the top, then one
/// section per item.
def module_spec (path : String) (title : String) (doc : Option String) (items : List DocItem) : PageSpec :=
    { title := title, root := root_for path, book := Option.none,
        body := List.append (module_doc_nodes doc) (item_sections items) }

/// The path from a page at `api/<...>/<name>.html` back to `api/`. The file
/// name is not a directory, so the count is the number of `/` the path has
/// minus one -- `api/std/list.html` is one, `api/std/concurrent/x.html` two.
pub def root_for (path : String) : String :=
    root_prefix (I64.sub (count_slashes path) 1) ""

#[partial]
def count_slashes (path : String) : I64 :=
    count_slashes_go (String.to_list path) 0

#[partial]
def count_slashes_go (cs : List U8) (n : I64) : I64 :=
    match cs {
        List.empty => n,
        List.cons c rest =>
            if U8.beq c (47u8) then count_slashes_go rest (I64.add n 1) else count_slashes_go rest n,
    }

#[partial]
def root_prefix (n : I64) (acc : String) : String :=
    if I64.lt n 1 then acc else root_prefix (I64.sub n 1) (String.concat acc "../")

/// The module's own leading doc comment, rendered as markdown.
def module_doc_nodes (doc : Option String) : List Html.Node :=
    match doc {
        Option.none => List.empty,
        Option.some text =>
            [element "div" [attr "class" "module-doc"] (markdown_nodes text)],
    }

/// One `<section>` per item, in source order.
#[partial]
def item_sections (items : List DocItem) : List Html.Node :=
    match items {
        List.empty => List.empty,
        List.cons i rest => List.cons (item_section i) (item_sections rest),
    }

/// One item: an anchored heading, its signature as a Monad code block, then
/// its doc comment as markdown.
def item_section (i : DocItem) : Html.Node :=
    let id : String := DocRender.anchor_of i in
    element "section" [attr "class" "item", attr "id" id]
        (List.append
            [element "h3" [attr "class" "item-name"]
                [element "span" [attr "class" "item-kind"] [text (String.concat i.kind " ")],
                    element "code" List.empty [text i.name]]]
            (List.append
                [code_block i.signature]
                (doc_nodes i.doc)))

/// An item's doc comment as markdown nodes; nothing when it has none.
def doc_nodes (doc : Option String) : List Html.Node :=
    match doc {
        Option.none => List.empty,
        Option.some text => [element "div" [attr "class" "item-doc"] (markdown_nodes text)],
    }

/// A markdown string rendered to HTML nodes with the book's own options.
def markdown_nodes (text : String) : List Html.Node :=
    let doc : Shared Markdown.Document := Shared.of (Markdown.parse_with Markdown.site_options text) in
    Markdown.to_html_nodes_with doc_html_options (Shared.get doc)

/// A signature as a highlighted Monad code block. `language-monad` is the
/// class the book's own fences carry, so the page needs no extra CSS.
def code_block (signature : String) : Html.Node :=
    element "pre" [attr "class" "language-monad"]
        [element "code" List.empty [text signature]]

/// The hub body: one `<section>` per mote, one link per module.
def hub_body (motes : List DocMote) : List Html.Node :=
    let shared : Shared (List DocMote) := Shared.of motes in
    match Shared.get shared {
        List.empty => [element "p" List.empty [text "No motes to document."]],
        List.cons _ rest => hub_sections (Shared.get shared),
    }

/// One section per mote. The empty case is handled by `hub_body`, which is
/// where the "no motes" message belongs; reaching here means at least one.
#[partial]
def hub_sections (motes : List DocMote) : List Html.Node :=
    match motes {
        List.empty => List.empty,
        List.cons m rest => List.cons (hub_section m) (hub_sections rest),
    }

def hub_section (m : DocMote) : Html.Node :=
    match m {
        { mote, modules, .. } =>
            element "section" [attr "class" "api-mote"]
                [element "h2" List.empty [text mote], module_links mote modules],
    }

#[partial]
def module_links (mote : String) (mods : List DocModule) : Html.Node :=
    element "ul" [attr "class" "api-modules"] (module_link_items mote mods)

#[partial]
def module_link_items (mote : String) (mods : List DocModule) : List Html.Node :=
    match mods {
        List.empty => List.empty,
        List.cons md rest =>
            List.cons (module_link_item mote md) (module_link_items mote rest),
    }

def module_link_item (mote : String) (md : DocModule) : Html.Node :=
    match md {
        { module, .. } =>
            element "li" List.empty
                [element "a" [attr "href" (hub_module_href mote module)] [text module]],
    }

/// The hub's link to one module page. The hub is `api/index.html`, so the
/// href is the page path minus its leading `api/`: `acorn/config.html`, or
/// `std/concurrent/channel.html` for a nested module.
def hub_module_href (mote : String) (module : String) : String :=
    String.drop 4 (DocRender.page_path mote module)

// --- Small HTML constructors --------------------------------------------

/// An element with children.
def element (tag : String) (attrs : List Html.Attr) (children : List Html.Node) : Html.Node :=
    Html.Node.node_element tag attrs children

/// A `name="value"` attribute.
def attr (name : String) (value : String) : Html.Attr :=
    Html.Attr.attr name value

/// A text node.
def text (content : String) : Html.Node :=
    Html.Node.node_text content
