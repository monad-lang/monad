/// Rendering: the page model to acorn `Built` pages.
///
/// Each mote is its own small site under a docs BASE (`motes/docs/` on
/// monad-lang.org, the output root for `monad doc`):
///
/// | Path under the base          | Page                                    |
/// |------------------------------|-----------------------------------------|
/// | `index.html`                 | the hub: one card per mote              |
/// | `docgen.css`                 | the stylesheet every page links         |
/// | `<mote>/index.html`          | the mote's home: its doc and modules    |
/// | `<mote>/<module/path>.html`  | one module's declarations               |
///
/// Every path and every href docgen produces is relative to the base; the
/// base itself is prepended only where a `Built` is made (`at_base`). A
/// page's `root` is the climb from its own base-relative path back to the
/// base (`root_for`), so the stylesheet, the hub and every sibling page are
/// reached through one coordinate system and cannot disagree about where
/// the base is.
///
/// The pages are handed to `Site.write_pages`, so they pass the same
/// broken-link and duplicate-path gate the book's own pages do: a doc page
/// that links to a module with no page is a build error, not a 404.
///
/// ANCHORS are `<kind>.<name>` -- `def.List.map`, `struct.Point` -- the
/// source's own spelling, so a link is predictable and reads like the `use`
/// line that reaches the declaration.
///
/// A declaration's doc comment is markdown, rendered with the book's own
/// site options so a doc page's prose looks like a chapter's.
///
/// The chrome is the site's rather than acorn's own: the API reference is a
/// published part of monad-lang.org, so it wears the same palette and the
/// same stylesheet shape. `lib::style` holds the stylesheet itself; this
/// module links it (`doc_shell`) and emits it (`css_page`).

use acorn::config {SiteConfig}
use acorn::layout {PageSpec, Shell, Layout.document_with}
use acorn::site {Built}
use markdown::html {Markdown.to_html_nodes_with}
use markdown::parse {Markdown.parse_with}
use markdown::types {Markdown.Document}
use markdown::options {Markdown.HtmlOptions, Markdown.default_html_options, Markdown.site_options}
use xml_html::html {Html.Attr, Html.Node}
use lib::model {DocItem, DocModule, DocMote}
use lib::style {Style.api_css}

/// The stylesheet's path, relative to the docs base. A page links it
/// through its own `root`; `css_page` writes it here.
pub def DocRender.css_path : String := "docgen.css"

/// A base-relative path as the path a `Built` is written to.
def at_base (base : String) (rel : String) : String :=
    String.concat base rel

/// How a doc comment's markdown is rendered: the book's site options, with
/// heading ids on so a `## Sections` comment gets anchors. Raw HTML stays
/// off -- a doc comment is prose, not markup.
def doc_html_options : Markdown.HtmlOptions :=
    { Markdown.default_html_options with heading_ids := true }

/// One item's anchor id: `<kind>.<name>`, the source's own spelling.
pub def DocRender.anchor_of (i : DocItem) : String :=
    String.concat i.kind (String.concat "." i.name)

/// The base-relative page path one module writes to:
/// `<mote>/<module>.html`. The module path's own mote prefix is dropped --
/// the directory already names the mote -- and its `::` becomes `/`, so
/// `init::string` is `init/string.html` and `lang::typecheck::affine` is
/// `lang/typecheck/affine.html`: the shape a reader's `use` line has.
pub def DocRender.page_path (mote : String) (module : String) : String :=
    String.concat mote
        (String.concat "/" (String.concat (slash_module (drop_mote_prefix mote module)) ".html"))

/// The base-relative path of a mote's home page: `<mote>/index.html`.
pub def DocRender.mote_home_path (mote : String) : String :=
    String.concat mote "/index.html"

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

// --- A mote's module list, as the sidebar needs it ------------------------

/// One module page's nav entry: the module's own path, and the href to its
/// page relative to the docs base (a page prefixes its own `root`).
pub struct NavModule {
    module : String,
    href : String,
}

/// Both fields are `String` (immutable pointers), so duplicating an entry
/// shares pointers: the sidebar reads one entry's `module` and `href`
/// separately, and without this each read would need its own `Shared` dance.
pub instance Copy NavModule {
    def copy (e : NavModule) : Pair NavModule NavModule := Pair.pair e e
}

/// Every module of a mote as a sidebar entry, in the mote's own order.
#[partial]
pub def DocRender.nav_modules (mods : List DocModule) : List NavModule :=
    match mods {
        List.empty => List.empty,
        List.cons md rest =>
            let module : String := md.module in
            let one : NavModule :=
                { module := module, href := DocRender.page_path (DocRender.mote_of_module module) module } in
            List.cons one (DocRender.nav_modules rest),
    }

/// The mote a module's path names: its first `::` segment, which is also the
/// directory `page_path` puts it in. A path with no `::` names itself.
pub def DocRender.mote_of_module (module : String) : String :=
    match String.byte_index_of module "::" {
        Option.some at => String.slice module 0 at,
        Option.none => module,
    }

// --- Pages ---------------------------------------------------------------

/// The whole mote's module pages, in module order, each ready to write.
pub def DocRender.mote_pages (cfg : SiteConfig) (base : String) (m : DocMote) : List Built :=
    match m {
        { mote, modules, .. } =>
            let shared : Shared (List DocModule) := Shared.of modules in
            DocRender.pages_for_modules cfg base mote shared,
    }

/// The module pages for a mote whose module list the caller already holds
/// as a handle. A `Shared` handle is `Copy`, so `mote_site` can hand the
/// SAME one to this and to the home page; storing `Shared.get` of it into a
/// rebuilt record instead is `borrowed_value_escapes`.
def DocRender.pages_for_modules
    (cfg : SiteConfig) (base : String) (mote : String) (shared : Shared (List DocModule)) : List Built :=
    List.map (fn (md : DocModule) => DocRender.module_page cfg base shared mote md.module) (Shared.get shared)

/// One module's page, given the mote's whole module list so its sidebar can
/// link every sibling. Its `root` climbs from its base-relative path:
/// `std/list.html` climbs one level, `std/concurrent/channel.html` two.
pub def DocRender.module_page (cfg : SiteConfig) (base : String) (mods : Shared (List DocModule)) (mote : String) (module : String) : Built :=
    let rel : String := DocRender.page_path mote module in
    let root : String := root_for rel in
    match find_module (Shared.get mods) module {
        Option.none => Built.page (at_base base rel) (empty_page cfg mote root module),
        Option.some md =>
            match md {
                { file, doc, items, .. } =>
                    let nav : Shared (List NavModule) := Shared.of (DocRender.nav_modules (Shared.get mods)) in
                    Built.page (at_base base rel)
                        (Layout.document_with cfg (Shared.of (doc_shell (Option.some mote)))
                            (with_sidebar nav mote module root (module_spec root module file doc items))),
            },
    }

/// A mote's whole site: its module pages, then its home page.
pub def DocRender.mote_site (cfg : SiteConfig) (base : String) (m : DocMote) : List Built :=
    match m {
        { mote, modules, .. } =>
            let shared : Shared (List DocModule) := Shared.of modules in
            List.append (DocRender.pages_for_modules cfg base mote shared)
                [DocRender.home_page_for_modules cfg base mote shared],
    }

/// The module a path names, from a mote's own list.
#[partial]
def find_module (mods : List DocModule) (module : String) : Option DocModule :=
    match mods {
        List.empty => Option.none,
        List.cons md rest =>
            if String.beq md.module module then Option.some md else find_module rest module,
    }

/// A page for a module the mote's list does not hold. It cannot happen from
/// `mote_pages` (which walks the list itself), but `module_page` is public
/// and a caller may name a module from elsewhere; an empty page keeps the
/// file it asked for rather than crashing or silently writing nothing.
def empty_page (cfg : SiteConfig) (mote : String) (root : String) (module : String) : Html.Node :=
    Layout.document_with cfg (Shared.of (doc_shell (Option.some mote)))
        { title := module, root := root, book := Option.none,
            body := [element "h1" List.empty [text module]] }

/// A page's `PageSpec` with the mote's module sidebar wrapped around its
/// body: the sidebar is `nav.api-sidebar`, the body the readable column
/// beside it (`div.api-main`), in the grid `lib::style` styles.
def with_sidebar (nav : Shared (List NavModule)) (mote : String) (module : String) (root : String) (spec : PageSpec) : PageSpec :=
    match spec {
        { title, body, toc, book, .. } =>
            { title := title, root := root, toc := toc, book := book,
                body := [sidebar nav mote module root body] },
    }

/// The module sidebar beside the page body: the mote's name (linking the
/// mote's home) over one link per module, with this page's own module
/// marked `current`.
def sidebar (nav : Shared (List NavModule)) (mote : String) (module : String) (root : String) (body : List Html.Node) : Html.Node :=
    element "div" [attr "class" "api"]
        [element "nav" [attr "class" "api-sidebar"]
            [element "p" [attr "class" "mote-name"]
                [element "a" [attr "href" (String.concat root (DocRender.mote_home_path mote))] [text mote]],
                element "p" [attr "class" "nav-label"] [text "Modules"],
                element "ol" List.empty (sidebar_items (Shared.get nav) mote module root)],
            element "div" [attr "class" "api-main"] body]

/// A module's path without its mote prefix -- what a mote's own pages show:
/// `lang::typecheck::affine` on the `lang` mote is `typecheck::affine`.
pub def module_short (mote : String) (module : String) : String :=
    drop_mote_prefix mote module

#[partial]
def sidebar_items (entries : List NavModule) (mote : String) (module : String) (root : String) : List Html.Node :=
    match entries {
        List.empty => List.empty,
        List.cons e rest =>
            List.cons (sidebar_item e mote module root) (sidebar_items rest mote module root),
    }

/// One sidebar link: the entry's base-relative href under the page's own
/// `root`, labelled without the mote prefix (the site already names the
/// mote), with the page's own module marked `current` -- the book sidebar's
/// `active` chapter. An unmarked entry carries no class at all rather than
/// one no stylesheet matches.
def sidebar_item (e : NavModule) (mote : String) (module : String) (root : String) : Html.Node :=
    let attrs : List Html.Attr :=
        if String.beq e.module module then [attr "class" "current"] else List.empty in
    element "li" attrs
        [element "a" [attr "href" (String.concat root e.href)] [text (module_short mote e.module)]]

/// A mote's home page, `<mote>/index.html`: the mote's name, its `lib`
/// module's doc comment when it has one (that is the mote's own overview),
/// and a link to every module. This is what makes each mote its own site:
/// the module pages' brand and sidebar title both lead here.
pub def DocRender.mote_home_page (cfg : SiteConfig) (base : String) (m : DocMote) : Built :=
    match m {
        { mote, modules, .. } =>
            let shared : Shared (List DocModule) := Shared.of modules in
            DocRender.home_page_for_modules cfg base mote shared,
    }

/// The home page for a mote whose module list the caller already holds as
/// a handle (see `pages_for_modules`).
def DocRender.home_page_for_modules
    (cfg : SiteConfig) (base : String) (mote : String) (shared : Shared (List DocModule)) : Built :=
    let rel : String := DocRender.mote_home_path mote in
    let root : String := root_for rel in
    let spec : PageSpec :=
        { title := mote, root := root, book := Option.none,
            body := [element "div" [attr "class" "hub"]
                (List.append
                    [element "h1" List.empty [text mote],
                        element "p" [attr "class" "mote-meta"] [text (module_count_text (Shared.get shared))]]
                    (List.append
                        (module_doc_nodes (lib_doc mote (Shared.get shared)))
                        [module_links root mote (Shared.get shared)]))] } in
    Built.page (at_base base rel) (Layout.document_with cfg (Shared.of (doc_shell (Option.some mote))) spec)

/// The doc comment of a mote's `lib` module, its overview by convention.
def lib_doc (mote : String) (mods : List DocModule) : Option String :=
    match find_module mods (String.concat mote "::lib") {
        Option.none => Option.none,
        Option.some md => md.doc,
    }

/// The `index.html` hub at the docs base: every mote, each card titled with
/// a link to the mote's own site.
pub def DocRender.hub_page (cfg : SiteConfig) (base : String) (motes : List DocMote) : Built :=
    let spec : PageSpec := { title := "Mote docs", root := "", body := hub_body motes, book := Option.none } in
    Built.page (at_base base "index.html") (Layout.document_with cfg (Shared.of (doc_shell Option.none)) spec)

/// The stylesheet as a file to write. `Site.write_pages` writes `Built`
/// pages only, and a stylesheet is not one, so it is a `Built` at the
/// `css_path` path whose document is one raw node: the serializer emits the
/// literal verbatim, and the link gate ignores a raw node. Written beside
/// the pages it styles, which is what makes `monad doc` self-sufficient.
pub def DocRender.css_page (base : String) : Built :=
    Built.page (at_base base DocRender.css_path) (Html.Node.node_raw_html Style.api_css)

/// The chrome a docs page wears. Every href is base-relative, so one shell
/// works at every depth: `Passes.prefix_root` prefixes them with the page's
/// `root`, and the stylesheet is always written (`css_page`).
///
/// On a mote's own pages (`Option.some mote`) the brand is the mote, leading
/// to its home, with a way back to every mote; the hub's brand is the hub.
/// The book's `Shell.default` points its brand at `docs/index.html`, which a
/// docs-only build does not write; the link gate refuses that, correctly, so
/// the chrome is docgen's own -- shaped like the site's (`Website.header`).
def doc_shell (mote : Option String) : Shell :=
    { head := [Html.Node.node_void "link" [attr "rel" "stylesheet", attr "href" DocRender.css_path]],
        header := [element "header" [attr "class" "site-header"] (header_links mote)],
        footer := [element "footer" [attr "class" "site-footer"]
            [text "Generated by docgen."]] }

def header_links (mote : Option String) : List Html.Node :=
    match mote {
        Option.none =>
            [element "a" [attr "class" "brand", attr "href" "index.html"] [text "Monad mote docs"]],
        Option.some m =>
            let name : String := m in
            [element "a" [attr "class" "brand", attr "href" (DocRender.mote_home_path name)] [text name],
                element "nav" [attr "class" "site-nav"]
                    [element "a" [attr "href" "index.html"] [text "All motes"]]],
    }

// --- Page bodies ---------------------------------------------------------

/// The module page's `PageSpec`: the module's own heading and doc at the
/// top, then one section per declaration.
def module_spec (root : String) (module : String) (file : String) (doc : Option String) (items : List DocItem) : PageSpec :=
    { title := module, root := root, book := Option.none,
        body := List.append
            (List.append (module_head module file) (module_doc_nodes doc))
            (item_sections items) }

/// The page's own heading: the module path, over the source file it came
/// from -- so a reader arriving from a search result knows which module this
/// is and where it lives before reading any declaration.
def module_head (module : String) (file : String) : List Html.Node :=
    [element "div" [attr "class" "module-head"]
        [element "h1" List.empty [text module],
            element "p" [attr "class" "module-source"] [text file]]]

/// The climb from a page's base-relative path back to the docs base: one
/// `../` per directory in it -- `index.html` is none, `std/list.html` one,
/// `std/concurrent/channel.html` two.
pub def root_for (rel : String) : String :=
    root_prefix (count_slashes rel) ""

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

/// One `<section>` per declaration, in source order. A module with none --
/// a re-export hub whose whole surface is `use` lines, or one documented
/// with `--include-private` off -- says so: a blank page reads as a broken
/// one, and the module doc above it is still worth showing.
///
/// The empty case is decided HERE, once, and `item_list` only ever maps a
/// non-empty list. A two-arm recursion over the items emitted the note after
/// the items on every page (measured against the real site build): the
/// `List.empty` arm of a `#[partial]` list recursion is not reached only at
/// the end of the list, so the termination of the list is not the note's.
def item_sections (items : List DocItem) : List Html.Node :=
    match items {
        List.empty => [no_items_note],
        List.cons i rest => item_list (List.cons i rest),
    }

/// The note a module page carries when it has no declarations to list.
def no_items_note : Html.Node :=
    Html.Node.node_element "p" [Html.Attr.attr "class" "no-items"]
        [Html.Node.node_text "This module has no public declarations of its own."]

/// Every item's section, for a list already known to be non-empty.
def item_list (items : List DocItem) : List Html.Node :=
    List.map item_section items

/// One declaration: its head (kind badge, name, deep link), its signature as
/// a Monad code block, then its doc comment as markdown. The head is a
/// `div.item-head` so the badge, name and anchor lay out on one line and the
/// stylesheet can hang the badge and the hover anchor off it.
def item_section (i : DocItem) : Html.Node :=
    let id : String := DocRender.anchor_of i in
    element "section" [attr "class" "item", attr "id" id]
        (List.append
            [element "div" [attr "class" "item-head"]
                [element "span" [attr "class" (kind_class i.kind)] [text i.kind],
                    element "code" [attr "class" "item-name"] [text i.name],
                    element "a" [attr "class" "item-anchor", attr "href" (String.concat "#" id)] [text "#"]]]
            (List.append
                [code_block i.signature]
                (doc_nodes i.doc)))

/// The badge's classes for one declaration kind: `item-kind` plus the
/// per-kind colour rule. `def` blue, `type`/`struct` orange, `class` purple,
/// `instance` green -- the assignment the highlighter gives a keyword of that
/// kind, so a page reads as one palette. A kind with no rule still gets a
/// badge (`kind-other`), never a class no stylesheet matches.
pub def kind_class (kind : String) : String :=
    String.concat "item-kind " (String.concat "kind-" (known_kind kind))

def known_kind (kind : String) : String :=
    if String.beq kind "def" then "def"
    else if String.beq kind "struct" then "struct"
    else if String.beq kind "type" then "type"
    else if String.beq kind "class" then "class"
    else if String.beq kind "instance" then "instance"
    else if String.beq kind "infix" then "infix"
    else if String.beq kind "use" then "use"
    else "other"

/// A declaration's doc comment as markdown nodes; nothing when it has none.
def doc_nodes (doc : Option String) : List Html.Node :=
    match doc {
        Option.none => List.empty,
        Option.some text => [element "div" [attr "class" "item-doc"] (markdown_nodes text)],
    }

/// A markdown string rendered to HTML nodes with the book's own options.
def markdown_nodes (text : String) : List Html.Node :=
    let doc : Shared Markdown.Document := Shared.of (Markdown.parse_with Markdown.site_options text) in
    Markdown.to_html_nodes_with doc_html_options (Shared.get doc)

/// A signature as a Monad code block. `language-monad` is the class the
/// book's own fences carry, so the page needs no extra rule for it.
def code_block (signature : String) : Html.Node :=
    element "pre" [attr "class" "language-monad"]
        [element "code" List.empty [text signature]]

// --- The hub -------------------------------------------------------------

/// The hub body: a heading, then one card per mote.
def hub_body (motes : List DocMote) : List Html.Node :=
    let shared : Shared (List DocMote) := Shared.of motes in
    match Shared.get shared {
        List.empty => [element "p" List.empty [text "No motes to document."]],
        List.cons _ rest =>
            [element "div" [attr "class" "hub"]
                (List.append [hub_heading] (hub_sections (Shared.get shared)))],
    }

/// The hub's heading, so the page names itself before the list of motes.
def hub_heading : Html.Node :=
    element "h1" List.empty [text "Mote docs"]

/// One card per mote. The empty case is handled by `hub_body`, which is
/// where the "no motes" message belongs; reaching here means at least one.
#[partial]
def hub_sections (motes : List DocMote) : List Html.Node :=
    match motes {
        List.empty => List.empty,
        List.cons m rest => List.cons (hub_section m) (hub_sections rest),
    }

/// One mote's card: its name (linking the mote's own site), how many
/// modules it documents, and the module links as a compact grid -- a flat
/// list is unreadable for a mote the size of `lang`.
def hub_section (m : DocMote) : Html.Node :=
    match m {
        { mote, modules, .. } =>
            let shared : Shared (List DocModule) := Shared.of modules in
            element "section" [attr "class" "api-mote"]
                [element "h2" List.empty
                    [element "a" [attr "href" (DocRender.mote_home_path mote)] [text mote]],
                    element "p" [attr "class" "mote-meta"] [text (module_count_text (Shared.get shared))],
                    module_links "" mote (Shared.get shared)],
    }

/// "17 modules", singular when there is one.
def module_count_text (mods : List DocModule) : String :=
    let n : I64 := List.length mods in
    if I64.beq n 1 then "1 module" else String.concat (I64.to_string n) " modules"

/// A mote's modules as a link grid, from a page whose climb to the base is
/// `root`. The labels drop the mote prefix: the card or page already names
/// the mote.
def module_links (root : String) (mote : String) (mods : List DocModule) : Html.Node :=
    element "ul" [attr "class" "api-modules"]
        (List.map (fn (md : DocModule) => module_link_item root mote md) mods)

def module_link_item (root : String) (mote : String) (md : DocModule) : Html.Node :=
    match md {
        { module, .. } =>
            element "li" List.empty
                [element "a" [attr "href" (String.concat root (DocRender.page_path mote module))]
                    [text (module_short mote module)]],
    }

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
