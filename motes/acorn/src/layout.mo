/// The page shell every acorn page renders through.
///
/// Pages are Oak views at `Msg = Unit`: a static page binds no handlers, and
/// `Oak.to_html` drops none. Content that is already markup (a rendered
/// markdown chapter) embeds with `Oak.of_html`.
///
/// The chrome around the content (head links, header, footer) is the site's,
/// supplied as data in a `Shell`; `Shell.default` is acorn's own plain chrome.
use oak::typed {Oak.Node, Oak.of_html, Oak.to_html}
use xml_html::html {Html.Node, Html.to_string}
use oak::elements {
    Html.a, Html.attr, Html.charset, Html.class_, Html.div, Html.document_with, Html.footer,
    Html.header, Html.href, Html.lang, Html.li, Html.link, Html.main_, Html.meta, Html.nav,
    Html.ol, Html.rel, Html.span, Html.text, Html.title, Html.aside, Html.p,
}
use lib::config {SiteConfig}
use lib::passes {Passes.prefix_root}
use lib::summary {NavEntry, NavChapter}
use lib::toc {TocEntry}

/// The site chrome around a book page. Relative `href`/`src` values are
/// prefixed with the page's `root` at render time (`Passes.prefix_root`), so
/// one shell works at every depth; absolute URLs, site-absolute paths and
/// fragments are left alone.
pub struct Shell {
    /// Emitted after `charset`, `viewport` and the page's `<title>`.
    head : List Html.Node,
    /// Replaces acorn's built-in header.
    header : List Html.Node,
    /// Replaces acorn's built-in footer.
    footer : List Html.Node,
}

def default_head (cfg : SiteConfig) : List Html.Node :=
    if String.is_empty cfg.assets_dir
    then List.empty
    else [Oak.to_html (Html.link [Html.rel "stylesheet", Html.href "acorn.css"])]

/// The brand links to the book's own `index.html`, which acorn always
/// writes. Nothing else: a site's navigation (its first chapter's name, its
/// `/try`, its source host) belongs to the site, which supplies its own
/// `Shell` through `Site.build_with`.
def default_header (cfg : SiteConfig) : List Html.Node :=
    [Oak.to_html
        (Html.header [Html.class_ ["site-header"]]
            [Html.a [Html.class_ ["brand"], Html.href (String.concat cfg.book_dir "/index.html")]
                [Html.text cfg.title]])]

def default_footer : List Html.Node :=
    [Oak.to_html (Html.footer [Html.class_ ["site-footer"]] [Html.text "Built with acorn."])]

/// acorn's own chrome: the stylesheet when the site has an `assets` tree, a
/// brand and a `Docs` link, and a one-line footer.
pub def Shell.default (cfg : SiteConfig) : Shell :=
    { head := default_head cfg, header := default_header cfg, footer := default_footer }

/// A book page's place in the book: the sidebar entries, the current
/// chapter's stem, and its neighbours in reading order.
pub struct BookNav {
    /// Shared by every page of the book.
    entries : Shared (List NavEntry),
    current : String,
    prev : Option NavChapter,
    next : Option NavChapter,
}

/// What one page contributes to the shell.
pub struct PageSpec {
    /// The page's own title; the site title is appended.
    title : String,
    /// The path from this page back to the output root (`""` at the root,
    /// `"../"` one level down), so every link works from `file://` and from
    /// any base URL.
    root : String,
    /// The page body, already rendered.
    body : List Html.Node,
    /// The on-page table of contents (`aside.toc`); empty renders none.
    toc : List TocEntry := List.empty,
    /// The book navigation, for a book chapter; none for other pages.
    book : Option BookNav,
}

/// One shell list, prefixed for this page's depth and ready to embed.
def shell_nodes (root : String) (shell : Shared Shell) (pick : Shell -> List Html.Node) : List (Oak.Node Unit) :=
    List.map Oak.of_html (Passes.prefix_root root (pick (Shared.get shell)))

def shell_head (s : Shell) : List Html.Node :=
    match s { { head, .. } => head }

def shell_header (s : Shell) : List Html.Node :=
    match s { { header, .. } => header }

def shell_footer (s : Shell) : List Html.Node :=
    match s { { footer, .. } => footer }

def head_nodes (cfg : SiteConfig) (title : String) (root : String) (shell : Shared Shell) : List (Oak.Node Unit) :=
    List.append
        [Html.meta [Html.charset "utf-8"],
            Html.meta [Html.attr "name" "viewport", Html.attr "content" "width=device-width, initial-scale=1"],
            Html.title List.empty [Html.text (String.concat title (String.concat " - " cfg.title))]]
        (shell_nodes root shell shell_head)

/// The link to a chapter page, from a page `root` away from the output root.
pub def Layout.chapter_href (cfg : SiteConfig) (root : String) (stem : String) : String :=
    String.concat root (String.concat cfg.book_dir (String.concat "/" (String.concat stem ".html")))

def depth_class (depth : I64) : String :=
    String.concat "depth-" (I64.to_string depth)

def sidebar_item (cfg : SiteConfig) (root : String) (current : String) (e : NavEntry) : Oak.Node Unit :=
    match e {
        NavEntry.part title => Html.li [Html.class_ ["part-title"]] [Html.text title],
        NavEntry.chapter title stem depth =>
            let classes : List String :=
                if String.beq stem current
                then ["chapter", depth_class depth, "active"]
                else ["chapter", depth_class depth] in
            Html.li [Html.class_ classes]
                [Html.a [Html.href (Layout.chapter_href cfg root stem)] [Html.text title]],
    }

def sidebar (cfg : SiteConfig) (root : String) (entries : Shared (List NavEntry)) (current : String) : Oak.Node Unit :=
    Html.nav [Html.class_ ["sidebar"]]
        [Html.ol [Html.class_ ["chapters"]] (List.map (sidebar_item cfg root current) (Shared.get entries))]

def pager_link (cfg : SiteConfig) (root : String) (cls : String) (label : String) (c : Option NavChapter) : List (Oak.Node Unit) :=
    match c {
        Option.none => List.empty,
        Option.some chapter => [pager_anchor cfg root cls label chapter],
    }

def pager_anchor (cfg : SiteConfig) (root : String) (cls : String) (label : String) (c : NavChapter) : Oak.Node Unit :=
    match c {
        { title, stem } =>
            Html.a [Html.class_ [cls], Html.href (Layout.chapter_href cfg root stem)]
                [Html.span [Html.class_ ["pager-label"]] [Html.text label], Html.text title],
    }

def pager (cfg : SiteConfig) (root : String) (prev : Option NavChapter) (next : Option NavChapter) : Oak.Node Unit :=
    Html.nav [Html.class_ ["pager"]]
        (List.append (pager_link cfg root "prev" "Previous" prev) (pager_link cfg root "next" "Next" next))

def toc_item (e : TocEntry) : Oak.Node Unit :=
    match e {
        { level, id, text } =>
            Html.li [Html.class_ [String.concat "toc-h" (I64.to_string level)]]
                [Html.a [Html.href (String.concat "#" id)] [Html.text text]],
    }

/// The on-page TOC; nothing when the page has fewer than two sections.
def toc_aside (toc : List TocEntry) : List (Oak.Node Unit) :=
    match toc {
        List.empty => List.empty,
        List.cons first rest => toc_after first rest,
    }

def toc_after (first : TocEntry) (rest : List TocEntry) : List (Oak.Node Unit) :=
    match rest {
        List.empty => List.empty,
        List.cons second more =>
            [Html.aside [Html.class_ ["toc"]]
                [Html.p [Html.class_ ["toc-title"]] [Html.text "On this page"],
                    Html.ol List.empty (List.map toc_item (List.cons first (List.cons second more)))]],
    }

/// The page body: content alone, or the sidebar beside content, pager and
/// the on-page TOC.
def body_nodes (cfg : SiteConfig) (root : String) (content : List (Oak.Node Unit)) (toc : List TocEntry) (book : Option BookNav) : List (Oak.Node Unit) :=
    match book {
        Option.none => [Html.main_ [Html.class_ ["content"]] content],
        Option.some nav => [book_body cfg root content toc nav],
    }

def book_body (cfg : SiteConfig) (root : String) (content : List (Oak.Node Unit)) (toc : List TocEntry) (nav : BookNav) : Oak.Node Unit :=
    match nav {
        { entries, current, prev, next } =>
            Html.div [Html.class_ ["book"]]
                (List.cons (sidebar cfg root entries current)
                    (List.cons (Html.main_ [Html.class_ ["content"]] (List.append content [pager cfg root prev next]))
                        (toc_aside toc))),
    }

/// The whole document for one page, in the site's chrome.
pub def Layout.page_with (cfg : SiteConfig) (shell : Shared Shell) (page : PageSpec) : Oak.Node Unit :=
    match page {
        { title, root, body, toc, book } =>
            let content : List (Oak.Node Unit) := List.map Oak.of_html body in
            Html.document_with [Html.lang "en"] List.empty List.empty
                (head_nodes cfg title root shell)
                (List.append (shell_nodes root shell shell_header)
                    (List.append (body_nodes cfg root content toc book) (shell_nodes root shell shell_footer))),
    }

/// The whole document in acorn's own `Shell.default` chrome.
pub def Layout.page (cfg : SiteConfig) (page : PageSpec) : Oak.Node Unit :=
    Layout.page_with cfg (Shared.of (Shell.default cfg)) page

/// The page as one `Html.Node` document (what the link gate reads).
pub def Layout.document_with (cfg : SiteConfig) (shell : Shared Shell) (page : PageSpec) : Html.Node :=
    Oak.to_html (Layout.page_with cfg shell page)

pub def Layout.document (cfg : SiteConfig) (page : PageSpec) : Html.Node :=
    Oak.to_html (Layout.page cfg page)

/// The page serialized to HTML text.
pub def Layout.render_with (cfg : SiteConfig) (shell : Shared Shell) (page : PageSpec) : String :=
    Html.to_string (Layout.document_with cfg shell page)

pub def Layout.render (cfg : SiteConfig) (page : PageSpec) : String :=
    Html.to_string (Layout.document cfg page)
