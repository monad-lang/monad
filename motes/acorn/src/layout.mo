/// The page shell every acorn page renders through.
///
/// Pages are Oak views at `Msg = Unit`: a static page binds no handlers, and
/// `Oak.to_html` drops none. Content that is already markup (a rendered
/// markdown chapter) embeds with `Oak.of_html`.
use oak::typed {Oak.Node, Oak.of_html, Oak.to_html}
use xml_html::html {Html.Node, Html.to_string}
use oak::elements {
    Html.a, Html.attr, Html.charset, Html.class_, Html.document_with, Html.footer,
    Html.header, Html.href, Html.lang, Html.link, Html.main_, Html.meta, Html.nav,
    Html.rel, Html.text, Html.title,
}
use lib::config {SiteConfig}

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
}

def head_nodes (cfg : SiteConfig) (title : String) (root : String) : List (Oak.Node Unit) :=
    [Html.meta [Html.charset "utf-8"],
        Html.meta [Html.attr "name" "viewport", Html.attr "content" "width=device-width, initial-scale=1"],
        Html.title List.empty [Html.text (String.concat title (String.concat " - " cfg.title))],
        Html.link [Html.rel "icon", Html.href (String.concat root "favicon.svg")],
        Html.link [Html.rel "stylesheet", Html.href (String.concat root "acorn.css")]]

def site_header (cfg : SiteConfig) (root : String) : Oak.Node Unit :=
    Html.header [Html.class_ ["site-header"]]
        [Html.a [Html.class_ ["brand"], Html.href (String.concat root "index.html")]
            [Html.text cfg.title],
            Html.nav [Html.class_ ["site-nav"]]
                [Html.a [Html.href (String.concat root (String.concat cfg.book_dir "/introduction.html"))]
                    [Html.text "Docs"],
                    Html.a [Html.href (String.concat root "try/")] [Html.text "Try"]]]

def site_footer : Oak.Node Unit :=
    Html.footer [Html.class_ ["site-footer"]] [Html.text "Built with acorn."]

/// The whole document for one page.
pub def Layout.page (cfg : SiteConfig) (page : PageSpec) : Oak.Node Unit :=
    match page {
        { title, root, body } =>
            let content : List (Oak.Node Unit) := List.map Oak.of_html body in
            Html.document_with [Html.lang "en"] List.empty List.empty
                (head_nodes cfg title root)
                [site_header cfg root,
                    Html.main_ [Html.class_ ["content"]] content,
                    site_footer],
    }

/// The page serialized to HTML text.
pub def Layout.render (cfg : SiteConfig) (page : PageSpec) : String :=
    Html.to_string (Oak.to_html (Layout.page cfg page))
