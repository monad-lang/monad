/// The monad-lang.org site: its chrome around every book page, and the
/// landing page at the output root.
///
/// acorn renders the book; this mote is what makes the result *this* site.
/// The chrome is data (a `Shell`), and the landing page is an extra page, so
/// acorn itself stays a generic generator.
use xml_html::html {Html.Node}
use oak::typed {Oak.Node, Oak.to_html}
use oak::elements {
    Html.a, Html.class_, Html.footer, Html.header, Html.href, Html.link, Html.nav, Html.rel,
    Html.text,
}
use acorn::config {SiteConfig}
use acorn::layout {Shell}
use acorn::site {Built, Site.build_with}
use lib::landing {Landing.page}

/// `<head>` additions for a book page, in order: the favicon, then the book
/// stylesheet. Both are root-relative; acorn prefixes the page's depth.
pub def Website.head : List Html.Node :=
    [Oak.to_html (Html.link [Html.rel "icon", Html.href "favicon.svg"]),
        Oak.to_html (Html.link [Html.rel "stylesheet", Html.href "acorn.css"])]

/// The site header: the brand, then Docs and Try.
pub def Website.header (cfg : SiteConfig) : List Html.Node :=
    [Oak.to_html
        (Html.header [Html.class_ ["site-header"]]
            [Html.a [Html.class_ ["brand"], Html.href "index.html"] [Html.text cfg.title],
                Html.nav [Html.class_ ["site-nav"]]
                    [Html.a [Html.href (String.concat cfg.book_dir "/introduction.html")] [Html.text "Docs"],
                        Html.a [Html.href "try/"] [Html.text "Try"]]])]

pub def Website.footer : List Html.Node :=
    [Oak.to_html (Html.footer [Html.class_ ["site-footer"]] [Html.text "Built with acorn."])]

pub def Website.shell (cfg : SiteConfig) : Shell :=
    { head := Website.head, header := Website.header cfg, footer := Website.footer }

/// The pages that are not part of the book: the landing page, at the output
/// root (and therefore also the site's `/index.html`).
pub def Website.pages (cfg : SiteConfig) : List Built :=
    [Built.page "index.html" (Oak.to_html (Landing.page cfg))]

/// Render monad-lang.org.
pub def Website.build (cfg : SiteConfig) : IO (Result String I64) :=
    Site.build_with cfg (Shared.of (Website.shell cfg)) (Website.pages cfg)
