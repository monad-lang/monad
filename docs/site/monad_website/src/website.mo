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
use docgen::extract {DocExtract.extract_mote}
use docgen::model {DocMote, DocMote.public_only}
use docgen::render {DocRender.hub_page, DocRender.mote_pages}
use lib::landing {Landing.page}

/// `<head>` additions for a book page, in order: the favicon, then the book
/// stylesheet. Both are root-relative; acorn prefixes the page's depth.
pub def Website.head : List Html.Node :=
    [Oak.to_html (Html.link [Html.rel "icon", Html.href "favicon.svg"]),
        Oak.to_html (Html.link [Html.rel "stylesheet", Html.href "acorn.css"])]

/// The site header: the brand, then Docs, API and Try.
pub def Website.header (cfg : SiteConfig) : List Html.Node :=
    [Oak.to_html
        (Html.header [Html.class_ ["site-header"]]
            [Html.a [Html.class_ ["brand"], Html.href "index.html"] [Html.text cfg.title],
                Html.nav [Html.class_ ["site-nav"]]
                    [Html.a [Html.href (String.concat cfg.book_dir "/introduction.html")] [Html.text "Docs"],
                        Html.a [Html.href "api/index.html"] [Html.text "API"],
                        Html.a [Html.href "try/"] [Html.text "Try"]]])]

pub def Website.footer : List Html.Node :=
    [Oak.to_html (Html.footer [Html.class_ ["site-footer"]] [Html.text "Built with acorn."])]

pub def Website.shell (cfg : SiteConfig) : Shell :=
    { head := Website.head, header := Website.header cfg, footer := Website.footer }

/// The pages that are not part of the book: the landing page at the output
/// root, then the API reference under `api/`. The API pages come from
/// docgen, which reads the motes' own sources -- so a declaration's page is
/// its doc comment, and the site and the reference cannot disagree about a
/// signature.
pub def Website.pages (cfg : SiteConfig) : IO (List Built) := do {
    let api <- Website.api_pages cfg;
    return (List.append [Built.page "index.html" (Oak.to_html (Landing.page cfg))] api)
}

/// The motes whose API the site publishes. The list is the site's, not
/// docgen's: which packages a reader is pointed at is an editorial choice.
def documented_motes : List String := ["init", "std", "lang", "cli", "eval"]

/// Every documented mote's pages, then the hub. The published reference
/// shows `pub` declarations only -- package-private internals are the mote's
/// own business, and the site is for readers. A mote that fails to read is
/// skipped rather than failing the site: a missing reference page is better
/// than no site at all, and the build reports the count either way.
def Website.api_pages (cfg : SiteConfig) : IO (List Built) := do {
    let motes <- extract_motes documented_motes List.empty;
    let shared : Shared (List DocMote) := Shared.of motes;
    return (List.append (all_mote_pages cfg (Shared.get shared))
        [DocRender.hub_page cfg (Shared.get shared)])
}

#[terminating]
def extract_motes (dirs : List String) (acc : List DocMote) : IO (List DocMote) :=
    match dirs {
        List.empty => return (List.reverse acc),
        List.cons d rest => extract_one d rest acc,
    }

#[terminating]
def extract_one (dir : String) (rest : List String) (acc : List DocMote) : IO (List DocMote) := do {
    let got <- DocExtract.extract_mote dir;
    match got {
        Result.err _ => extract_motes rest acc,
        Result.ok m => extract_motes rest (List.cons (DocMote.public_only m) acc),
    }
}

def all_mote_pages (cfg : SiteConfig) (motes : List DocMote) : List Built :=
    match motes {
        List.empty => List.empty,
        List.cons m rest => List.append (DocRender.mote_pages cfg m) (all_mote_pages cfg rest),
    }

/// Render monad-lang.org.
pub def Website.build (cfg : SiteConfig) : IO (Result String I64) := do {
    let extras <- Website.pages cfg;
    Site.build_with cfg (Shared.of (Website.shell cfg)) extras
}
