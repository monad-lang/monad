/// Link rewriting and admonitions over rendered chapters.
use lib::passes {Passes.rewrite_href}
use lib::site {Site.render_chapter}
use lib::config {SiteConfig}

def cfg : SiteConfig :=
    { title := "Monad language", base_url := "/", book_src := "docs/src",
        book_dir := "docs", out_dir := "out" }

#[test]
def test_md_link_becomes_html : Bool :=
    String.beq (Passes.rewrite_href "./modules.md") "./modules.html"

#[test]
def test_md_link_keeps_fragment : Bool :=
    String.beq (Passes.rewrite_href "./modules.md#how-modules-are-found") "./modules.html#how-modules-are-found"

#[test]
def test_absolute_and_other_links_unchanged : Bool :=
    String.beq (Passes.rewrite_href "https://example.com/a.md") "https://example.com/a.md"
        && String.beq (Passes.rewrite_href "#section") "#section"
        && String.beq (Passes.rewrite_href "../try/") "../try/"

def render (src : String) : String :=
    Site.render_chapter cfg Option.none "page" src

#[test]
def test_rendered_link_is_rewritten : Bool :=
    String.contains (render "See [modules](./modules.md).\n") "href=\"./modules.html\""

#[test]
def test_warning_admonition : Bool :=
    let html : String := render "> [!WARNING]\n> **Careful.** Body text.\n" in
    String.contains html "<div class=\"admonition warning\"><p class=\"admonition-title\">Warning</p>"
        && String.contains html "<strong>Careful.</strong>"
        && Bool.not (String.contains html "[!WARNING]")
        && Bool.not (String.contains html "<blockquote>")

#[test]
def test_marker_with_text_on_same_line : Bool :=
    let html : String := render "> [!NOTE] Read this.\n" in
    String.contains html "<p class=\"admonition-title\">Note</p><p>Read this.</p>"

#[test]
def test_plain_and_unknown_quotes_stay_blockquotes : Bool :=
    String.contains (render "> Just a quote.\n") "<blockquote>"
        && String.contains (render "> [!SHOUT] no.\n") "[!SHOUT]"
