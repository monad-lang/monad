/// Link rewriting and admonitions over rendered chapters.
use std::list {List.intercalate}
use lib::passes {FenceInfo, Passes.fence_info, Passes.rewrite_href}
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

def info_text (i : FenceInfo) : String :=
    match i {
        { lang, flags } => String.concat lang (String.concat "|" (List.intercalate "," flags)),
    }

#[test]
def test_fence_info_splits_flags : Bool :=
    String.beq (info_text (Passes.fence_info "monad,ignore")) "monad|ignore"
        && String.beq (info_text (Passes.fence_info "monad")) "monad|"
        && String.beq (info_text (Passes.fence_info "monad,check,run")) "monad|check,run"

#[test]
def test_monad_fence_is_highlighted_and_flagged : Bool :=
    let html : String := render "```monad,ignore\ndef x : I64 := 1\n```\n" in
    String.contains html "<pre class=\"ignore\"><code class=\"language-monad\"><span class=\"kw\">def</span> <span class=\"fn\">x</span>"
        && String.contains html "<span class=\"num\">1</span>"

#[test]
def test_other_fences_are_left_plain : Bool :=
    let html : String := render "```bash\nmonad run x.mo\n```\n" in
    String.contains html "<pre><code class=\"language-bash\">monad run x.mo"

#[test]
def test_section_headings_get_self_links : Bool :=
    let html : String := render "# Title\n\n## Basic Syntax\n\n#### Deep\n" in
    String.contains html "<h2 id=\"basic-syntax\">Basic Syntax<a class=\"anchor\" href=\"#basic-syntax\" aria-hidden=\"true\">#</a></h2>"
        && String.contains html "<a class=\"anchor\" href=\"#deep\""
        && Bool.not (String.contains html "href=\"#title\"")
