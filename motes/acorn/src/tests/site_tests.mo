/// Chapter rendering through the page shell.
use lib::config {SiteConfig}
use lib::site {Site.render_chapter}
use lib::layout {BookNav}
use lib::summary {NavEntry, NavChapter}

def cfg : SiteConfig :=
    { title := "Monad language", base_url := "/", book_src := "docs/src",
        book_dir := "docs", out_dir := "out" }

#[test]
def test_render_has_title_and_heading_id : Bool :=
    let html : String := Site.render_chapter cfg Option.none "intro" "# Hello World\n\nText.\n" in
    String.contains html "<title>Hello World - Monad language</title>"
        && String.contains html "id=\"hello-world\""
        && String.contains html "<!DOCTYPE html>"

#[test]
def test_render_falls_back_to_stem : Bool :=
    let html : String := Site.render_chapter cfg Option.none "intro" "No heading.\n" in
    String.contains html "<title>intro - Monad language</title>"

def intro : NavChapter := { title := "Intro", stem := "intro" }

def nav : BookNav :=
    { entries := Shared.of [NavEntry.chapter "Intro" "intro" 0, NavEntry.part "Tutorial", NavEntry.chapter "Types" "types" 0],
        current := "types", prev := Option.some intro, next := Option.none }

#[test]
def test_render_marks_current_and_links_prev : Bool :=
    let html : String := Site.render_chapter cfg (Option.some nav) "types" "# Types\n" in
    String.contains html "class=\"chapter depth-0 active\"><a href=\"../docs/types.html\">Types</a>"
        && String.contains html "<li class=\"part-title\">Tutorial</li>"
        && String.contains html "class=\"prev\" href=\"../docs/intro.html\""
        && Bool.not (String.contains html "class=\"next\"")

def toc_src : String :=
    "# Types\n\n## First `code` part\n\nText.\n\n### Detail\n\n#### Too deep\n\n## Second\n"

#[test]
def test_book_page_has_on_page_toc : Bool :=
    let html : String := Site.render_chapter cfg (Option.some nav) "types" toc_src in
    String.contains html "<aside class=\"toc\"><p class=\"toc-title\">On this page</p><ol>"
        && String.contains html "<li class=\"toc-h2\"><a href=\"#first-code-part\">First code part</a></li>"
        && String.contains html "<li class=\"toc-h3\"><a href=\"#detail\">Detail</a></li>"
        && String.contains html "<li class=\"toc-h2\"><a href=\"#second\">Second</a></li>"
        && Bool.not (String.contains html "href=\"#too-deep\">Too deep")

#[test]
def test_single_section_page_has_no_toc : Bool :=
    let html : String := Site.render_chapter cfg (Option.some nav) "types" "# Types\n\n## Only\n" in
    Bool.not (String.contains html "class=\"toc\"")
