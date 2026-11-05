/// Chapter rendering through the page shell.
use lib::config {SiteConfig}
use lib::site {Site.chapter_stem, Site.render_chapter}

def cfg : SiteConfig :=
    { title := "Monad language", base_url := "/", book_src := "docs/src",
        book_dir := "docs", out_dir := "out" }

#[test]
def test_chapter_stem : Bool :=
    match Site.chapter_stem "modules.md" {
        Option.some s => String.beq s "modules",
        Option.none => false,
    }

#[test]
def test_summary_is_not_a_chapter : Bool :=
    match Site.chapter_stem "SUMMARY.md" {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_non_markdown_is_skipped : Bool :=
    match Site.chapter_stem "images" {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_render_has_title_and_heading_id : Bool :=
    let html : String := Site.render_chapter cfg "intro" "# Hello World\n\nText.\n" in
    String.contains html "<title>Hello World - Monad language</title>"
        && String.contains html "id=\"hello-world\""
        && String.contains html "<!DOCTYPE html>"

#[test]
def test_render_falls_back_to_stem : Bool :=
    let html : String := Site.render_chapter cfg "intro" "No heading.\n" in
    String.contains html "<title>intro - Monad language</title>"
