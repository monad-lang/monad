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
    { entries := [NavEntry.chapter "Intro" "intro" 0, NavEntry.part "Tutorial", NavEntry.chapter "Types" "types" 0],
        current := "types", prev := Option.some intro, next := Option.none }

#[test]
def test_render_marks_current_and_links_prev : Bool :=
    let html : String := Site.render_chapter cfg (Option.some nav) "types" "# Types\n" in
    String.contains html "class=\"chapter depth-0 active\"><a href=\"../docs/types.html\">Types</a>"
        && String.contains html "<li class=\"part-title\">Tutorial</li>"
        && String.contains html "class=\"prev\" href=\"../docs/intro.html\""
        && Bool.not (String.contains html "class=\"next\"")
