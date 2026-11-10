/// Chapter rendering through the page shell.
use lib::config {SiteConfig}
use lib::site {Site.render_chapter, read_text}
use lib::layout {BookNav}
use lib::summary {NavEntry, NavChapter}
use std::process {exec_cmd}
use std::path {Path, Path.of}
use xml_html::html {Html.Node, Html.Attr}

/// Read a file under the test's output root, flattening the two error
/// shapes (a bad path and a missing file) into the one this test means:
/// "nothing was written".
def read_out (path : String) : IO (Result String String) :=
    read_text path

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

// --- Site.write_pages: the gate and writer without the book -------------
//
// The same checks the book's own pages go through, on a caller's own pages:
// one page writes; a duplicate path is refused before anything is written;
// a broken internal link is refused with the link named.

use lib::site {Built, Site.write_pages}

/// A one-link page, the way a caller (the API generator, a landing page)
/// builds one.
def link_page (path : String) (href : String) : Built :=
    Built.page path (Html.Node.node_element "a" [Html.Attr.attr "href" href] [Html.Node.node_text "x"])

#[test]
def test_write_pages_writes_one_page : IO Bool := do {
    let out : String := "/tmp/acorn-write-pages-ok";
    let _ <- exec_cmd "rm" ["-rf", out];
    let wrote <- Site.write_pages out [link_page "api/index.html" "./list.html", link_page "api/list.html" "./index.html"];
    wrote_then_read wrote out
}

/// The write succeeded; the page must exist with the link, and the count
/// must be the number of files written (two pages, one path each). Split
/// out of the test body: nesting a match on the read's
/// `Result String String` inside the write's `Result String I64` is the
/// two-different-type-variables shape the checker cannot handle.
def wrote_then_read (wrote : Result String I64) (out : String) : IO Bool := do {
    match wrote {
        Result.err _ => return false,
        Result.ok n => read_and_check n out,
    }
}

def read_and_check (n : I64) (out : String) : IO Bool := do {
    let read <- read_out (String.concat out "/api/index.html");
    match read {
        Result.err _ => return false,
        Result.ok html => return (I64.beq n 2 && String.contains html "<a href=\"./list.html\">"),
    }
}

#[test]
def test_write_pages_refuses_a_duplicate_path : IO Bool := do {
    let out : String := "/tmp/acorn-write-pages-dup";
    let _ <- exec_cmd "rm" ["-rf", out];
    let wrote <- Site.write_pages out [link_page "api/index.html" "./list.html", link_page "api/index.html" "./list.html"];
    dup_then_read wrote out
}

/// The duplicate must be refused with the path named, and refused BEFORE
/// writing: nothing may exist at the path. Same split as above -- the
/// read's `Result String String` cannot be matched inside the write's
/// `Result String I64`.
def dup_then_read (wrote : Result String I64) (out : String) : IO Bool := do {
    match wrote {
        Result.ok _ => return false,
        Result.err e => dup_refused_before_write e out,
    }
}

def dup_refused_before_write (e : String) (out : String) : IO Bool := do {
    let read <- read_out (String.concat out "/api/index.html");
    match read {
        Result.err _ => return (String.contains e "duplicate output path: api/index.html"),
        Result.ok _ => return false,
    }
}

#[test]
def test_write_pages_refuses_a_broken_link : IO Bool := do {
    let out : String := "/tmp/acorn-write-pages-broken";
    let _ <- exec_cmd "rm" ["-rf", out];
    let wrote <- Site.write_pages out [link_page "api/index.html" "./missing.html"];
    match wrote {
        Result.ok _ => return false,
        Result.err e =>
            let shared : Shared String := Shared.of e in
            return (String.contains (Shared.get shared) "broken internal links"
                && String.contains (Shared.get shared) "missing.html"),
    }
}
