/// Site assembly: read the sources, render each page, write the output.
///
/// The book's chapters come from `SUMMARY.md`, in its order, and render to
/// `<out>/<book_dir>/<chapter>.html` (mdBook's URLs), each with the sidebar
/// and its prev/next neighbours.
use std::io {IO.read_file, IO.write_file}
use std::path {Path, Path.of, Path.to_string}
use std::process {exec_cmd}
use markdown::types {Markdown.Document}
use markdown::options {Markdown.HtmlOptions, Markdown.default_html_options, Markdown.site_options}
use markdown::parse {Markdown.parse_with}
use markdown::html {Markdown.heading_texts, Markdown.to_html_nodes_with}
use lib::config {SiteConfig}
use lib::layout {Layout.render, PageSpec, BookNav}
use lib::passes {Passes.chapter}
use lib::summary {NavEntry, NavChapter, Summary.parse, Summary.chapters}

/// The rendering options for book chapters: heading ids on, so the TOC and
/// intra-page links have anchors.
def chapter_html_options : Markdown.HtmlOptions :=
    { Markdown.default_html_options with heading_ids := true }

/// A chapter's title: its first heading, else the file stem.
def chapter_title (stem : String) (doc : Markdown.Document) : String :=
    match Markdown.heading_texts doc.blocks {
        List.cons first _ => first,
        List.empty => stem,
    }

/// Render one chapter's markdown to a full page. `stem` names the chapter
/// when it has no heading; `book` is its place in the book (none renders
/// the page without a sidebar). Pure: the IO layer only reads and writes.
pub def Site.render_chapter (cfg : SiteConfig) (book : Option BookNav) (stem : String) (src : String) : String :=
    let doc : Shared Markdown.Document := Shared.of (Markdown.parse_with Markdown.site_options src) in
    let page : PageSpec :=
        { title := chapter_title stem (Shared.get doc), root := "../",
            body := Passes.chapter (Markdown.to_html_nodes_with chapter_html_options (Shared.get doc)),
            book := book } in
    Layout.render cfg page

/// One chapter to build, with its neighbours in reading order.
pub struct ChapterPage {
    chapter : NavChapter,
    prev : Option NavChapter,
    next : Option NavChapter,
}

def chapter_page (prev : Option NavChapter) (c : NavChapter) (next : Option NavChapter) : ChapterPage :=
    { chapter := c, prev := prev, next := next }

/// Pair every chapter with its neighbours.
pub def Site.with_neighbours (prev : Option NavChapter) (cs : List NavChapter) : List ChapterPage :=
    match cs {
        List.empty => List.empty,
        List.cons c rest => page_then prev c rest,
    }

// Mutual recursion with `Site.with_neighbours` on the same tail it was
// given, rebuilt from its parts; the checker does not see through that.
#[terminating]
def page_then (prev : Option NavChapter) (c : NavChapter) (rest : List NavChapter) : List ChapterPage :=
    match rest {
        List.empty => [chapter_page prev c Option.none],
        List.cons n more =>
            List.cons (chapter_page prev c (Option.some n))
                (Site.with_neighbours (Option.some c) (List.cons n more)),
    }

def join (a : String) (b : String) : String :=
    String.concat a (String.concat "/" b)

def mkdir_p (dir : String) : IO (Result String Unit) := do {
    let rc <- exec_cmd "mkdir" ["-p", dir];
    if rc == 0
    then return (Result.ok Unit.unit)
    else return (Result.err (String.concat "mkdir -p failed: " dir))
}

def read_text (file : String) : IO (Result String String) :=
    match Path.of file {
        Result.err e => return (Result.err e),
        Result.ok p => read_path p,
    }

def read_path (p : Path) : IO (Result String String) := do {
    let read <- IO.read_file p;
    match read {
        Result.err e => return (Result.err (String.concat (Path.to_string p) (String.concat ": " e.message))),
        Result.ok src => return (Result.ok src),
    }
}

def write_page (target : String) (html : String) : IO (Result String Unit) :=
    match Path.of target {
        Result.err e => return (Result.err e),
        Result.ok p => write_to p html,
    }

def write_to (p : Path) (html : String) : IO (Result String Unit) := do {
    let wrote <- IO.write_file p html;
    match wrote {
        Result.err e => return (Result.err (String.concat (Path.to_string p) (String.concat ": " e.message))),
        Result.ok _ => return (Result.ok Unit.unit),
    }
}

/// Where the book's pages are read from and written to.
struct BookDirs {
    src : String,
    out : String,
}

instance Copy BookDirs {
    def copy (d : BookDirs) : Pair BookDirs BookDirs := Pair.pair d d
}

def write_chapter (cfg : SiteConfig) (dirs : BookDirs) (entries : Shared (List NavEntry)) (page : ChapterPage) : IO (Result String Unit) :=
    match page {
        { chapter, prev, next } =>
            let nav : BookNav :=
                { entries := Shared.get entries, current := chapter.stem, prev := prev, next := next } in
            render_from cfg dirs chapter.stem nav,
    }

def render_from (cfg : SiteConfig) (dirs : BookDirs) (stem : String) (nav : BookNav) : IO (Result String Unit) := do {
    let read <- read_text (join dirs.src (String.concat stem ".md"));
    match read {
        Result.err e => return (Result.err e),
        Result.ok src =>
            write_page (join dirs.out (String.concat stem ".html"))
                (Site.render_chapter cfg (Option.some nav) stem src),
    }
}

/// Write every chapter, stopping at the first error; returns the count.
def write_all (cfg : SiteConfig) (dirs : BookDirs) (entries : Shared (List NavEntry)) (pages : List ChapterPage) (done : I64) : IO (Result String I64) :=
    match pages {
        List.empty => return (Result.ok done),
        List.cons p rest => write_then cfg dirs entries p rest done,
    }

// Mutual recursion with `write_all` on a strictly shorter `rest`; the checker
// does not see through the IO bind between them.
#[terminating]
def write_then (cfg : SiteConfig) (dirs : BookDirs) (entries : Shared (List NavEntry)) (p : ChapterPage) (rest : List ChapterPage) (done : I64) : IO (Result String I64) := do {
    let one <- write_chapter cfg dirs entries p;
    match one {
        Result.err e => return (Result.err e),
        Result.ok _ => write_all cfg dirs entries rest (done + 1),
    }
}

/// Build the site; returns the number of pages written.
pub def Site.build (cfg : SiteConfig) : IO (Result String I64) :=
    let dirs : BookDirs := { src := cfg.book_src, out := join cfg.out_dir cfg.book_dir } in
    build_book cfg dirs

def build_book (cfg : SiteConfig) (dirs : BookDirs) : IO (Result String I64) := do {
    let made <- mkdir_p dirs.out;
    match made {
        Result.err e => return (Result.err e),
        Result.ok _ => read_summary cfg dirs,
    }
}

def read_summary (cfg : SiteConfig) (dirs : BookDirs) : IO (Result String I64) := do {
    let read <- read_text (join dirs.src "SUMMARY.md");
    match read {
        Result.err e => return (Result.err e),
        Result.ok src => build_from_summary cfg dirs src,
    }
}

def build_from_summary (cfg : SiteConfig) (dirs : BookDirs) (summary : String) : IO (Result String I64) :=
    let entries : Shared (List NavEntry) := Shared.of (Summary.parse summary) in
    write_all cfg dirs entries (Site.with_neighbours Option.none (Summary.chapters (Shared.get entries))) 0
