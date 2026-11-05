/// Site assembly: read the sources, render each page, write the output.
///
/// Phase 0 renders every chapter in the book's source directory to
/// `<out>/<book_dir>/<chapter>.html`, keeping mdBook's URLs. Navigation from
/// `SUMMARY.md`, link rewriting and the landing page come in later phases.
use std::io {IO.read_file, IO.write_file, IO.list_dir}
use std::path {Path, Path.of, Path.to_string, Path.file_name}
use std::process {exec_cmd}
use markdown::types {Markdown.Document}
use markdown::options {Markdown.HtmlOptions, Markdown.default_html_options, Markdown.site_options}
use markdown::parse {Markdown.parse_with}
use markdown::html {Markdown.heading_texts, Markdown.to_html_nodes_with}
use lib::config {SiteConfig}
use lib::layout {Layout.render, PageSpec}

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
/// when it has no heading. Pure: the IO layer only reads and writes.
pub def Site.render_chapter (cfg : SiteConfig) (stem : String) (src : String) : String :=
    let doc : Shared Markdown.Document := Shared.of (Markdown.parse_with Markdown.site_options src) in
    let page : PageSpec :=
        { title := chapter_title stem (Shared.get doc), root := "../",
            body := Markdown.to_html_nodes_with chapter_html_options (Shared.get doc) } in
    Layout.render cfg page

/// `foo.md` → `Option.some "foo"`; anything else (and `SUMMARY.md`, which is
/// navigation, not a page) → none.
pub def Site.chapter_stem (file_name : String) : Option String :=
    let n : I64 := String.length file_name in
    if n > 3 && String.beq (String.drop (n - 3) file_name) ".md" && Bool.not (String.beq file_name "SUMMARY.md")
    then Option.some (String.slice file_name 0 (n - 3))
    else Option.none

def join (a : String) (b : String) : String :=
    String.concat a (String.concat "/" b)

def mkdir_p (dir : String) : IO (Result String Unit) := do {
    let rc <- exec_cmd "mkdir" ["-p", dir];
    if rc == 0
    then return (Result.ok Unit.unit)
    else return (Result.err (String.concat "mkdir -p failed: " dir))
}

/// One chapter to build: its source file and stem.
struct Chapter {
    file : Path,
    stem : String,
}

/// The chapters among a directory listing, in listing (sorted) order.
def chapters_of (files : List Path) : List Chapter :=
    match files {
        List.empty => List.empty,
        List.cons f rest =>
            match Site.chapter_stem (Path.file_name f) {
                Option.some stem =>
                    let c : Chapter := { file := f, stem := stem } in
                    List.cons c (chapters_of rest),
                Option.none => chapters_of rest,
            },
    }

def write_chapter (cfg : SiteConfig) (out_dir : String) (c : Chapter) : IO (Result String Unit) :=
    match c {
        { file, stem } => read_and_write cfg out_dir file stem,
    }

def read_and_write (cfg : SiteConfig) (out_dir : String) (file : Path) (stem : String) : IO (Result String Unit) := do {
    let read <- IO.read_file file;
    match read {
        Result.err e => return (Result.err (String.concat (Path.to_string file) (String.concat ": " e.message))),
        Result.ok src => write_page (join out_dir (String.concat stem ".html")) (Site.render_chapter cfg stem src),
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

/// Write every chapter, stopping at the first error; returns the count.
def write_all (cfg : SiteConfig) (out_dir : String) (cs : List Chapter) (done : I64) : IO (Result String I64) :=
    match cs {
        List.empty => return (Result.ok done),
        List.cons c rest => write_then cfg out_dir c rest done,
    }

// Mutual recursion with `write_all` on a strictly shorter `rest`; the checker
// does not see through the IO bind between them.
#[terminating]
def write_then (cfg : SiteConfig) (out_dir : String) (c : Chapter) (rest : List Chapter) (done : I64) : IO (Result String I64) := do {
    let one <- write_chapter cfg out_dir c;
    match one {
        Result.err e => return (Result.err e),
        Result.ok _ => write_all cfg out_dir rest (done + 1),
    }
}

/// Build the site; returns the number of pages written.
pub def Site.build (cfg : SiteConfig) : IO (Result String I64) :=
    let book_out : String := join cfg.out_dir cfg.book_dir in
    match Path.of cfg.book_src {
        Result.err e => return (Result.err e),
        Result.ok src_dir => build_book cfg book_out src_dir,
    }

def build_book (cfg : SiteConfig) (book_out : String) (src_dir : Path) : IO (Result String I64) := do {
    let made <- mkdir_p book_out;
    match made {
        Result.err e => return (Result.err e),
        Result.ok _ => list_and_build cfg book_out src_dir,
    }
}

def list_and_build (cfg : SiteConfig) (book_out : String) (src_dir : Path) : IO (Result String I64) := do {
    let files <- IO.list_dir src_dir;
    write_all cfg book_out (chapters_of files) 0
}
