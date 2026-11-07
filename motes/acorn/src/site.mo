/// Site assembly: read the sources, render each page, write the output.
///
/// The book's chapters come from `SUMMARY.md`, in its order, and render to
/// `<out>/<book_dir>/<chapter>.html` (mdBook's URLs), each with the sidebar
/// and its prev/next neighbours. mdBook's other pages come along: `index.html`
/// (the first chapter again), `print.html` (every chapter on one page) and
/// `404.html`; the book source's non-markdown files (`images/`) are copied
/// beside the pages. mdBook's `toc.html` is its no-JavaScript sidebar
/// fallback, which a static sidebar does not need.
use std::io {IO.read_file, IO.write_file, IO.list_dir, IO.is_dir}
use std::path {Path, Path.of, Path.to_string, Path.file_name}
use std::process {exec_cmd}
use std::list {List.intercalate, List.filter}
use xml_html::html {Html.Node, Html.Attr}
use markdown::types {Markdown.Document}
use markdown::options {Markdown.HtmlOptions, Markdown.default_html_options, Markdown.site_options}
use markdown::parse {Markdown.parse_with}
use markdown::html {Markdown.heading_texts, Markdown.to_html_nodes_with}
use lib::config {SiteConfig}
use lib::layout {Layout.render, Layout.chapter_href, PageSpec, BookNav}
use lib::passes {Passes.chapter, Passes.dup_nodes, Passes.dup_list}
use lib::toc {TocEntry, Toc.of_nodes}
use lib::links {PageLinks, Links.of_page, Links.broken}
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

/// A chapter's title, its on-page TOC and its rendered body, passes applied.
pub struct ChapterBody {
    title : String,
    toc : List TocEntry,
    body : List Html.Node,
}

/// Render one chapter's markdown. `stem` names the chapter when it has no
/// heading. Pure: the IO layer only reads and writes.
pub def Site.chapter_body (stem : String) (src : String) : ChapterBody :=
    let doc : Shared Markdown.Document := Shared.of (Markdown.parse_with Markdown.site_options src) in
    with_toc (chapter_title stem (Shared.get doc))
        (Passes.dup_nodes (Passes.chapter (Markdown.to_html_nodes_with chapter_html_options (Shared.get doc))))

def with_toc (title : String) (nodes : Pair (List Html.Node) (List Html.Node)) : ChapterBody :=
    match nodes {
        Pair.pair for_toc body => { title := title, toc := Toc.of_nodes for_toc, body := body },
    }

def page_of (book : Option BookNav) (b : ChapterBody) : PageSpec :=
    match b {
        { title, toc, body } => { title := title, root := "../", body := body, toc := toc, book := book },
    }

/// One chapter as a full page; `book` is its place in the book (none renders
/// it without a sidebar).
pub def Site.render_chapter (cfg : SiteConfig) (book : Option BookNav) (stem : String) (src : String) : String :=
    Layout.render cfg (page_of book (Site.chapter_body stem src))

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

instance Copy ChapterPage {
    def copy (p : ChapterPage) : Pair ChapterPage ChapterPage := Pair.pair p p
}

/// A chapter read from disk.
struct Loaded {
    page : ChapterPage,
    src : String,
}

/// Read every chapter's source, stopping at the first error.
def load_all (dirs : BookDirs) (pages : List ChapterPage) (acc : List Loaded) : IO (Result String (List Loaded)) :=
    match pages {
        List.empty => return (Result.ok (List.reverse acc)),
        List.cons p rest => load_then dirs p rest acc,
    }

// Mutual recursion with `load_all` on a strictly shorter `rest`.
#[terminating]
def load_then (dirs : BookDirs) (p : ChapterPage) (rest : List ChapterPage) (acc : List Loaded) : IO (Result String (List Loaded)) := do {
    let read <- read_text (join dirs.src (String.concat p.chapter.stem ".md"));
    match read {
        Result.err e => return (Result.err e),
        Result.ok src =>
            let one : Loaded := { page := p, src := src } in
            load_all dirs rest (List.cons one acc),
    }
}

/// A chapter rendered, before the page shell.
struct Rendered {
    page : ChapterPage,
    body : ChapterBody,
}

def render_loaded (l : Loaded) : Rendered :=
    match l {
        { page, src } => { page := page, body := Site.chapter_body page.chapter.stem src },
    }

/// The page's links for the gate, and the page itself, still whole.
def scan_rendered (book_dir : String) (r : Rendered) : Pair PageLinks Rendered :=
    match r {
        { page, body } => scan_body book_dir page body,
    }

def scan_body (book_dir : String) (page : ChapterPage) (b : ChapterBody) : Pair PageLinks Rendered :=
    match b {
        { title, toc, body } =>
            match Passes.dup_nodes body {
                Pair.pair for_links for_page =>
                    let path : String := join book_dir (String.concat page.chapter.stem ".html") in
                    let kept : ChapterBody := { title := title, toc := toc, body := for_page } in
                    let r : Rendered := { page := page, body := kept } in
                    Pair.pair (Links.of_page path for_links) r,
            },
    }

/// Write one page; the chapter named `index_stem` is written again as
/// `index.html`. Returns the number of files written.
def write_rendered (cfg : SiteConfig) (dirs : BookDirs) (entries : Shared (List NavEntry)) (index_stem : String) (r : Rendered) : IO (Result String I64) :=
    match r {
        { page, body } =>
            let nav : BookNav :=
                { entries := entries, current := page.chapter.stem, prev := page.prev, next := page.next } in
            let html : String := Layout.render cfg (page_of (Option.some nav) body) in
            write_twice (join dirs.out (String.concat page.chapter.stem ".html"))
                (if String.beq page.chapter.stem index_stem then Option.some (join dirs.out "index.html") else Option.none)
                html,
    }

def write_twice (target : String) (also : Option String) (html : String) : IO (Result String I64) := do {
    let wrote <- write_page target html;
    match wrote {
        Result.err e => return (Result.err e),
        Result.ok _ => write_also also html,
    }
}

def write_also (also : Option String) (html : String) : IO (Result String I64) :=
    match also {
        Option.none => return (Result.ok 1),
        Option.some target => count_write 2 (write_page target html),
    }

def count_write (n : I64) (w : IO (Result String Unit)) : IO (Result String I64) := do {
    let wrote <- w;
    match wrote {
        Result.err e => return (Result.err e),
        Result.ok _ => return (Result.ok n),
    }
}

/// Write every page, stopping at the first error; returns the count.
def write_all (cfg : SiteConfig) (dirs : BookDirs) (entries : Shared (List NavEntry)) (index_stem : String) (pages : List Rendered) (done : I64) : IO (Result String I64) :=
    match pages {
        List.empty => return (Result.ok done),
        List.cons p rest => write_then cfg dirs entries index_stem p rest done,
    }

// Mutual recursion with `write_all` on a strictly shorter `rest`; the checker
// does not see through the IO bind between them.
#[terminating]
def write_then (cfg : SiteConfig) (dirs : BookDirs) (entries : Shared (List NavEntry)) (index_stem : String) (p : Rendered) (rest : List Rendered) (done : I64) : IO (Result String I64) := do {
    let one <- write_rendered cfg dirs entries index_stem p;
    match one {
        Result.err e => return (Result.err e),
        Result.ok n => write_all cfg dirs entries index_stem rest (done + n),
    }
}

instance Copy Rendered {
    def copy (r : Rendered) : Pair Rendered Rendered := Pair.pair r r
}

/// The chapters followed by `print.html`: every chapter's body in order on
/// one page, with no TOC.
def with_print (title : String) (rendered : List Rendered) : List Rendered :=
    match Passes.dup_list rendered {
        Pair.pair for_print pages => List.append pages [print_page title (all_bodies for_print)],
    }

def all_bodies (rs : List Rendered) : List Html.Node :=
    match rs {
        List.empty => List.empty,
        List.cons r rest => List.append (rendered_body r) (all_bodies rest),
    }

def rendered_body (r : Rendered) : List Html.Node :=
    match r {
        { body, .. } => body.body,
    }

def print_chapter : NavChapter :=
    { title := "Print", stem := "print" }

def print_page (title : String) (body : List Html.Node) : Rendered :=
    let page : ChapterPage := { chapter := print_chapter, prev := Option.none, next := Option.none } in
    let b : ChapterBody := { title := title, toc := List.empty, body := body } in
    { page := page, body := b }

/// The site root as an absolute URL prefix, for a page served at any depth.
def absolute_root (base_url : String) : String :=
    if String.ends_with base_url "/" then base_url else String.concat base_url "/"

def not_found_body (href : String) : List Html.Node :=
    [Html.Node.node_element "h1" List.empty [Html.Node.node_text "Page not found"],
        Html.Node.node_element "p" List.empty
            [Html.Node.node_text "There is no page at this address. Start from the ",
                Html.Node.node_element "a" [Html.Attr.attr "href" href] [Html.Node.node_text "introduction"],
                Html.Node.node_text "."]]

/// `404.html`: served for any missing path, so every link is absolute
/// (from `base_url`) rather than relative to the page.
def not_found_page (cfg : SiteConfig) (entries : Shared (List NavEntry)) (index_stem : String) : PageSpec :=
    let root : String := absolute_root cfg.base_url in
    let nav : BookNav := { entries := entries, current := "", prev := Option.none, next := Option.none } in
    { title := "Page not found", root := root,
        body := not_found_body (Layout.chapter_href cfg root index_stem), book := Option.some nav }

def write_not_found (cfg : SiteConfig) (dirs : BookDirs) (entries : Shared (List NavEntry)) (index_stem : String) (written : I64) : IO (Result String I64) :=
    count_write (written + 1)
        (write_page (join dirs.out "404.html") (Layout.render cfg (not_found_page cfg entries index_stem)))

/// Build the site; returns the number of files written.
pub def Site.build (cfg : SiteConfig) : IO (Result String I64) := do {
    let made <- mkdir_p cfg.out_dir;
    match made {
        Result.err e => return (Result.err e),
        Result.ok _ => assets_then_book cfg,
    }
}

def assets_then_book (cfg : SiteConfig) : IO (Result String I64) := do {
    let copied <- copy_assets cfg.assets_dir cfg.out_dir;
    match copied {
        Result.err e => return (Result.err e),
        Result.ok n => book_then_count cfg n,
    }
}

def book_then_count (cfg : SiteConfig) (assets : I64) : IO (Result String I64) := do {
    let dirs : BookDirs := { src := cfg.book_src, out := join cfg.out_dir cfg.book_dir };
    let pages <- build_book cfg dirs;
    match pages {
        Result.err e => return (Result.err e),
        Result.ok n => return (Result.ok (n + assets)),
    }
}

/// Copy every file in the assets directory into the output root.
def copy_assets (assets : String) (out : String) : IO (Result String I64) :=
    match Path.of assets {
        Result.err e => return (Result.err e),
        Result.ok dir => list_and_copy dir out,
    }

def list_and_copy (dir : Path) (out : String) : IO (Result String I64) := do {
    let listed <- entries_of dir;
    match listed {
        Result.err e => return (Result.err e),
        Result.ok files => copy_all files out 0,
    }
}

/// A directory's entries; a missing directory is an error, not an empty
/// listing (`IO.list_dir` cannot tell the two apart), so a wrong `assets`
/// path never publishes pages without their stylesheet.
def entries_of (dir : Path) : IO (Result String (List Path)) := do {
    let present <- IO.is_dir dir;
    if present
    then listed_ok dir
    else return (Result.err (String.concat (Path.to_string dir) ": not a directory"))
}

def listed_ok (dir : Path) : IO (Result String (List Path)) := do {
    let files <- IO.list_dir dir;
    return (Result.ok files)
}

def copy_all (files : List Path) (out : String) (done : I64) : IO (Result String I64) :=
    match files {
        List.empty => return (Result.ok done),
        List.cons f rest => copy_then f rest out done,
    }

// Mutual recursion with `copy_all` on a strictly shorter `rest`.
#[terminating]
def copy_then (f : Path) (rest : List Path) (out : String) (done : I64) : IO (Result String I64) := do {
    let one <- copy_file f out;
    match one {
        Result.err e => return (Result.err e),
        Result.ok _ => copy_all rest out (done + 1),
    }
}

def copy_file (f : Path) (out : String) : IO (Result String Unit) := do {
    let target : String := join out (Path.file_name f);
    let read <- read_path f;
    match read {
        Result.err e => return (Result.err e),
        Result.ok text => write_page target text,
    }
}

def build_book (cfg : SiteConfig) (dirs : BookDirs) : IO (Result String I64) := do {
    let made <- mkdir_p dirs.out;
    match made {
        Result.err e => return (Result.err e),
        Result.ok _ => book_files_then_pages cfg dirs,
    }
}

def book_files_then_pages (cfg : SiteConfig) (dirs : BookDirs) : IO (Result String I64) := do {
    let copied <- copy_book_files dirs;
    match copied {
        Result.err e => return (Result.err e),
        Result.ok n => pages_plus n (read_summary cfg dirs),
    }
}

def pages_plus (n : I64) (pages : IO (Result String I64)) : IO (Result String I64) := do {
    let built <- pages;
    match built {
        Result.err e => return (Result.err e),
        Result.ok m => return (Result.ok (n + m)),
    }
}

/// Copy the book source's non-markdown entries (`images/`) beside the
/// pages, as mdBook does. `cp -R` keeps binary files and directories whole.
def copy_book_files (dirs : BookDirs) : IO (Result String I64) :=
    match Path.of dirs.src {
        Result.err e => return (Result.err e),
        Result.ok dir => list_book_files dir dirs.out,
    }

def list_book_files (dir : Path) (out : String) : IO (Result String I64) := do {
    let listed <- entries_of dir;
    match listed {
        Result.err e => return (Result.err e),
        Result.ok entries => cp_all (List.filter (fn (p : Path) => Bool.not (String.ends_with (Path.file_name p) ".md")) entries) out 0,
    }
}

def cp_all (files : List Path) (out : String) (done : I64) : IO (Result String I64) :=
    match files {
        List.empty => return (Result.ok done),
        List.cons f rest => cp_then f rest out done,
    }

// Mutual recursion with `cp_all` on a strictly shorter `rest`.
#[terminating]
def cp_then (f : Path) (rest : List Path) (out : String) (done : I64) : IO (Result String I64) := do {
    let from : String := Path.to_string f;
    let rc <- exec_cmd "cp" ["-R", from, out];
    if rc == 0
    then cp_all rest out (done + 1)
    else return (Result.err (String.concat "cp -R failed: " from))
}

def read_summary (cfg : SiteConfig) (dirs : BookDirs) : IO (Result String I64) := do {
    let read <- read_text (join dirs.src "SUMMARY.md");
    match read {
        Result.err e => return (Result.err e),
        Result.ok src => build_from_summary cfg dirs src,
    }
}

def build_from_summary (cfg : SiteConfig) (dirs : BookDirs) (summary : String) : IO (Result String I64) := do {
    let entries : Shared (List NavEntry) := Shared.of (Summary.parse summary);
    let loaded <- load_all dirs (Site.with_neighbours Option.none (Summary.chapters (Shared.get entries))) List.empty;
    match loaded {
        Result.err e => return (Result.err e),
        Result.ok ls =>
            gate_then_write cfg dirs entries (first_stem (Summary.chapters (Shared.get entries)))
                (List.map (scan_rendered cfg.book_dir) (with_print cfg.title (List.map render_loaded ls))),
    }
}

/// Write the pages only when no internal link is broken.
def gate_then_write (cfg : SiteConfig) (dirs : BookDirs) (entries : Shared (List NavEntry)) (index_stem : String) (scanned : List (Pair PageLinks Rendered)) : IO (Result String I64) :=
    match unzip scanned {
        Pair.pair links pages =>
            match Links.broken links {
                List.empty => pages_then_not_found cfg dirs entries index_stem pages,
                List.cons first more => return (Result.err (broken_report (List.cons first more))),
            },
    }

def pages_then_not_found (cfg : SiteConfig) (dirs : BookDirs) (entries : Shared (List NavEntry)) (index_stem : String) (pages : List Rendered) : IO (Result String I64) := do {
    let wrote <- write_all cfg dirs entries index_stem pages 0;
    match wrote {
        Result.err e => return (Result.err e),
        Result.ok n => write_not_found cfg dirs entries index_stem n,
    }
}

/// The first chapter's stem, the one `index.html` repeats.
def first_stem (cs : List NavChapter) : String :=
    match cs {
        List.empty => "",
        List.cons c _ => c.stem,
    }

def broken_report (problems : List String) : String :=
    String.concat "broken internal links:\n  " (List.intercalate "\n  " problems)

def unzip (ps : List (Pair PageLinks Rendered)) : Pair (List PageLinks) (List Rendered) :=
    match ps {
        List.empty => Pair.pair List.empty List.empty,
        List.cons p rest => cons_pair p (unzip rest),
    }

def cons_pair (p : Pair PageLinks Rendered) (acc : Pair (List PageLinks) (List Rendered)) : Pair (List PageLinks) (List Rendered) :=
    match p {
        Pair.pair l r =>
            match acc {
                Pair.pair ls rs => Pair.pair (List.cons l ls) (List.cons r rs),
            },
    }
