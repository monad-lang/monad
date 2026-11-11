/// Site assembly: read the sources, render each page, gate, write.
///
/// The site's chrome is its caller's (`Site.build_with` takes a `Shell`), and
/// so are any pages that are not book pages (`extra`, e.g. a landing page at
/// `index.html`); `Site.build` is the plain configuration-only builder. The
/// `assets` (acorn's own stylesheet) and `static` trees are copied into the
/// output root when the configuration names them.
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
use std::list {List.intercalate, List.filter, List.any}
use xml_html::html {Html.Node, Html.Attr, Html.to_string}
use markdown::types {Markdown.Document}
use markdown::options {Markdown.HtmlOptions, Markdown.default_html_options, Markdown.site_options}
use markdown::parse {Markdown.parse_with}
use markdown::html {Markdown.heading_texts, Markdown.to_html_nodes_with}
use lib::config {SiteConfig}
use lib::layout {
    Layout.render, Layout.render_with, Layout.document, Layout.document_with,
    Layout.chapter_href, PageSpec, BookNav, Shell,
}
use lib::passes {Passes.chapter, Passes.dup_nodes, Passes.dup_node, Passes.dup_list}
use lib::toc {TocEntry, Toc.of_nodes}
use lib::links {PageLinks, Links.of_page, Links.with_aliases, Links.broken}
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

/// One chapter in the caller's chrome (see `Layout.page_with`).
pub def Site.render_chapter_with (cfg : SiteConfig) (shell : Shared Shell) (book : Option BookNav) (stem : String) (src : String) : String :=
    Layout.render_with cfg shell (page_of book (Site.chapter_body stem src))

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
        Result.err e => return (Result.err (PathError.to_string e)),
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
        Result.err e => return (Result.err (PathError.to_string e)),
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

/// A finished page: its whole document and the paths under the output root
/// it is written to. The link gate reads it at the first path.
pub struct Built {
    paths : List String,
    doc : Html.Node,
}

/// A page written to one path.
pub def Built.page (path : String) (doc : Html.Node) : Built :=
    { paths := [path], doc := doc }

/// A page written to several paths from one document (`index.html` repeats
/// the first chapter; the 404 page is served from the root and the book).
pub def Built.pages (paths : List String) (doc : Html.Node) : Built :=
    { paths := paths, doc := doc }

/// A chapter in the book shell; the chapter named `index_stem` is written
/// again as the book's `index.html`.
def built_chapter (cfg : SiteConfig) (shell : Shared Shell) (entries : Shared (List NavEntry)) (index_stem : String) (r : Rendered) : Built :=
    match r {
        { page, body } =>
            let stem : String := page.chapter.stem in
            let nav : BookNav := { entries := entries, current := stem, prev := page.prev, next := page.next } in
            let own : String := join cfg.book_dir (String.concat stem ".html") in
            let paths : List String := if String.beq stem index_stem then [own, join cfg.book_dir "index.html"] else [own] in
            { paths := paths, doc := Layout.document_with cfg shell (page_of (Option.some nav) body) },
    }

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

/// Written at the book's `404.html` (mdBook's location, for parity) and at
/// the output root: GitHub Pages only serves a custom `/404.html` from the
/// root, and the page's links are absolute so one document fits both.
def built_not_found (cfg : SiteConfig) (shell : Shared Shell) (entries : Shared (List NavEntry)) (index_stem : String) : Built :=
    { paths := [join cfg.book_dir "404.html", "404.html"],
        doc := Layout.document_with cfg shell (not_found_page cfg entries index_stem) }

/// The page's links for the gate (at its first path, with the rest as
/// aliases), and the page itself, still whole.
def scan_built (b : Built) : Pair PageLinks Built :=
    match b {
        { paths, doc } =>
            match Passes.dup_list paths {
                Pair.pair for_gate kept_paths =>
                    match Passes.dup_node doc {
                        Pair.pair for_links kept_doc =>
                            let kept : Built := { paths := kept_paths, doc := kept_doc } in
                            Pair.pair (links_for_paths for_gate [for_links]) kept,
                    },
            },
    }

def links_for_paths (paths : List String) (nodes : List Html.Node) : PageLinks :=
    match paths {
        List.empty => Links.of_page "" nodes,
        List.cons first rest => Links.with_aliases rest (Links.of_page first nodes),
    }

/// Write one page to each of its paths; returns the number of files.
def write_built (out : String) (b : Built) : IO (Result String I64) :=
    match b {
        { paths, doc } => write_paths out paths (Html.to_string doc) 0,
    }

def write_paths (out : String) (paths : List String) (html : String) (done : I64) : IO (Result String I64) :=
    match paths {
        List.empty => return (Result.ok done),
        List.cons p rest => write_path_then out p rest html done,
    }

// Mutual recursion with `write_paths` on a strictly shorter `rest`.
#[terminating]
def write_path_then (out : String) (p : String) (rest : List String) (html : String) (done : I64) : IO (Result String I64) := do {
    let wrote <- write_page (join out p) html;
    match wrote {
        Result.err e => return (Result.err e),
        Result.ok _ => write_paths out rest html (done + 1),
    }
}

/// Write every page, stopping at the first error; returns the count.
def write_all (out : String) (pages : List Built) (done : I64) : IO (Result String I64) :=
    match pages {
        List.empty => return (Result.ok done),
        List.cons p rest => write_then out p rest done,
    }

// Mutual recursion with `write_all` on a strictly shorter `rest`; the checker
// does not see through the IO bind between them.
#[terminating]
def write_then (out : String) (p : Built) (rest : List Built) (done : I64) : IO (Result String I64) := do {
    let one <- write_built out p;
    match one {
        Result.err e => return (Result.err e),
        Result.ok n => write_all out rest (done + n),
    }
}

/// What the caller supplies beyond the configuration: the site chrome and
/// any pages that are not part of the book. Both are shared because every
/// page of the build reads them.
pub struct SiteSpec {
    shell : Shared Shell,
    extra : Shared (List Built),
}

/// Every field is shared, so the spec is cheap to thread through the build.
pub instance Copy SiteSpec {
    def copy (s : SiteSpec) : Pair SiteSpec SiteSpec := Pair.pair s s
}

/// Build the site in acorn's own chrome, without extra pages; returns the
/// number of files written (a copied directory counts once).
pub def Site.build (cfg : SiteConfig) : IO (Result String I64) :=
    Site.build_with cfg (Shared.of (Shell.default cfg)) List.empty

/// Build the site in the caller's chrome, appending its extra pages.
pub def Site.build_with (cfg : SiteConfig) (shell : Shared Shell) (extra : List Built) : IO (Result String I64) := do {
    let spec : SiteSpec := { shell := shell, extra := Shared.of extra };
    let made <- mkdir_p cfg.out_dir;
    match made {
        Result.err e => return (Result.err e),
        Result.ok _ => trees_then_pages cfg spec,
    }
}

def trees_then_pages (cfg : SiteConfig) (spec : SiteSpec) : IO (Result String I64) := do {
    let assets <- copy_if cfg.assets_dir cfg.out_dir false;
    match assets {
        Result.err e => return (Result.err e),
        Result.ok n => count_then n (static_then_pages cfg spec),
    }
}

def static_then_pages (cfg : SiteConfig) (spec : SiteSpec) : IO (Result String I64) := do {
    let copied <- copy_if cfg.static_dir cfg.out_dir false;
    match copied {
        Result.err e => return (Result.err e),
        Result.ok n => count_then n (build_book cfg spec { src := cfg.book_src, out := join cfg.out_dir cfg.book_dir }),
    }
}

/// Copy a tree when the configuration names one; `""` means the site has no
/// such tree.
def copy_if (dir : String) (out : String) (skip_md : Bool) : IO (Result String I64) :=
    if String.is_empty dir
    then return (Result.ok 0)
    else copy_entries dir out skip_md

/// `n` plus what `rest` reports.
def count_then (n : I64) (rest : IO (Result String I64)) : IO (Result String I64) := do {
    let built <- rest;
    match built {
        Result.err e => return (Result.err e),
        Result.ok m => return (Result.ok (n + m)),
    }
}

/// Copy a directory's entries into `out` with `cp -R` (binary files and
/// subdirectories whole); `skip_md` leaves out markdown sources.
def copy_entries (src : String) (out : String) (skip_md : Bool) : IO (Result String I64) :=
    match Path.of src {
        Result.err e => return (Result.err (PathError.to_string e)),
        Result.ok dir => list_then_copy dir out skip_md,
    }

def list_then_copy (dir : Path) (out : String) (skip_md : Bool) : IO (Result String I64) := do {
    let listed <- entries_of dir;
    match listed {
        Result.err e => return (Result.err e),
        Result.ok entries =>
            cp_all (List.filter (fn (p : Path) => Bool.not (skip_md && String.ends_with (Path.file_name p) ".md")) entries) out 0,
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

/// The book: its source's non-markdown entries (`images/`) copied beside
/// the pages, as mdBook does, then every page.
def build_book (cfg : SiteConfig) (spec : SiteSpec) (dirs : BookDirs) : IO (Result String I64) := do {
    let made <- mkdir_p dirs.out;
    match made {
        Result.err e => return (Result.err e),
        Result.ok _ => book_files_then_pages cfg spec dirs,
    }
}

def book_files_then_pages (cfg : SiteConfig) (spec : SiteSpec) (dirs : BookDirs) : IO (Result String I64) := do {
    let copied <- copy_entries dirs.src dirs.out true;
    match copied {
        Result.err e => return (Result.err e),
        Result.ok n => count_then n (read_summary cfg spec dirs),
    }
}

def read_summary (cfg : SiteConfig) (spec : SiteSpec) (dirs : BookDirs) : IO (Result String I64) := do {
    let read <- read_text (join dirs.src "SUMMARY.md");
    match read {
        Result.err e => return (Result.err e),
        Result.ok src => build_from_summary cfg spec dirs src,
    }
}

def build_from_summary (cfg : SiteConfig) (spec : SiteSpec) (dirs : BookDirs) (summary : String) : IO (Result String I64) := do {
    let entries : Shared (List NavEntry) := Shared.of (Summary.parse summary);
    let loaded <- load_all dirs (Site.with_neighbours Option.none (Summary.chapters (Shared.get entries))) List.empty;
    match loaded {
        Result.err e => return (Result.err e),
        Result.ok ls => gate_then_write cfg.out_dir (site_pages cfg spec entries ls),
    }
}

/// Every page of the book: the chapters, `print.html` and `404.html`, then
/// the caller's extra pages.
def site_pages (cfg : SiteConfig) (spec : SiteSpec) (entries : Shared (List NavEntry)) (ls : List Loaded) : List Built :=
    let index_stem : String := first_stem (Summary.chapters (Shared.get entries)) in
    let chapters : List Built :=
        List.map (built_chapter cfg spec.shell entries index_stem) (with_print cfg.title (List.map render_loaded ls)) in
    List.append chapters
        (List.cons (built_not_found cfg spec.shell entries index_stem) (Shared.get spec.extra))

/// Write the pages only when no internal link is broken. The gate reads whole
/// documents: the shell's header, sidebar and pager links as well as the body.
/// A path claimed twice is a build error, not a silent overwrite.
def gate_then_write (out : String) (pages : List Built) : IO (Result String I64) :=
    let all : Shared (List Built) := Shared.of pages in
    match first_duplicate_path (Shared.get all) List.empty {
        Option.some p => return (Result.err (String.concat "duplicate output path: " p)),
        Option.none =>
            match unzip (List.map scan_built (Shared.get all)) {
                Pair.pair links built =>
                    match Links.broken links {
                        List.empty => write_all out built 0,
                        List.cons first more => return (Result.err (broken_report (List.cons first more))),
                    },
            },
    }

/// The first output path two pages claim, if any.
#[terminating]
def first_duplicate_path (pages : List Built) (seen : List String) : Option String :=
    match pages {
        List.empty => Option.none,
        List.cons b rest => duplicate_for_page b rest seen,
    }

// Part of the `first_duplicate_path` cycle; `rest` shrinks on every turn.
#[terminating]
def duplicate_for_page (b : Built) (rest : List Built) (seen : List String) : Option String :=
    match b {
        { paths, .. } =>
            match Passes.dup_list paths {
                Pair.pair for_check for_seen =>
                    let shared : Shared (List String) := Shared.of seen in
                    match first_duplicate_in for_check (Shared.get shared) {
                        Option.some p => Option.some p,
                        Option.none => first_duplicate_path rest (List.append for_seen (Shared.get shared)),
                    },
            },
    }

/// A duplicate within one page's own paths, or against the paths already
/// seen.
def first_duplicate_in (paths : List String) (seen : List String) : Option String :=
    match paths {
        List.empty => Option.none,
        List.cons p rest =>
            let shared : Shared (List String) := Shared.of seen in
            let hit : Bool := List.any (fn (q : String) => String.beq q p) (Shared.get shared) in
            if hit
            then Option.some p
            else first_duplicate_in rest (List.cons p (Shared.get shared)),
    }

/// The first chapter's stem, the one the book's `index.html` repeats.
def first_stem (cs : List NavChapter) : String :=
    match cs {
        List.empty => "",
        List.cons c _ => c.stem,
    }

def broken_report (problems : List String) : String :=
    String.concat "broken internal links:\n  " (List.intercalate "\n  " problems)

def unzip (ps : List (Pair PageLinks Built)) : Pair (List PageLinks) (List Built) :=
    match ps {
        List.empty => Pair.pair List.empty List.empty,
        List.cons p rest => cons_pair p (unzip rest),
    }

def cons_pair (p : Pair PageLinks Built) (acc : Pair (List PageLinks) (List Built)) : Pair (List PageLinks) (List Built) :=
    match p {
        Pair.pair l r =>
            match acc {
                Pair.pair ls rs => Pair.pair (List.cons l ls) (List.cons r rs),
            },
    }
