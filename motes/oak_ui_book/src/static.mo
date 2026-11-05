// `book_static`: write the static gallery and the shared stylesheet.
//
//     OAK_UI_BOOK_OUT=dir monad run motes/oak_ui_book --bin book_static
//
// Writes `<dir>/oak-ui.css`, `<dir>/index.html` and `<dir>/<story>.html`
// (default dir: target-monad/oak-ui-book). Pure rendering plus file writes;
// no browser runtime involved.

use std::process {exec_cmd}
use std::path {Path, Path.of}
use std::io {IO.write_file, IO.get_env}
use lib::story {Book.Story, Book.Story.id}
use lib::stories::all {Book.all_stories}
use lib::gallery {Book.stylesheet, Book.gallery_page, Book.story_page}

def write_or_report (dir : String) (name : String) (content : String) : IO Bool :=
    match Path.of (String.concat_list [dir, "/", name]) {
        Result.err e => do {
            IO.println (String.concat_list ["book_static: bad path ", name, ": ", e]);
            IO.pure false
        },
        Result.ok p => write_checked p name content,
    }

def write_checked (p : Path) (name : String) (content : String) : IO Bool := do {
    let r <- IO.write_file p content;
    match r {
        Result.ok _ => IO.pure true,
        Result.err _ => do {
            IO.println (String.concat "book_static: could not write " name);
            IO.pure false
        },
    }
}

#[terminating]
def write_stories (dir : String) (stories : List Book.Story) : IO Bool :=
    match stories {
        List.empty => IO.pure true,
        List.cons s rest => do {
            let ok <- write_or_report dir (String.concat (Book.Story.id s) ".html") (Book.story_page s);
            let rest_ok <- write_stories dir rest;
            IO.pure (ok && rest_ok)
        },
    }

/// 0 when every file was written, 1 otherwise (the process exit code).
def run (dir : String) : IO I64 := do {
    let _ <- exec_cmd "mkdir" ["-p", dir];
    let css_ok <- write_or_report dir "oak-ui.css" Book.stylesheet;
    let index_ok <- write_or_report dir "index.html" (Book.gallery_page Book.all_stories);
    let stories_ok <- write_stories dir Book.all_stories;
    if css_ok && index_ok && stories_ok
    then do {
        IO.println (String.concat "book_static: wrote the gallery to " dir);
        IO.pure 0
    }
    else IO.pure 1
}

def main : IO I64 := do {
    let out <- IO.get_env "OAK_UI_BOOK_OUT";
    match out {
        Option.some dir => run dir,
        Option.none => run "target-monad/oak-ui-book",
    }
}
