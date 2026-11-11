// ply -- the editor binary (code-editor.md Phase 4).
//
// THIS FILE IS THE WHOLE IO SIDE. Everything below it is a pure library:
// `model.mo`/`transaction.mo` hold the text, `commands.mo` the pure step,
// `view.mo` the frame. The binary's job is the glue -- read the file,
// build the state, hand it to `tui::run_app` -- plus the argv and the
// error path.
//
// `main (args : List String) : IO I64`, not `IO Unit`: a usage error and a
// missing file are exit codes, so a built `ply nope` fails the way a shell
// script expects. The conventional target path is `src/main.mo` and the
// mote declares no `[[bin]]` table, so `monad build motes/ply` finds this
// file with no manifest edit (`Mote.bin_targets`).
//
// NO CLI PARSER DEPENDENCY. `ply [path]` is one positional: `motes/clap`
// would be a mote dependency for an `if`, and a new dependency is not free
// -- `motes/clap` is still in `[affine] mode = "warn"`, and an ownership
// build refuses a closure containing one.
//
// A MISSING FILE IS AN ERROR, NOT AN EMPTY BUFFER: `IO.read_file` answers
// `Result.err`, and this prints one line and exits 1. Opening a
// nonexistent path as a scratch buffer would silently turn `ply typo.mo`
// into an empty buffer whose save then creates the file.

use lib::model {Document, Document.of_text, Document.with_language,
    Document.with_path, EditorState, EditorState.init, EditorMsg, on_event}
use lib::commands {update}
use lib::view {View.view}
use tui::tui {App, run_app}
use tui::terminal {Terminal.size}
use std::stream {StreamError}

// ── argv ─────────────────────────────────────────────────────────────────

/// `ply [path]`: the optional first positional, and nothing else.
/// Anything past it is a usage error -- a second path silently ignored
/// would look like "the file I meant to open was not the one that
/// opened".
pub def main (args : List String) : IO I64 :=
    match args {
        List.empty => open_scratch,
        List.cons path rest => open_path path rest
    }

def open_path (path : String) (rest : List String) : IO I64 :=
    match rest {
        List.cons extra _ => usage_error extra,
        List.empty => open_file path
    }

/// A usage error: the extra argument, then how to call this program.
def usage_error (extra : String) : IO I64 := do {
    IO.write_stderr (String.concat "ply: unexpected argument: " (String.concat extra usage_tail));
    return 1
}

def usage_tail : String := "\nusage: ply [path]\n"

// ── Opening ──────────────────────────────────────────────────────────────

/// No path: a scratch buffer. The editor is still an editor with no file
/// (`Space w` refuses -- there is nowhere to write), so this is a
/// legitimate way to run it, not an error.
def open_scratch : IO I64 := do {
    let doc : Document := Document.of_text "";
    run_sized doc
}

/// Open `path`: read it, derive the language from its extension, and
/// run. A read failure is the exit path.
def open_file (path : String) : IO I64 := do {
    let r <- IO.read_file (Path.path path);
    match r {
        Result.err e => read_failed path e,
        Result.ok text => do {
            let doc : Document := opened_doc path text;
            run_sized doc
        }
    }
}

/// The read failure: one stderr line, exit 1. `StreamError.message` is the
/// OS text, so the user sees "No such file or directory" rather than a
/// kind code they would have to look up.
def read_failed (path : String) (e : StreamError) : IO I64 := do {
    IO.write_stderr ("ply: " ++ path ++ ": " ++ e.message ++ "\n");
    return 1
}

/// The document an opened file becomes: its text, its path, and the
/// language its extension names.
///
/// Built through THREE annotated locals rather than one expression: a
/// struct-update expression in argument position is the two-host
/// inference hazard, and `Document.of_text` is the one constructor for a
/// `Document`'s field list (the plan's Phase 1 note).
pub def opened_doc (path : String) (text : String) : Document :=
    let base : Document := Document.of_text text in
    let named : Document := Document.with_path base path in
    Document.with_language named (language_for_path path)

/// The language name `Document.language` carries, from the file's
/// extension: `monad` for `.mo`, `text` (the no-highlight default) for
/// everything else. Phase 3's `Highlight.config_for` takes the same
/// names, and "text" is its fallback too -- an editor must open any file,
/// not only the ones it can color.
///
/// Matched case-sensitively: `.MO` is not `.mo` anywhere else in this
/// corpus, and guessing would only make the highlighter's table wrong in
/// a way nothing reports.
///
/// ARGUMENT ORDER: `String.ends_with` takes the STRING first and the
/// suffix second (`std`'s other user, `acorn::passes`, reads
/// `ends_with path ".md"`). That is the opposite of `String.starts_with`,
/// which takes the prefix first -- the pair is an easy one to write
/// backwards, and backwards here is silently always-false.
pub def language_for_path (path : String) : String :=
    if String.ends_with path ".mo" then "monad" else "text"

// ── The run ──────────────────────────────────────────────────────────────

/// Size the editor from the terminal and run it. The size is DESTRUCTURED
/// once: `Pair` is not `Copy`, so reading it twice through two accessors
/// would spend the affine budget twice.
def run_sized (doc : Document) : IO I64 := do {
    let size <- Terminal.size;
    match size {
        Pair.pair rows cols => run_editor (EditorState.init doc rows cols)
    }
}

/// Hand the state to the loop. `tick_ms` is NEGATIVE: the editor is
/// input-driven, so the loop blocks until a key (or EOF) instead of
/// waking ten times a second to redraw nothing.
///
/// A piped run therefore terminates at EOF, and the loop's EOF path folds
/// the batch it already read (`tui.mo`'s `final_frame`) -- which is what
/// makes a scripted `Space w` really write before the process exits.
def run_editor (st : EditorState) : IO I64 := do {
    let app : App EditorState EditorMsg := ply_app st;
    let _ <- run_app app;
    return 0
}

def ply_app (st : EditorState) : App EditorState EditorMsg :=
    App.app st on_event update View.view ply_no_ticks

/// `App.tick_ms`: no frame clock. A negative timeout blocks until input
/// (poll(2)'s own convention), which is exactly what an editor wants.
def ply_no_ticks : I64 := 0 - 1

// ── Tests ────────────────────────────────────────────────────────────────
//
// A `main`-bearing file is safe in the test sweep: the driver renames the
// program's own `main` out of the way (`codegen/src/test_driver.mo`'s
// `rename_user_main`), so these run and the entry point never does.
//
// The extension table is the one piece of this file that is a DECISION
// rather than glue, so it is pinned here. The rest (argv, the read, the
// loop) is covered by the e2e fixture, which runs the real binary.

#[test]
def test_monad_extension_is_monad : Bool :=
    String.beq (language_for_path "motes/ply/src/main.mo") "monad"

#[test]
def test_other_extensions_are_text : Bool :=
    String.beq (language_for_path "README.md") "text"
        && String.beq (language_for_path "notes") "text"

/// `.mo` must be the EXTENSION, not a substring: a file named `demo`
/// (whose name merely ends in those letters) is not Monad source, and
/// neither is a bare `mo` (an extension needs its dot).
#[test]
def test_extension_must_be_the_suffix : Bool :=
    String.beq (language_for_path "demo") "text"
        && String.beq (language_for_path "/tmp/mo") "text"
        && String.beq (language_for_path "/tmp/a.mo") "monad"

/// The opened document carries the path it came from -- what `Space w`
/// writes to and what the status line shows.
#[test]
def test_opened_doc_keeps_its_path : Bool :=
    match Document.path_of (opened_doc "/tmp/a.mo" "x") {
        Option.some p => String.beq p "/tmp/a.mo",
        Option.none => false
    }
