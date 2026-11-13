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

use lib::model {Document, Document.of_text, Document.of_file,
    Document.language_for_path, EditorState, EditorState.init, EditorState.with_bindings,
    EditorState.with_status, EditorMsg, on_event}
use lib::commands {update}
use lib::view {View.view}
use lib::config {Config, Config.empty, Config.parse, Config.merge, Config.bindings_of_all,
    Config.problems_of_all}
use std::path {Path}
use lib::keymap {Binding, Keymap.default_bindings}
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

/// The document an opened file becomes. DELEGATES to `model.mo`'s
/// `Document.of_file`, because `:e <path>` (Phase 5) opens files too and the
/// two paths must build the same document for one file -- the argv path
/// exiting on a read failure and the `:e` path reporting it is the only
/// difference between them.
pub def opened_doc (path : String) (text : String) : Document :=
    Document.of_file path text

/// The language name — `model.mo` owns it, so the binary and the command
/// line cannot disagree about how a file highlights.
pub def language_for_path (path : String) : String :=
    Document.language_for_path path

// ── The run ──────────────────────────────────────────────────────────────

/// Size the editor from the terminal and run it. The size is DESTRUCTURED
/// once: `Pair` is not `Copy`, so reading it twice through two accessors
/// would spend the affine budget twice.
///
/// THE CONFIG IS READ HERE, after the size, so a `ply.toml` that cannot be
/// read reports on a status line the user can see (`run_editor` paints one
/// in the first frame) rather than on a terminal that has not started.
def run_sized (doc : Document) : IO I64 := do {
    let size <- Terminal.size;
    match size {
        Pair.pair rows cols => do {
            let base : EditorState := EditorState.init doc rows cols;
            let configured <- apply_config base;
            run_editor configured
        }
    }
}

// ── ply.toml (Phase 5) ────────────────────────────────────────────────────
//
// TWO LAYERS, GLOBAL THEN PROJECT, and the merge is the keymap's LAST-match
// rule over appended rows (`Config.merge`, which says so). The DEFAULTS are
// the first layer, so a `ply.toml` rebinds a key without having to restate
// the whole table.
//
// A MISSING FILE IS NOT AN ERROR and not a problem line: most users have no
// `ply.toml`, and reporting "no such file" on every start would train them to
// ignore the status line. A file that EXISTS but cannot be parsed or names a
// key this editor does not have IS reported -- those are mistakes, and the
// message names the row.

/// The global config's path: `$XDG_CONFIG_HOME/ply/ply.toml`, falling back to
/// `$HOME/.config/ply/ply.toml`. `none` when neither variable is set, which
/// is a headless environment, not an error.
def global_config_path : IO (Option String) := do {
    let xdg <- IO.get_env "XDG_CONFIG_HOME";
    let home <- IO.get_env "HOME";
    return (global_config_from xdg home)
}

/// The global path from the two environment readings.
def global_config_from (xdg : Option String) (home : Option String) : Option String :=
    match xdg {
        Option.some dir => ply_nonempty_dir dir "XDG_CONFIG_HOME",
        Option.none =>
            match home {
                Option.some dir => ply_nonempty_dir dir "HOME",
                Option.none => Option.none
            }
    }

/// `<dir>/.config/ply/ply.toml` for `HOME`, `<dir>/ply/ply.toml` for an XDG
/// root -- i.e. the XDG rule applied once. An empty variable is treated as
/// unset: `HOME=` is a real (if broken) environment, and joining onto it would
/// give a path rooted at the cwd.
def ply_nonempty_dir (dir : String) (var : String) : Option String :=
    if String.is_empty dir
    then Option.none
    else if String.beq var "XDG_CONFIG_HOME"
    then Option.some (String.concat dir "/ply/ply.toml")
    else Option.some (String.concat dir "/.config/ply/ply.toml")

/// The project config's path: `ply.toml` in the process's cwd. One fixed
/// name, not a search up the tree -- a project config that a parent directory
/// supplies is a surprise, and the plan asks for "global, then project".
def project_config_path : String := "ply.toml"

/// Read and apply the config layers to `st`: the global file, then the
/// project file, then report every problem line the two produced.
///
/// THE BINDING TABLE IS COMPOSED ONCE, here: defaults first, then each
/// layer's rows (`Config.bindings_of_all`), because the keymap keeps the LAST
/// match and the layers are appended in precedence order.
def apply_config (st : EditorState) : IO EditorState := do {
    let global_path <- global_config_path;
    let global <- read_config_at global_path "ply.toml";
    let project <- read_config_at (Option.some project_config_path) project_config_path;
    // The layer list is read twice (its rows, its problems), so one
    // `Shared` handle serves both -- the affine rule's own remedy.
    let layers : Shared (List Config) :=
        Shared.of (List.cons global (List.cons project List.empty));
    let bindings : List Binding :=
        List.append Keymap.default_bindings (Config.bindings_of_all (Shared.get layers));
    let table : EditorState := EditorState.with_bindings st bindings;
    return (report_config table (Config.problems_of_all (Shared.get layers)))
}

/// Read one config file. A path of `none` (no global config location) or a
/// MISSING file answers the empty config; a file that will not read answers
/// one problem line, because the user wrote it and expects it to work.
def read_config_at (path : Option String) (label : String) : IO Config :=
    match path {
        Option.none => read_config_nothing,
        Option.some p => read_config_file p label
    }

/// The `none` path's answer: no global config location, so no config.
///
/// A NAMED DEF rather than `return Config.empty` inline: a `return` as a bare
/// `match` arm inside a `do` body is the shape the self-hosted loader refuses.
def read_config_nothing : IO Config := do {
    return Config.empty
}

/// One config file: the empty config when it does not exist (most users have
/// no `ply.toml`), the parsed config when it does, one problem line when it
/// exists but will not read.
def read_config_file (p : String) (label : String) : IO Config := do {
    let exists <- IO.file_exists (Path.path p);
    if exists
    then read_config_existing p label
    else read_config_nothing
}

/// The existing-file case.
def read_config_existing (p : String) (label : String) : IO Config := do {
    let r <- IO.read_file (Path.path p);
    match r {
        Result.ok text => return Config.parse text label,
        Result.err e => return config_read_problem p e
    }
}

/// The config for a file that exists but will not read: one problem line.
///
/// Built as a parsed empty config plus a problem line, so `Config`'s field
/// list stays in one module -- a struct literal here would be the two-host
/// literal hazard.
def config_read_problem (path : String) (e : StreamError) : Config :=
    Config.parse (String.concat "# " (String.concat path (String.concat ": " e.message))) label_problem

/// The label `config_read_problem` reports under.
def label_problem : String := "ply.toml"

/// Put the first config problem on the status line, or leave the state alone
/// when there were none.
///
/// ONE LINE, NOT A LIST: the status line is one row, and a config with three
/// bad rows would otherwise scroll the terminal. The first problem is the one
/// to fix; the rest are the same fix repeated.
def report_config (st : EditorState) (problems : List String) : EditorState :=
    match problems {
        List.empty => st,
        List.cons first _ => EditorState.with_status st ("config: " ++ first)
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
