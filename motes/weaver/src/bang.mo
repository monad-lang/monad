/// `! cmd`: the user's own shell line. It runs through the `shell` tool's
/// machinery (process group, log, tail, Ctrl+B-free budget) with no gate --
/// the user typed it -- shows its output in the transcript, and leaves a
/// note that rides the next model message, so the model sees what the user
/// saw without paying for it until then.
use shuttle::message_types {Content}
use shuttle::context {Context.cap_text}
use json::json {Json, Json.make_object, Json.make_str, Json.make_num_int}
use std::map {Map, BTreeMap}
use std::path {Path, Path.with_suffix}
use weaver::procs {Procs.root}
use weaver::shell_tool {ShellEnv, WeaverShell.run, WeaverShell.fg_path, WeaverShell.never_stop, WeaverShell.max_wait}
use weaver::store {StoreState, Store.scratch_of}

/// The command of a `!` line, trimmed; `some ""` for a bare `!` (the
/// caller shows usage). None for any other line.
pub def Bang.command (text : String) : Option String :=
    if String.starts_with "!" text then Option.some (String.trim (String.drop 1 text))
    else Option.none

/// The most of one command's output the model is sent.
pub def Bang.note_bytes : I64 := 8192

/// The note the next model message carries.
pub def Bang.note (command : String) (output : String) : String :=
    String.concat_list ["[the user ran a shell command]\n$ ", command, "\n", Context.cap_text output Bang.note_bytes]

pub def Bang.usage : String := "usage: ! <shell command> -- runs it now; the output joins your next message"

/// Its own foreground marker beside the shell tool's, so a `!` beside a
/// turn never answers the turn's Ctrl+B or live-tail reads.
def fg_path (store : Option StoreState) : Path :=
    Path.with_suffix (WeaverShell.fg_path store) ".bang"

def args_of (command : String) : Json :=
    Json.make_object (Map.insert "wait_seconds" (Json.make_num_int WeaverShell.max_wait)
        (Map.insert "command" (Json.make_str command) BTreeMap.empty))

def text_of (c : Content) : String :=
    match c {
        Content.tool_result _ output _ => output,
        Content.text s => s,
        _ => "",
    }

/// Run the command to completion (or the shell's 300 s budget, after which
/// it stays a task) and answer its shown output.
pub def Bang.run (store : Option StoreState) (command : String) : IO String := do {
    let root <- Procs.root;
    let env : ShellEnv := { root := root, fg := fg_path store, stop := WeaverShell.never_stop, log := Option.none,
        budget_ms := 0, scratch := Store.scratch_of store };
    let c <- WeaverShell.run env "bang" (args_of command);
    IO.pure (text_of c)
}
