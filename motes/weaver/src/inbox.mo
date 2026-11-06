/// The turn's inbox: notes the UI posts while a turn runs (a background
/// task exited) and the turn takes at its next tool boundary
/// (`RunState.inbox`), or the next submit takes when no boundary came.
/// One note per line, in a file beside `stop.txt`.
use std::path {Path, Path.to_string}
use std::io {IO.read_file, IO.file_exists}
use std::process {exec_cmd, process_id}
use std::list {List.filter, List.intercalate}
use weaver::theme {theme_split_lines}
use weaver::store {StoreState, Store.child}

pub def Inbox.path (store : Option StoreState) : Path :=
    match store {
        Option.some s => Store.child s.dir "inbox.txt",
        Option.none =>
            Path.path (String.concat "/tmp/weaver-inbox-"
                (String.concat (I64.to_string process_id) ".txt")),
    }

/// Append the notes, one line each (a note's own newlines become spaces).
#[partial]
pub def Inbox.post (store : Option StoreState) (notes : List String) : IO Unit :=
    match notes {
        List.empty => IO.pure unit,
        List.cons n rest => do {
            let _ <- exec_cmd "sh" ["-c", "printf '%s\\n' \"$1\" >> \"$2\"", "sh",
                List.intercalate " " (theme_split_lines n), Path.to_string (Inbox.path store)];
            Inbox.post store rest
        },
    }

/// Every note posted so far, emptying the inbox. The file is moved aside
/// before it is read, so a note posted meanwhile lands in a fresh file.
pub def Inbox.take (store : Option StoreState) : IO (List String) := do {
    let path : Path := Inbox.path store;
    let there <- IO.file_exists path;
    if Bool.not there then IO.pure List.empty
    else do {
        let taking : String := String.concat (Path.to_string path) ".taking";
        let _ <- exec_cmd "mv" [Path.to_string path, taking];
        let r <- IO.read_file (Path.path taking);
        let _ <- exec_cmd "rm" ["-f", taking];
        IO.pure (match r {
            Result.err _ => List.empty,
            Result.ok text => List.filter (fn (l : String) => Bool.not (String.is_empty l)) (theme_split_lines text),
        })
    }
}

/// The seam `RunState.inbox` takes.
pub def Inbox.seam (store : Option StoreState) : Unit -> IO (List String) :=
    fn (_ : Unit) => Inbox.take store

/// `text` with `notes` after it, as one user message: the notes ride the
/// next typed line (task exits, instruction-file changes).
pub def Inbox.with_notes (notes : List String) (text : String) : String :=
    if List.is_empty notes then text
    else String.concat text (String.concat "\n\n" (List.intercalate "\n" notes))
