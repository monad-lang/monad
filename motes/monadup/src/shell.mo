/// The IO boundary: every external process monadup runs.
///
/// All calls use argv (`exec_cmd`/`Proc.capture`), never `sh -c` with a
/// manifest- or user-derived string. `uname`, `curl`, `tar`, `readlink`,
/// `test`, `mkdir`, `rm`, `ln`, `chmod`, `mv` and `cp` are the commands the
/// bash implementation already required.
use std::process {Proc.capture, exec_cmd, process_id}
use std::io {IO.get_env}
use lib::text {*}
use lib::layout {*}

pub def Shell.run (cmd : String) (args : List String) : IO I64 :=
    exec_cmd cmd args

pub def Shell.capture (cmd : String) (args : List String) : IO (Pair I64 String) :=
    Proc.capture cmd args

pub def Shell.file_exists (path : String) : IO Bool :=
    IO.file_exists (Path.path path)

pub def Shell.is_dir (path : String) : IO Bool :=
    IO.is_dir (Path.path path)

pub def Shell.list_dir (path : String) : IO (List String) :=
    IO.list_dir (Path.path path)

pub def Shell.read_file (path : String) : IO String :=
    IO.read_file (Path.path path)

pub def Shell.write_file (path : String) (content : String) : IO Unit :=
    IO.write_file (Path.path path) content

pub def Shell.mkdir_p (path : String) : IO I64 :=
    Shell.run "mkdir" ["-p", path]

pub def Shell.rm_rf (path : String) : IO I64 :=
    Shell.run "rm" ["-rf", path]

pub def Shell.ln_sfn (target : String) (link : String) : IO I64 :=
    Shell.run "ln" ["-sfn", target, link]

pub def Shell.chmod_x (path : String) : IO I64 :=
    Shell.run "chmod" ["+x", path]

pub def Shell.mv (from : String) (to : String) : IO I64 :=
    Shell.run "mv" ["-f", from, to]

pub def Shell.cp (from : String) (to : String) : IO I64 :=
    Shell.run "cp" ["-f", from, to]

pub def Shell.untar (archive : String) (dest : String) : IO I64 :=
    Shell.run "tar" ["-xzf", archive, "-C", dest]

pub def Shell.curl_download (url : String) (dest : String) : IO I64 :=
    Shell.run "curl" ["-fsSL", "-o", dest, url]

pub def Shell.curl_fetch (url : String) : IO (Pair I64 String) :=
    Shell.capture "curl" ["-fsSL", url]

pub def Shell.curl_head (url : String) : IO I64 := do {
    let r <- Shell.capture "curl" ["-fsSI", "--max-time", "5", url];
    match r {
        Pair.pair code _ => return code,
    }
}

/// `test -x path`, the executable bit check the bash script used.
pub def Shell.is_executable (path : String) : IO Bool := do {
    let r <- Shell.capture "test" ["-x", path];
    match r {
        Pair.pair code _ => return (I64.beq code 0),
    }
}

pub def Shell.readlink (path : String) : IO (Option String) := do {
    let r <- Shell.capture "readlink" [path];
    match r {
        Pair.pair code out =>
            let s : String := Text.trim out in
            if I64.beq code 0 && Bool.not (String.is_empty s)
            then return (Option.some s)
            else return Option.none,
    }
}

/// A tool is present when running it with `--version` succeeds. No
/// `which`/`command -v` dependency and no shell.
pub def Shell.tool_exists (cmd : String) : IO Bool := do {
    let r <- Shell.capture cmd ["--version"];
    match r {
        Pair.pair code _ => return (I64.beq code 0),
    }
}

pub def Shell.uname_sm : IO String := do {
    let override <- IO.get_env "MONADUP_UNAME";
    match override {
        Option.some s =>
            let t : String := Text.trim s in
            if String.is_empty t
            then Shell.uname_from_process
            else return t,
        Option.none => Shell.uname_from_process,
    }
}

def Shell.uname_from_process : IO String := do {
    let r <- Proc.capture "uname" ["-sm"];
    match r {
        Pair.pair _ out => return (Text.trim out),
    }
}

pub def Shell.home_env : IO (Option String) :=
    IO.get_env "HOME"

pub def Shell.monad_home_env : IO (Option String) :=
    IO.get_env "MONAD_HOME"

pub def Shell.api_url : IO String := do {
    let env <- IO.get_env "MONADUP_API_URL";
    match env {
        Option.some s =>
            let t : String := Text.trim s in
            if String.is_empty t
            then return "https://api.github.com/repos/monad-lang/monad/releases"
            else return t,
        Option.none => return "https://api.github.com/repos/monad-lang/monad/releases",
    }
}

/// The running binary's absolute path, or `none` where procfs is absent
/// (Darwin). Used by `self-install` before falling back to a download.
pub def Shell.self_exe_path : IO (Option String) := do {
    let p : String := String.concat "/proc/" (String.concat (I64.to_string process_id) "/exe");
    let r <- Proc.capture "readlink" ["-f", p];
    match r {
        Pair.pair code out =>
            let s : String := Text.trim out in
            if I64.beq code 0 && Bool.not (String.is_empty s)
            then return (Option.some s)
            else return Option.none,
    }
}

#[partial]
def Shell.path_has_loop (dir : String) (entries : List String) : Bool :=
    match entries {
        List.empty => false,
        List.cons e rest =>
            if String.beq (Layout.drop_trailing_slash e) dir
            then true
            else Shell.path_has_loop dir rest,
    }

pub def Shell.path_has (dir : String) : IO Bool := do {
    let p <- IO.get_env "PATH";
    match p {
        Option.none => return false,
        Option.some raw => return (Shell.path_has_loop (Layout.drop_trailing_slash dir) (Text.split_on ":" raw)),
    }
}

/// First line of a capture, trimmed; `none` when the command failed or
/// printed nothing.
pub def Shell.capture_line (cmd : String) (args : List String) : IO (Option String) := do {
    let r <- Proc.capture cmd args;
    match r {
        Pair.pair code out =>
            let first : String := Text.trim out in
            if I64.beq code 0 && Bool.not (String.is_empty first)
            then return (Option.some first)
            else return Option.none,
    }
}
