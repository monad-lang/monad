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

pub def Shell.file_exists (path : Path) : IO Bool :=
    IO.file_exists path

pub def Shell.is_dir (path : Path) : IO Bool :=
    IO.is_dir path

pub def Shell.list_dir (path : Path) : IO (List String) := do {
    let entries <- IO.list_dir path;
    return (List.map (fn (p : Path) => Path.file_name p) entries)
}

pub def Shell.read_file (path : Path) : IO (Result String String) := do {
    let r <- IO.read_file path;
    match r {
        Result.ok s => return (Result.ok s),
        Result.err _ => return (Result.err ("failed to read " ++ Path.to_string path)),
    }
}

pub def Shell.write_file (path : Path) (content : String) : IO (Result String Unit) := do {
    let r <- IO.write_file path content;
    match r {
        Result.ok _ => return (Result.ok unit),
        Result.err _ => return (Result.err ("failed to write " ++ Path.to_string path)),
    }
}

pub def Shell.mkdir_p (path : Path) : IO I64 :=
    Shell.run "mkdir" ["-p", Path.to_string path]

pub def Shell.rm_rf (path : Path) : IO I64 :=
    Shell.run "rm" ["-rf", Path.to_string path]

pub def Shell.ln_sfn (target : Path) (link : Path) : IO I64 :=
    Shell.run "ln" ["-sfn", Path.to_string target, Path.to_string link]

pub def Shell.chmod_x (path : Path) : IO I64 :=
    Shell.run "chmod" ["+x", Path.to_string path]

pub def Shell.mv (from : Path) (to : Path) : IO I64 :=
    Shell.run "mv" ["-f", Path.to_string from, Path.to_string to]

pub def Shell.cp (from : Path) (to : Path) : IO I64 :=
    Shell.run "cp" ["-f", Path.to_string from, Path.to_string to]

pub def Shell.untar (archive : Path) (dest : Path) : IO I64 :=
    Shell.run "tar" ["-xzf", Path.to_string archive, "-C", Path.to_string dest]

/// The token a GitHub fetch authenticates with, if any.
/// `MONADUP_GITHUB_TOKEN` wins over `GITHUB_TOKEN` and `GH_TOKEN`, so a CI
/// run can use its own token without disturbing a developer's `gh` login.
///
/// GitHub throttles UNAUTHENTICATED release downloads hard enough to answer
/// HTTP 504 for hours (measured 2026-11-08: every nightly asset 504s bare
/// and 200s with a token), which is what made `monadup default` fail for
/// users who had a perfectly good token sitting in their environment.
pub def Shell.github_token : IO (Option String) := do {
    let a <- IO.get_env "MONADUP_GITHUB_TOKEN";
    match a {
        Option.some t => return (Option.some t),
        Option.none => do {
            let b <- IO.get_env "GITHUB_TOKEN";
            match b {
                Option.some t => return (Option.some t),
                Option.none => do {
                    let c <- IO.get_env "GH_TOKEN";
                    match c {
                        Option.some t => return (Option.some t),
                        Option.none => Shell.gh_auth_token,
                    }
                },
            }
        },
    }
}

/// The token the `gh` CLI is logged in with, if any.
///
/// Last resort behind the environment variables: a developer who ran
/// `gh auth login` should not have to export their token for `monadup` to
/// get an authenticated download. Absent `gh`, a logged-out one, or any
/// other failure is simply `none` -- never an error, because plenty of
/// machines have no `gh` at all and still install fine unauthenticated.
def Shell.gh_auth_token : IO (Option String) := do {
    let r <- Shell.capture "sh" ["-c", "command -v gh >/dev/null 2>&1 && gh auth token 2>/dev/null || true"];
    match r {
        Pair.pair code out =>
            if Bool.not (I64.beq code 0) then return Option.none
            else
                let t : String := Text.trim out in
                if I64.beq (String.length t) 0
                then return Option.none
                else return (Option.some t),
    }
}

/// `-H "Authorization: ..."` when a token is set, nothing otherwise. The
/// header is only meaningful for github.com URLs, so it is added to the
/// release fetches and the API query, not to every `curl` in the tool.
pub def Shell.github_auth_args : IO (List String) := do {
    let t <- Shell.github_token;
    match t {
        Option.none => IO.pure List.empty,
        Option.some tok => IO.pure ["-H", String.concat "Authorization: Bearer " tok],
    }
}

pub def Shell.curl_download_auth (url : String) (dest : Path) : IO I64 := do {
    let auth <- Shell.github_auth_args;
    Shell.run "curl" (List.append auth ["-fsSL", "-o", Path.to_string dest, url])
}

pub def Shell.curl_download (url : String) (dest : Path) : IO I64 :=
    Shell.run "curl" ["-fsSL", "-o", Path.to_string dest, url]

pub def Shell.curl_fetch (url : String) : IO (Pair I64 String) :=
    Shell.capture "curl" ["-fsSL", url]

pub def Shell.curl_fetch_auth (url : String) : IO (Pair I64 String) := do {
    let auth <- Shell.github_auth_args;
    Shell.capture "curl" (List.append auth ["-fsSL", url])
}

pub def Shell.curl_head (url : String) : IO I64 := do {
    let r <- Shell.capture "curl" ["-fsSI", "--max-time", "5", url];
    match r {
        Pair.pair code _ => return code,
    }
}

/// `test -x path`, the executable bit check the bash script used.
pub def Shell.is_executable (path : Path) : IO Bool := do {
    let r <- Shell.capture "test" ["-x", Path.to_string path];
    match r {
        Pair.pair code _ => return (I64.beq code 0),
    }
}

/// `test -w path`.
pub def Shell.is_writable (path : Path) : IO Bool := do {
    let r <- Shell.capture "test" ["-w", Path.to_string path];
    match r {
        Pair.pair code _ => return (I64.beq code 0),
    }
}

/// `test -L path` -- unlike `readlink`, this distinguishes a regular file
/// from a symlink.
pub def Shell.is_symlink (path : Path) : IO Bool := do {
    let r <- Shell.capture "test" ["-L", Path.to_string path];
    match r {
        Pair.pair code _ => return (I64.beq code 0),
    }
}

pub def Shell.readlink (path : Path) : IO (Option Path) := do {
    let r <- Shell.capture "readlink" [Path.to_string path];
    match r {
        Pair.pair code out =>
            let s : String := Text.trim out in
            if I64.beq code 0 && Bool.not (String.is_empty s)
            then return (Option.some (Path.path s))
            else return Option.none,
    }
}

/// A tool is present when `sh -c 'command -v -- "$1"'` finds it. The
/// command is a fixed string and the tool name is passed as `$1`, never
/// interpolated. This matches the bash implementation's `command -v`;
/// probing with `--version` misreports tools that do not accept it (some
/// BusyBox `tar` builds error on `--version`).
pub def Shell.tool_exists (cmd : String) : IO Bool := do {
    let r <- Shell.capture "sh" ["-c", "command -v -- \"$1\" >/dev/null 2>&1", "sh", cmd];
    match r {
        Pair.pair code _ => return (I64.beq code 0),
    }
}

pub def Shell.uname_sm : IO (Option String) := do {
    let override <- IO.get_env "MONADUP_UNAME";
    match override {
        Option.some s =>
            let t : String := Text.trim s in
            if String.is_empty t
            then Shell.uname_from_process
            else return (Option.some t),
        Option.none => Shell.uname_from_process,
    }
}

def Shell.uname_from_process : IO (Option String) := do {
    let r <- Proc.capture "uname" ["-sm"];
    match r {
        Pair.pair code out =>
            let t : String := Text.trim out in
            if I64.beq code 0 && Bool.not (String.is_empty t)
            then return (Option.some t)
            else return Option.none,
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

/// The running binary's absolute path. The bootstrap stub sets
/// `MONADUP_SELF_BIN` to the file it downloaded and executed -- the only
/// way `self-install` can find the binary on a platform without procfs
/// (Darwin). Fall back to `/proc/<pid>/exe` where it exists.
pub def Shell.self_exe_path : IO (Option Path) := do {
    let seeded <- IO.get_env "MONADUP_SELF_BIN";
    match seeded {
        Option.some raw =>
            let t : String := Text.trim raw in
            if String.is_empty t then Shell.self_exe_from_proc else return (Option.some (Path.path t)),
        Option.none => Shell.self_exe_from_proc,
    }
}

def Shell.self_exe_from_proc : IO (Option Path) := do {
    let p : Path := Path.path ("/proc/" ++ I64.to_string process_id ++ "/exe");
    let r <- Proc.capture "readlink" ["-f", Path.to_string p];
    match r {
        Pair.pair code out =>
            let s : String := Text.trim out in
            if I64.beq code 0 && Bool.not (String.is_empty s)
            then return (Option.some (Path.path s))
            else return Option.none,
    }
}

/// Hex SHA-256 of a file, via `sha256sum` or `shasum -a 256` (whichever
/// is present). `none` when neither is.
pub def Shell.sha256 (path : Path) : IO (Option String) := do {
    let line <- Shell.capture_line "sha256sum" [Path.to_string path];
    match line {
        Option.some l => return (Option.some (Text.first_word l)),
        Option.none => do {
            let alt <- Shell.capture_line "shasum" ["-a", "256", Path.to_string path];
            match alt {
                Option.some l => return (Option.some (Text.first_word l)),
                Option.none => return Option.none,
            }
        },
    }
}

/// Remove the bootstrap stub's downloaded copy once the command has run.
/// `self-install` consults `MONADUP_SELF_BIN` during dispatch (the only
/// way to copy the running binary where `/proc` is absent), so this must
/// happen after `Cli.run`.
pub def Shell.remove_self_bin : IO Unit := do {
    let seeded <- IO.get_env "MONADUP_SELF_BIN";
    match seeded {
        Option.none => return unit,
        Option.some raw =>
            let t : String := Text.trim raw in
            if String.is_empty t then return unit
            else do {
                let _ <- Shell.rm_rf (Path.path t);
                return unit
            },
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

pub def Shell.path_has (dir : Path) : IO Bool := do {
    let p <- IO.get_env "PATH";
    match p {
        Option.none => return false,
        Option.some raw =>
            return (Shell.path_has_loop (Layout.drop_trailing_slash (Path.to_string dir)) (Text.split_on ":" raw)),
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
