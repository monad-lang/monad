/// `grep`/`glob` over a capped, killable pipe.
///
/// `Proc.capture` redirected the WHOLE output to a temp file and read it
/// back: `glob /` on a large filesystem took 197 s and could exhaust
/// memory before the tool ever saw a cap. This streams line by line over
/// `Proc.spawn`/`Proc.read_line`, so a flood stops at `search_max_lines`
/// or `search_max_bytes` and the child is killed. The command runs under
/// GNU `timeout`, which also owns the process group (a detached child
/// cannot outlive it).
///
/// Arguments are passed as POSITIONAL PARAMETERS ($1/$2) to `sh -c`, not
/// interpolated into the script, so a pattern or path with quotes/spaces
/// cannot turn into shell syntax.
use init::transformers {ResultT}
use shuttle::message_types {Content}
use shuttle::tools::search_args {GrepArgs, GlobArgs}
use json::json {Json}
use std::process {Child, Proc.spawn, Proc.read_line, Proc.wait}
use std::concurrent::fiber {forkIO}
use std::stream {StreamError}

def tool_err (id : String) (msg : String) : Content := Content.tool_result id msg true
def tool_ok (id : String) (msg : String) : Content := Content.tool_result id msg false

pub def search_max_lines : I64 := 200
pub def search_max_bytes : I64 := 32768
def search_timeout_s : I64 := 30
def search_kill_after_s : I64 := 5

def search_timeout_marker : String := "\n[search timed out after 30 s; command killed]\n"
def search_line_marker : String := "\n[output truncated at "
def search_byte_marker : String := "\n[output truncated at "

/// Spawn `timeout -k 5 30 sh -c SCRIPT sh A1 A2 A3` (A1/A2/A3 are
/// `$1`/`$2`/`$3`; grep leaves A3 empty).
def search_spawn (id : String) (script : String) (a1 : String) (a2 : String) (a3 : String) : IO Content := do {
    let kill_after : String := (I64.to_string search_kill_after_s) ++ "s";
    let limit : String := (I64.to_string search_timeout_s) ++ "s";
    let spawned <- Proc.spawn "timeout" ["-k", kill_after, limit, "sh", "-c", script, "sh", a1, a2, a3];
    match spawned {
        Result.err e => IO.pure (tool_err id (String.concat "search: could not spawn timeout: " e.message)),
        Result.ok child => search_read id child 0 "",
    }
}

#[partial]
def search_read (id : String) (c : Child) (count : I64) (acc : String) : IO Content := do {
    let ln <- Proc.read_line c;
    match ln {
        Result.err e => search_read_err id c e,
        Result.ok opt => search_got_line id c count acc opt,
    }
}

/// `timeout` owns the command's process group; kill it only through its
/// own deadline. Reap it on a fiber so no child slot leaks.
def search_reap_later (c : Child) : IO Unit := do {
    let _fiber <- forkIO (fn (_ : Unit) => do { let _ <- Proc.wait c; IO.pure unit });
    IO.pure unit
}

def search_read_err (id : String) (c : Child) (e : StreamError) : IO Content := do {
    search_reap_later c;
    IO.pure (tool_err id (String.concat "search: read failed: " e.message))
}

#[partial]
def search_got_line (id : String) (c : Child) (count : I64) (acc : String) (opt : Option String) : IO Content :=
    match opt {
        Option.none => search_eof id c acc,
        Option.some s =>
            if Bool.not (I64.lt count search_max_lines)
            then search_truncate_lines id c acc
            else search_grow id c count acc s,
    }

#[partial]
def search_grow (id : String) (c : Child) (count : I64) (acc : String) (s : String) : IO Content :=
    let grown : String := acc ++ s ++ "\n" in
    if Bool.not (I64.lt (String.length grown) search_max_bytes)
    then search_truncate_bytes id c grown
    else search_read id c (count + 1) grown

/// The command's end. Matches are success; so is "no match" (grep's
/// rc 1 with no output), which used to come back as an empty tool ERROR.
/// Another rc with output keeps the output (an unreadable file among
/// matches) as a result; with none it is an error.
def search_eof (id : String) (c : Child) (acc : String) : IO Content := do {
    let code <- Proc.wait c;
    IO.pure (search_outcome id code acc)
}

pub def search_outcome (id : String) (code : I64) (acc : String) : Content :=
    if code == 124 then tool_err id (acc ++ search_timeout_marker)
    else if String.is_empty (String.trim acc)
    then (if Bool.or (code == 0) (code == 1) then tool_ok id "no matches" else tool_err id (String.concat "search failed (exit " (String.concat (I64.to_string code) ")")))
    else tool_ok id acc

/// A truncated result is still a result: the marker says what was cut.
def search_truncate_lines (id : String) (c : Child) (acc : String) : IO Content := do {
    search_reap_later c;
    IO.pure (tool_ok id (acc ++ search_line_marker ++ I64.to_string search_max_lines ++ " lines; output truncated]\n"))
}

def search_truncate_bytes (id : String) (c : Child) (acc : String) : IO Content := do {
    search_reap_later c;
    IO.pure (tool_ok id (acc ++ search_byte_marker ++ I64.to_string search_max_bytes ++ " bytes; output truncated]\n"))
}

/// Inside a git work tree, `git grep` (tracked and untracked files,
/// `.gitignore` respected, binaries skipped); elsewhere, or for a path git
/// rejects (rc > 1), plain `grep -rnI` with the usual build directories
/// pruned (`target*` covers `target-rust/` and `target-monad/`).
pub def grep_script : String :=
    String.concat_list [
        "exec 2>&1; ",
        "git grep -n -I --untracked --exclude-standard -e \"$1\" -- \"$2\" 2>/dev/null; rc=$?; ",
        "[ $rc -le 1 ] && exit $rc; ",
        "exec grep -rnI --exclude-dir=.git --exclude-dir='target*' --exclude-dir=node_modules --exclude-dir=build -- \"$1\" \"$2\""
    ]

/// Inside a git work tree, the tracked and untracked (not ignored) files
/// whose base name matches `$1`; elsewhere `find` with the build
/// directories pruned.
///
/// SYMLINKS. `$3` = 1 turns on `find -L` (the `follow_links` argument,
/// default true); `$3` = 0 keeps the old `-P` walk. Following is bounded
/// three ways because a link can point at its own ancestor: `-maxdepth`
/// (`WEAVER_GLOB_MAXDEPTH`, default 24) caps the walk, GNU find detects a
/// loop and skips it, and the 30 s `timeout` plus the line/byte caps stop
/// a pathological tree. Inside a work tree `git ls-files` lists a
/// symlinked directory as one entry and never descends, so a directory
/// entry is walked explicitly with the same bounded `find -L`; the whole
/// stream is deduped because a link's target may also be listed by path.
///
/// The walker is shell, not Monad code: `std` cannot tell a link from its
/// target (`IO.is_dir` uses `stat`) and has no realpath, and `find -L`
/// already implements the bound.
pub def glob_script : String :=
    String.concat_list [
        "exec 2>&1; ",
        "follow=''; if [ \"$3\" = 1 ]; then follow=-L; fi; ",
        "depth=\"${WEAVER_GLOB_MAXDEPTH:-24}\"; ",
        "walk() { find $follow \"$1\" -maxdepth \"$depth\" \\( -name .git -o -name 'target*' -o -name node_modules -o -name build \\) -prune -o -type f -name \"$2\" -print; }; ",
        "if [ \"$(git rev-parse --is-inside-work-tree 2>/dev/null)\" = true ] && files=$(git ls-files -co --exclude-standard -- \"$2\" 2>/dev/null); then ",
        "top=$(git rev-parse --show-toplevel 2>/dev/null); [ -n \"$top\" ] && cd \"$top\"; ",
        "printf '%s\\n' \"$files\" | while IFS= read -r f; do ",
        "[ -z \"$f\" ] && continue; ",
        "case \"${f##*/}\" in $1) printf '%s\\n' \"$f\";; esac; ",
        "[ -n \"$follow\" ] && [ -d \"$f\" ] && walk \"$f\" \"$1\"; ",
        "done | awk '!seen[$0]++'; exit 0; fi; ",
        "walk \"$2\" \"$1\" | awk '!seen[$0]++'"
    ]

pub def grep_run (id : String) (j : Json) : ResultT String IO Content :=
    match GrepArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (do {
                let c <- search_spawn id grep_script args.pattern args.path "";
                return (Result.ok c)
            }),
    }

/// An optional boolean key, read off the raw JSON: `follow_links` is not
/// part of the all-required `GlobArgs` derive, the same shape as `read`'s
/// `offset`/`limit`.
def bool_of_key (key : String) (j : Json) : Option Bool :=
    match Json.get_object j {
        Result.err _ => Option.none,
        Result.ok o => match Json.object_get key o {
            Option.none => Option.none,
            Option.some v => match Json.get_bool v {
                Result.ok b => Option.some b,
                Result.err _ => Option.none,
            },
        },
    }

pub def glob_run (id : String) (j : Json) : ResultT String IO Content :=
    match GlobArgs.deserialize_json j {
        Result.err e => ResultT.mk (return (Result.ok (tool_err id e))),
        Result.ok args =>
            ResultT.mk (do {
                let follow : String := match bool_of_key "follow_links" j {
                    Option.none => "1",
                    Option.some b => if b then "1" else "0",
                };
                let c <- search_spawn id glob_script args.pattern args.path follow;
                return (Result.ok c)
            }),
    }
