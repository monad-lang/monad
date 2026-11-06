/// weaver / instructions -- the AGENTS.md files a project keeps for its
/// agents, found from the user's config, the repo root, and each directory
/// down to the working directory (weaver.md Phase 19).
///
/// Files are capped (32 KiB each, 96 KiB in all) and cut on a line
/// boundary; a cut file says so and names its path, so the model can read
/// the rest. Whether a project's files are loaded at all is `trust.mo`'s
/// decision; this module only finds and renders them.
use std::io {IO.read_file, IO.get_env}
use std::path {Path, Path.to_string, Path.join, Path.parent, Path.beq}
use std::list {List.intercalate}
use weaver::place {SessionPlace}

/// One loaded file. `scope` is `user`, `repo` or `dir`.
pub struct InstrFile {
    path : Path,
    scope : String,
    text : String,
    truncated : Bool,
}

pub def Instructions.file_cap : I64 := 32768
pub def Instructions.total_cap : I64 := 98304

pub def Instructions.file_name : String := "AGENTS.md"

/// The directories from `repo` down to `cwd`, root first. Just `[cwd]`
/// when `cwd` is not under `repo` (outside a repo the two are equal).
pub def Instructions.chain (repo : Path) (cwd : Path) : List Path :=
    chain_up repo cwd [cwd] 64

#[partial]
def chain_up (repo : Path) (here : Path) (acc : List Path) (fuel : I64) : List Path :=
    if Path.beq here repo then acc
    else if fuel < 1 then [cwd_of acc]
    else match Path.parent here {
        Option.none => [cwd_of acc],
        Option.some up => chain_up repo up (List.cons up acc) (fuel - 1),
    }

/// The last element of the walk, the cwd itself.
#[partial]
def cwd_of (acc : List Path) : Path :=
    match acc {
        List.empty => Path.path ".",
        List.cons p rest => if List.is_empty rest then p else cwd_of rest,
    }

/// `$XDG_CONFIG_HOME/weaver/AGENTS.md`, else `~/.config/weaver/AGENTS.md`.
pub def Instructions.user_path : IO (Option Path) := do {
    let xdg <- IO.get_env "XDG_CONFIG_HOME";
    let home <- IO.get_env "HOME";
    IO.pure (Instructions.user_path_of xdg home)
}

pub def Instructions.user_path_of (xdg : Option String) (home : Option String) : Option Path :=
    match non_empty xdg {
        Option.some x => Option.some (Path.path (String.concat x "/weaver/AGENTS.md")),
        Option.none => match non_empty home {
            Option.some h => Option.some (Path.path (String.concat h "/.config/weaver/AGENTS.md")),
            Option.none => Option.none,
        },
    }

def non_empty (o : Option String) : Option String :=
    match o {
        Option.some s => if String.is_empty s then Option.none else Option.some s,
        Option.none => Option.none,
    }

/// The project's files only: `AGENTS.md` in each directory from the repo
/// root down to the cwd. The root's is scoped `repo`, deeper ones `dir`.
pub def Instructions.project (place : SessionPlace) : IO (List InstrFile) :=
    read_dirs place.repo (Instructions.chain place.repo place.cwd) List.empty

#[partial]
def read_dirs (repo : Path) (dirs : List Path) (acc : List InstrFile) : IO (List InstrFile) :=
    match dirs {
        List.empty => IO.pure (List.reverse acc),
        List.cons d rest => read_dir_step repo d rest acc,
    }

#[terminating]
def read_dir_step (repo : Path) (d : Path) (rest : List Path) (acc : List InstrFile) : IO (List InstrFile) := do {
    let scope : String := if Path.beq d repo then "repo" else "dir";
    let one <- Instructions.read_one (Path.join d (Path.path Instructions.file_name)) scope;
    read_dirs repo rest (push_some one acc)
}

def push_some (o : Option InstrFile) (acc : List InstrFile) : List InstrFile :=
    match o {
        Option.some f => List.cons f acc,
        Option.none => acc,
    }

/// Every file for a session: the user's, then the project's when
/// `trusted`. The total cap applies across them in that order.
pub def Instructions.discover (user : Option Path) (place : Option SessionPlace) (trusted : Bool) : IO (List InstrFile) := do {
    let mine <- user_file user;
    let theirs <- project_if place trusted;
    IO.pure (Instructions.cap_total (List.append mine theirs) Instructions.total_cap)
}

def user_file (user : Option Path) : IO (List InstrFile) :=
    match user {
        Option.none => IO.pure List.empty,
        Option.some p => do {
            let one <- Instructions.read_one p "user";
            IO.pure (push_some one List.empty)
        },
    }

def project_if (place : Option SessionPlace) (trusted : Bool) : IO (List InstrFile) :=
    match place {
        Option.some p => if trusted then Instructions.project p else IO.pure List.empty,
        Option.none => IO.pure List.empty,
    }

/// A file, capped to `file_cap`; none when it is missing, unreadable or blank.
pub def Instructions.read_one (p : Path) (scope : String) : IO (Option InstrFile) := do {
    let r <- IO.read_file p;
    IO.pure (match r {
        Result.err _ => Option.none,
        Result.ok text =>
            if String.is_empty (String.trim text) then Option.none
            else Option.some (Instructions.capped p scope text Instructions.file_cap),
    })
}

pub def Instructions.capped (p : Path) (scope : String) (text : String) (cap : I64) : InstrFile :=
    let cut : I64 := Instructions.cut_at text cap in
    let f : InstrFile := { path := p, scope := scope, text := String.slice text 0 cut, truncated := cut < String.length text } in
    f

/// The byte length to keep so `text` fits `cap`: all of it when it fits,
/// else up to and including the last newline within the cap (0 when there
/// is none), so a cut never lands mid-line or mid-character.
pub def Instructions.cut_at (text : String) (cap : I64) : I64 :=
    if String.length text < cap + 1 then String.length text
    else last_newline (String.to_list text) 0 cap 0

#[partial]
def last_newline (bs : List U8) (i : I64) (cap : I64) (best : I64) : I64 :=
    match bs {
        List.empty => best,
        List.cons b rest =>
            if i + 1 > cap then best
            else last_newline rest (i + 1) cap (if U8.beq b 10u8 then i + 1 else best),
    }

/// Apply the total cap in order: each file gets what is left of `budget`.
#[partial]
pub def Instructions.cap_total (fs : List InstrFile) (budget : I64) : List InstrFile :=
    match fs {
        List.empty => List.empty,
        List.cons f rest =>
            let room : I64 := if budget < 0 then 0 else budget in
            let kept : InstrFile := recap f room in
            List.cons kept (Instructions.cap_total rest (room - String.length kept.text)),
    }

def recap (f : InstrFile) (room : I64) : InstrFile :=
    if String.length f.text < room + 1 then f
    else
        let g : InstrFile := Instructions.capped f.path f.scope f.text room in
        { g with truncated := true }

pub def Instructions.size_of (fs : List InstrFile) : I64 :=
    match fs {
        List.empty => 0,
        List.cons f rest => String.length f.text + Instructions.size_of rest,
    }

// ── rendering ───────────────────────────────────────────────────────────

/// The system-prompt block; empty for no files.
pub def Instructions.render (fs : List InstrFile) : String :=
    match fs {
        List.empty => "",
        List.cons _ _ =>
            String.concat "# Project instructions\nThe files below are instructions from the user and the project. Follow them; a deeper directory's file refines a shallower one.\n\n"
                (List.intercalate "\n\n" (List.map Instructions.render_one fs)),
    }

pub def Instructions.render_one (f : InstrFile) : String :=
    String.concat_list ["## ", Path.to_string f.path, " (", f.scope, ")\n", f.text,
        if f.truncated then String.concat_list ["\n[truncated; read ", Path.to_string f.path, " for the rest]"] else ""]

/// `AGENTS.md (repo, 21 KiB)`-style summary of one file.
pub def Instructions.label (f : InstrFile) : String :=
    String.concat_list [Path.to_string f.path, " (", f.scope, ", ", Instructions.size_text (String.length f.text),
        if f.truncated then ", truncated" else "", ")"]

pub def Instructions.size_text (n : I64) : String :=
    if n < 1024 then String.concat (I64.to_string n) " B"
    else String.concat (I64.to_string ((n + 512) / 1024)) " KiB"

/// The startup note: one label per loaded file; none when nothing loaded.
pub def Instructions.note (fs : List InstrFile) : Option String :=
    match fs {
        List.empty => Option.none,
        List.cons _ _ => Option.some (String.concat "instructions: " (List.intercalate ", " (List.map Instructions.label fs))),
    }

/// Weaver's own system prompt, before any instructions file.
pub def Prompt.base : String :=
    "You are Weaver, an interactive coding assistant. Inspect the workspace with read, grep and glob before changing anything; prefer edit over write for existing files; explain what you are about to do before doing it. For Monad code, use monad_check to type-check a file or snippet and monad_eval to try expressions in the self-hosted interpreter (pure programs only). For a task of three or more steps, keep a todo list with todo_write and update it as each step starts and finishes."

/// `base` followed by the rendered instruction files, when there are any.
/// Built once per session: it is the cached prefix of every request.
pub def Prompt.with_files (base : String) (fs : List InstrFile) : String :=
    let block : String := Instructions.render fs in
    if String.is_empty block then base else String.concat_list [base, "\n\n", block]

/// The main session's system prompt.
pub def Prompt.system (fs : List InstrFile) : String :=
    Prompt.with_files Prompt.base fs
