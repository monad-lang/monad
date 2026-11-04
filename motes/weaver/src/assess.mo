/// weaver / assess -- where a tool pick reaches, read from its input before
/// the gate decides. A file tool names its `path`; a `shell` or
/// `start_process` command is tokenized (`shell_words.mo`) and every
/// path-like word, `cd` target and redirect target is resolved against the
/// working directory. Lexical, like `Permissions.within`: no symlinks are
/// followed and nothing runs.
use shuttle::gate {Pick}
use json::json {Json, Json.get_object, Json.object_get, Json.get_str}
use std::path {Path, Path.of, Path.to_string, Path.beq}
use std::list {List.intercalate, List.any}
use weaver::shell_words {ShellWord, ShellRedir, ShellCmd, ShellScript, ShellWords.parse}
use weaver::permissions {Permissions.within, Permissions.normalize}

/// `inside`: every path the pick names is under the working directory (a
/// command naming none is inside too); `outside` lists the ones that are
/// not; `unknown` when a path depends on something only known when the
/// command runs.
pub type Reach {
    inside,
    outside (paths : List Path),
    unknown,
}

/// The gate's reading of one pick. `danger` names why a command is
/// destructive enough that auto mode must still ask.
pub struct Assessment {
    scope : Reach,
    danger : Option String,
}

/// Commands longer than this are not scanned (the scanner recurses per
/// byte): their scope is unknown.
def scan_max_bytes : I64 := 16384

/// Nested `$(..)`, `sh -c '..'` and `eval` text is scanned this deep.
def nest_max : I64 := 3

pub def Assess.pick (root : Option Path) (p : Pick) : Assessment :=
    if Bool.or (String.beq p.name "shell") (String.beq p.name "start_process")
    then command_pick root p
    else match input_str "path" p.input {
        Option.none => Assess.unknown,
        Option.some path => Assess.path root path,
    }

pub def Assess.unknown : Assessment :=
    let a : Assessment := { scope := Reach.unknown, danger := Option.none } in
    a

/// A file tool's target.
pub def Assess.path (root : Option Path) (path : String) : Assessment :=
    let w : Walk := note_word (walk_start root root) (plain_word path) in
    walk_result w

def command_pick (root : Option Path) (p : Pick) : Assessment :=
    match input_str "command" p.input {
        Option.none => Assess.unknown,
        Option.some cmd =>
            let base : Option Path := match input_str "cwd" p.input {
                Option.none => root,
                Option.some c => resolve_dir root c,
            } in
            let w0 : Walk := walk_start root root in
            // A `cwd` outside the root is itself a place the command reaches.
            let w1 : Walk := match input_str "cwd" p.input {
                Option.none => w0,
                Option.some c => note_word w0 (plain_word c),
            } in
            let w2 : Walk := { w1 with base := base } in
            walk_result (walk_text 0 cmd w2),
    }

/// `command` run from the root.
pub def Assess.command (root : Option Path) (cmd : String) : Assessment :=
    walk_result (walk_text 0 cmd (walk_start root root))

def input_str (key : String) (input : Json) : Option String :=
    match Json.get_object input {
        Result.err _ => Option.none,
        Result.ok obj => match Json.object_get key obj {
            Option.none => Option.none,
            Option.some j => match Json.get_str j {
                Result.ok s => if String.is_empty s then Option.none else Option.some s,
                Result.err _ => Option.none,
            },
        },
    }

def plain_word (text : String) : ShellWord :=
    let w : ShellWord := { text := text, dynamic := false } in
    w

// ── the walk ────────────────────────────────────────────────────────────

/// `base` is where relative words resolve: the root, moved by `cd`; none
/// once a `cd` went somewhere unknowable.
struct Walk {
    root : Option Path,
    base : Option Path,
    outside : List Path,
    unknown : Bool,
    danger : Option String,
}

def walk_start (root : Option Path) (base : Option Path) : Walk :=
    let w : Walk := { root := root, base := base, outside := List.empty, unknown := false, danger := Option.none } in
    w

def walk_result (w : Walk) : Assessment :=
    let scope : Reach := match w.root {
        Option.none => Reach.unknown,
        Option.some _ =>
            if w.unknown then Reach.unknown
            else if List.is_empty w.outside then Reach.inside
            else Reach.outside (List.reverse w.outside),
    } in
    let a : Assessment := { scope := scope, danger := w.danger } in
    a

def lost (w : Walk) : Walk :=
    let w2 : Walk := { w with unknown := true } in
    w2

def add_outside (p : Path) (w : Walk) : Walk :=
    if List.any (fn (q : Path) => Path.beq p q) w.outside then w
    else
        let w2 : Walk := { w with outside := List.cons p w.outside } in
        w2

def add_danger (reason : String) (w : Walk) : Walk :=
    match w.danger {
        Option.some _ => w,
        Option.none =>
            let w2 : Walk := { w with danger := Option.some reason } in
            w2,
    }

/// Bounded by `nest_max`: each nested text is one level deeper.
#[terminating]
def walk_text (depth : I64) (text : String) (w : Walk) : Walk :=
    if I64.lt nest_max depth then lost w
    else if I64.lt scan_max_bytes (String.length text) then lost w
    else walk_script depth (ShellWords.parse text) w

#[terminating]
def walk_script (depth : I64) (sc : ShellScript) (w0 : Walk) : Walk :=
    let w1 : Walk := if sc.unknown then lost w0 else w0 in
    let w2 : Walk := walk_cmds depth sc.cmds w1 in
    walk_nested depth sc.nested w2

#[terminating]
def walk_nested (depth : I64) (texts : List String) (w : Walk) : Walk :=
    match texts {
        List.empty => w,
        List.cons t rest => walk_nested depth rest (walk_text (depth + 1) t w),
    }

#[terminating]
def walk_cmds (depth : I64) (cmds : List ShellCmd) (w : Walk) : Walk :=
    match cmds {
        List.empty => w,
        List.cons c rest => walk_cmds depth rest (walk_cmd depth c w),
    }

#[terminating]
def walk_cmd (depth : I64) (c : ShellCmd) (w0 : Walk) : Walk :=
    let words : List ShellWord := Assess.command_words c.words in
    let w1 : Walk := walk_redirs c.redirs w0 in
    match words {
        List.empty => w1,
        List.cons name args => walk_named depth name args w1,
    }

#[terminating]
def walk_named (depth : I64) (name : ShellWord) (args : List ShellWord) (w : Walk) : Walk :=
    if String.beq name.text "cd" then walk_cd args w
    else
        let w2 : Walk := note_words args w in
        match Assess.inline_script name.text args {
            Option.none => w2,
            Option.some text => walk_text (depth + 1) text w2,
        }

#[partial]
def note_words (ws : List ShellWord) (w : Walk) : Walk :=
    match ws {
        List.empty => w,
        List.cons x rest => note_words rest (note_word w x),
    }

#[partial]
def walk_redirs (rs : List ShellRedir) (w : Walk) : Walk :=
    match rs {
        List.empty => w,
        List.cons r rest => walk_redirs rest (note_word w r.target),
    }

/// `cd DIR` moves the base. `cd` and `cd ~` go home (outside); `cd -` and
/// a dynamic target go somewhere unknowable. Either way the base is lost.
def walk_cd (args : List ShellWord) (w : Walk) : Walk :=
    match args {
        List.empty => cd_lost (add_outside (Path.path "~") w),
        List.cons d _ =>
            if String.beq d.text "-" then cd_lost (lost w)
            else if Bool.or d.dynamic (String.starts_with "~" d.text)
            then cd_lost (note_word w d)
            else
                let w2 : Walk := note_word w d in
                let w3 : Walk := { w2 with base := resolve_dir w2.base d.text } in
                w3,
    }

def cd_lost (w : Walk) : Walk :=
    let w2 : Walk := { w with base := Option.none } in
    w2

/// One word: when it reads as a path, classify where it points.
def note_word (w : Walk) (x : ShellWord) : Walk :=
    let text : String := Assess.path_part x.text in
    if Bool.not (Assess.path_like text) then w
    else if x.dynamic then lost w
    else match Assess.resolve w.base text {
        Option.none => lost w,
        Option.some p =>
            if Assess.harmless p then w
            else if Assess.inside w.root p then w
            else add_outside p w,
    }

// ── words ───────────────────────────────────────────────────────────────

/// The words that name and drive the command: leading assignments,
/// grouping and control keywords, and transparent wrappers (`env`,
/// `command`, `nice`, `nohup`, `time`, `exec`, `timeout`) are dropped.
#[partial]
pub def Assess.command_words (ws : List ShellWord) : List ShellWord :=
    match ws {
        List.empty => ws,
        List.cons x rest =>
            if Bool.or (is_assignment x.text) (is_keyword x.text) then Assess.command_words rest
            else if is_wrapper x.text then Assess.command_words (skip_wrapper_opts x.text rest)
            else ws,
    }

def is_keyword (t : String) : Bool :=
    List.any (fn (k : String) => String.beq k t)
        ["{", "}", "!", "if", "then", "else", "elif", "fi", "do", "done", "while", "until", "time"]

def is_wrapper (t : String) : Bool :=
    List.any (fn (k : String) => String.beq k t)
        ["env", "command", "builtin", "nice", "nohup", "exec", "timeout", "stdbuf", "ionice"]

/// A wrapper's own options (`env -i`, `nice -n 5`, `timeout -k 5 30s`):
/// flags, assignments, and for `nice`/`timeout` the one operand they take.
#[partial]
def skip_wrapper_opts (wrapper : String) (ws : List ShellWord) : List ShellWord :=
    match ws {
        List.empty => ws,
        List.cons x rest =>
            if Bool.or (String.starts_with "-" x.text) (is_assignment x.text) then skip_wrapper_opts wrapper rest
            else if Bool.and (String.beq wrapper "timeout") (starts_with_digit x.text) then rest
            else ws,
    }

def starts_with_digit (t : String) : Bool :=
    match String.get t 0 {
        Option.none => false,
        Option.some b =>
            let c : I64 := U8.to_i64 b in
            Bool.and (Bool.not (c < 48)) (Bool.not (57 < c)),
    }

/// `NAME=value` before a command.
def is_assignment (t : String) : Bool :=
    let eq : I64 := index_of_eq t in
    if I64.lt eq 1 then false
    else Bool.not (String.contains (String.slice t 0 eq) "/")
        && Bool.not (String.starts_with "-" t)

#[partial]
def index_of_eq_go (t : String) (i : I64) (n : I64) : I64 :=
    if Bool.not (i < n) then 0 - 1
    else if String.beq (String.slice t i 1) "=" then i
    else index_of_eq_go t (i + 1) n

def index_of_eq (t : String) : I64 := index_of_eq_go t 0 (String.length t)

/// The text a word names as a path: `--out=/x` and `of=/x` name `/x`.
pub def Assess.path_part (t : String) : String :=
    let eq : I64 := index_of_eq t in
    if I64.lt eq 1 then t
    else
        let key : String := String.slice t 0 eq in
        if String.contains key "/" then t
        else String.drop (eq + 1) t

pub def Assess.path_like (t : String) : Bool :=
    if String.is_empty t then false
    else if String.contains t "://" then false
    else String.starts_with "/" t
        || String.starts_with "~" t
        || String.beq t "."
        || String.beq t ".."
        || String.starts_with "./" t
        || String.starts_with "../" t
        || String.contains t "/"

/// `sh -c '<text>'`, `bash -c`, and `eval <words>` run text that is
/// itself a command line.
pub def Assess.inline_script (name : String) (args : List ShellWord) : Option String :=
    if String.beq name "eval" then Option.some (List.intercalate " " (List.map (fn (x : ShellWord) => x.text) args))
    else if is_shell name then dash_c args
    else Option.none

def is_shell (t : String) : Bool :=
    List.any (fn (k : String) => String.beq k t) ["sh", "bash", "zsh", "dash", "ksh", "fish"]

#[partial]
def dash_c (args : List ShellWord) : Option String :=
    match args {
        List.empty => Option.none,
        List.cons x rest =>
            if String.beq x.text "-c" then match rest {
                List.empty => Option.none,
                List.cons body _ => Option.some body.text,
            }
            else if String.starts_with "-" x.text then dash_c rest
            else Option.none,
    }

// ── paths ───────────────────────────────────────────────────────────────

/// Absolute and normalized against `base`; `~` stays literal (it is never
/// inside a workspace this check can vouch for); none when a relative word
/// has no base to resolve against.
pub def Assess.resolve (base : Option Path) (t : String) : Option Path :=
    if String.starts_with "~" t then Option.some (Path.path t)
    else if String.starts_with "/" t then of_normal (Permissions.normalize t)
    else match base {
        Option.none => Option.none,
        Option.some b => of_normal (Permissions.normalize (String.concat (Path.to_string b) (String.concat "/" t))),
    }

def of_normal (s : String) : Option Path :=
    match Path.of s {
        Result.ok p => Option.some p,
        Result.err _ => Option.some (Path.path "/"),
    }

def resolve_dir (base : Option Path) (t : String) : Option Path :=
    if String.starts_with "~" t then Option.none else Assess.resolve base t

/// `~` paths stay literal and are never inside.
pub def Assess.inside (root : Option Path) (p : Path) : Bool :=
    match root {
        Option.none => false,
        Option.some r => Bool.and (Bool.not (String.starts_with "~" (Path.to_string p))) (Permissions.within r p),
    }

/// Device files every command may name.
pub def Assess.harmless (p : Path) : Bool :=
    let t : String := Path.to_string p in
    List.any (fn (k : String) => String.beq k t)
        ["/dev/null", "/dev/stdin", "/dev/stdout", "/dev/stderr", "/dev/tty", "/dev/zero", "/dev/random", "/dev/urandom"]
        || String.starts_with "/dev/fd/" t

// ── display ─────────────────────────────────────────────────────────────

/// The approval prompt's scope line.
pub def Assess.scope_line (root : Option Path) (s : Reach) : String :=
    match s {
        Reach.inside => match root {
            Option.none => "inside the workspace",
            Option.some r => String.concat "inside " (Path.to_string r),
        },
        Reach.outside ps => String.concat "outside the workspace: " (List.intercalate ", " (List.map Path.to_string ps)),
        Reach.unknown => "can't tell where this runs",
    }

pub def Reach.is_inside (s : Reach) : Bool :=
    match s {
        Reach.inside => true,
        _ => false,
    }
