/// weaver / trust -- ask before a project's files steer the model.
///
/// A project's AGENTS.md files become instructions, and its
/// `.weaver/config.toml` can loosen the approval mode. A file the user did
/// not write can carry prompt injection, so neither is loaded until the
/// user has trusted the project (weaver.md Phase 19). Trust is recorded
/// per repo root in `~/.weaver/trusted.json` together with the text the
/// user trusted: when any of those files is new or edited since (a
/// `git pull`), weaver asks again and can show what changed.
use std::io {IO.read_file, IO.write_file, IO.get_env}
use std::path {Path, Path.to_string, Path.join}
use std::process {exec_cmd}
use std::map {Map, BTreeMap}
use std::list {List.intercalate, List.filter, List.any, List.filter_map}
use json::json {
    Json, Json.parse, Json.to_string, Json.make_object, Json.make_object_pairs, Json.make_array,
    Json.make_str, Json.get_object, Json.get_array, Json.get_str, Json.object_get,
}
use weaver::instructions {InstrFile, Instructions.project, Instructions.read_one, Instructions.size_text}
use weaver::place {SessionPlace}
use weaver::diff {Diff.render, Diff.lines}

/// One file the trust covers: its name relative to the repo root and the
/// (capped) text.
pub struct TrustItem {
    name : String,
    text : String,
}

/// What the record says about the project's files now.
pub type TrustState {
    trust_ok,
    trust_new,
    trust_changed (names : List String),
}

/// The answer for this run, and the startup note when there is one.
pub struct TrustOutcome {
    trusted : Bool,
    note : Option String,
}

pub def Trust.config_name : String := ".weaver/config.toml"

// ── the files ───────────────────────────────────────────────────────────

/// The project's AGENTS.md files, then `.weaver/config.toml` in the cwd.
pub def Trust.items (place : SessionPlace) : IO (List TrustItem) := do {
    let fs <- Instructions.project place;
    let cfg <- Instructions.read_one (Path.join place.cwd (Path.path Trust.config_name)) "config";
    let docs : List TrustItem := List.map (item_of place) fs;
    IO.pure (match cfg {
        Option.some c => List.append docs [item_of place c],
        Option.none => docs,
    })
}

def item_of (place : SessionPlace) (f : InstrFile) : TrustItem :=
    let t : TrustItem := { name := Trust.relative place.repo f.path, text := f.text } in
    t

/// `p` relative to `root` when it is under it, else whole.
pub def Trust.relative (root : Path) (p : Path) : String :=
    let r : String := String.concat (Path.to_string root) "/" in
    let s : String := Path.to_string p in
    if String.starts_with r s then String.drop (String.length r) s else s

// ── the record ──────────────────────────────────────────────────────────

pub def Trust.record_path : IO (Option Path) := do {
    let home <- IO.get_env "HOME";
    IO.pure (match home {
        Option.some h => if String.is_empty h then Option.none else Option.some (Path.path (String.concat h "/.weaver/trusted.json")),
        Option.none => Option.none,
    })
}

/// The whole record, `{root: [{name, text}]}`; empty when missing or bad.
pub def Trust.read_record (p : Path) : IO (BTreeMap String Json) := do {
    let r <- IO.read_file p;
    IO.pure (match r {
        Result.err _ => BTreeMap.empty,
        Result.ok text => Trust.parse_record text,
    })
}

pub def Trust.parse_record (text : String) : BTreeMap String Json :=
    match Json.parse text {
        Result.err _ => BTreeMap.empty,
        Result.ok j => match Json.get_object j {
            Result.ok o => o,
            Result.err _ => BTreeMap.empty,
        },
    }

/// The items recorded for `root`; none when the root was never trusted.
pub def Trust.recorded (record : BTreeMap String Json) (root : String) : Option (List TrustItem) :=
    match Json.object_get root record {
        Option.none => Option.none,
        Option.some j => match Json.get_array j {
            Result.err _ => Option.none,
            Result.ok xs => Option.some (List.filter_map decode_item xs),
        },
    }

def decode_item (j : Json) : Option TrustItem :=
    match Json.get_object j {
        Result.err _ => Option.none,
        Result.ok o => match Json.object_get "name" o {
            Option.none => Option.none,
            Option.some n => match Json.object_get "text" o {
                Option.none => Option.none,
                Option.some t => decode_strs n t,
            },
        },
    }

def decode_strs (n : Json) (t : Json) : Option TrustItem :=
    match Json.get_str n {
        Result.err _ => Option.none,
        Result.ok name => match Json.get_str t {
            Result.err _ => Option.none,
            Result.ok text =>
                let it : TrustItem := { name := name, text := text } in
                Option.some it,
        },
    }

def encode_item (it : TrustItem) : Json :=
    Json.make_object_pairs [Pair.pair "name" (Json.make_str it.name), Pair.pair "text" (Json.make_str it.text)]

/// The record with `root` set to `items`, as JSON text.
pub def Trust.with_root (record : BTreeMap String Json) (root : String) (items : List TrustItem) : String :=
    Json.to_string (Json.make_object (Map.insert root (Json.make_array (List.map encode_item items)) record))

/// Record, in the record at `p`, that the user trusts `root` with these files.
pub def Trust.remember_at (p : Path) (root : String) (items : List TrustItem) : IO Bool := do {
    let record <- Trust.read_record p;
    let dir : String := String.slice (Path.to_string p) 0 (String.length (Path.to_string p) - String.length "/trusted.json");
    let _ <- exec_cmd "mkdir" ["-p", dir];
    let w <- IO.write_file p (Trust.with_root record root items);
    IO.pure (match w { Result.ok _ => true, Result.err _ => false })
}

// ── the decision ────────────────────────────────────────────────────────

/// `trust_new` when nothing is recorded; `trust_changed` naming each file
/// that is new or whose text differs; `trust_ok` otherwise. A file that
/// was removed changes nothing: there is less to trust.
pub def Trust.state (recorded : Option (List TrustItem)) (now : List TrustItem) : TrustState :=
    match recorded {
        Option.none => TrustState.trust_new,
        Option.some old =>
            let changed : List String := List.map (fn (it : TrustItem) => it.name) (List.filter (fn (it : TrustItem) => Bool.not (same_in old it)) now) in
            if List.is_empty changed then TrustState.trust_ok else TrustState.trust_changed changed,
    }

def same_in (old : List TrustItem) (it : TrustItem) : Bool :=
    List.any (fn (o : TrustItem) => String.beq o.name it.name && String.beq o.text it.text) old

/// What the line prompt shows before asking.
pub def Trust.question (root : Path) (state : TrustState) (items : List TrustItem) : String :=
    String.concat_list [
        "weaver: ", Path.to_string root, header_of state,
        List.intercalate "\n" (List.map item_line items),
        "\nA file you did not write can steer the model (prompt injection): run commands, edit files, send data out.\n",
        "Trust this project? [y]es  [n]o  [v]iew: ",
    ]

def header_of (state : TrustState) : String :=
    match state {
        TrustState.trust_changed names =>
            String.concat_list [" changed since you trusted it (", List.intercalate ", " names, "). Its files the model will take as instructions:\n"],
        _ => " is a new project. It has files the model will take as instructions:\n",
    }

def item_line (it : TrustItem) : String :=
    String.concat_list ["  ", it.name, "  ", Instructions.size_text (String.length it.text),
        if String.beq it.name Trust.config_name then "  (settings: can change the approval mode)" else ""]

/// `v`: each changed file as a diff against what was trusted, every other
/// file's first 40 lines.
pub def Trust.view (recorded : Option (List TrustItem)) (items : List TrustItem) : String :=
    List.intercalate "\n" (List.map (view_one recorded) items)

def view_one (recorded : Option (List TrustItem)) (it : TrustItem) : String :=
    match old_text recorded it.name {
        Option.some old =>
            if String.beq old it.text then String.concat_list ["── ", it.name, " (unchanged)"]
            else String.concat_list ["── ", it.name, " (changed)\n", Diff.render old it.text],
        Option.none => String.concat_list ["── ", it.name, "\n", List.intercalate "\n" (first_lines 40 (Diff.lines it.text))],
    }

def old_text (recorded : Option (List TrustItem)) (name : String) : Option String :=
    match recorded {
        Option.none => Option.none,
        Option.some old => match List.filter (fn (o : TrustItem) => String.beq o.name name) old {
            List.cons o _ => Option.some o.text,
            List.empty => Option.none,
        },
    }

#[partial]
def first_lines (n : I64) (xs : List String) : List String :=
    match xs {
        List.empty => List.empty,
        List.cons x rest => if n < 1 then ["…"] else List.cons x (first_lines (n - 1) rest),
    }

/// The answer to one prompt line: `y`/`yes` trust, `v`/`view` show the
/// files, anything else (an empty line included) declines.
pub type TrustAnswer {
    answer_yes,
    answer_view,
    answer_no,
}

pub def Trust.answer_of (line : String) : TrustAnswer :=
    let a : String := String.to_lowercase (String.trim line) in
    if String.beq a "y" || String.beq a "yes" then TrustAnswer.answer_yes
    else if String.beq a "v" || String.beq a "view" then TrustAnswer.answer_view
    else TrustAnswer.answer_no

/// The note for a project left untrusted this run.
pub def Trust.declined_note (why : String) : String :=
    String.concat_list ["project not trusted", why, ": AGENTS.md and .weaver/config.toml ignored (/trust to trust it)"]

/// `--trust`, or `WEAVER_TRUST` set to exactly `1`.
pub def Trust.forced_by (flag : Bool) (env : Option String) : Bool :=
    if flag then true
    else match env {
        Option.some v => String.beq v "1",
        Option.none => false,
    }

/// Decide for this run against the record at `rp`. `forced` (`--trust`, `WEAVER_TRUST=1`) trusts
/// without asking or recording; without a terminal the project stays
/// untrusted; otherwise the user is asked on `read`/`write`, and a yes
/// is recorded. `interactive` runs only when there is a question to ask. Both it
/// and `read` are thunks: a zero-argument `IO` def passed as an
/// argument runs at the call when compiled.
pub def Trust.decide (rp : Option Path) (place : Option SessionPlace) (forced : Bool) (interactive : Unit -> IO Bool) (read : Unit -> IO (Option String)) (write : String -> IO Unit) : IO TrustOutcome :=
    match place {
        Option.none => IO.pure (outcome false Option.none),
        Option.some p => if forced then IO.pure (outcome true Option.none) else decide_at rp p interactive read write,
    }

def outcome (trusted : Bool) (note : Option String) : TrustOutcome :=
    let o : TrustOutcome := { trusted := trusted, note := note } in
    o

def decide_at (rp : Option Path) (p : SessionPlace) (interactive : Unit -> IO Bool) (read : Unit -> IO (Option String)) (write : String -> IO Unit) : IO TrustOutcome := do {
    let items <- Trust.items p;
    let record <- record_at rp;
    let recorded : Option (List TrustItem) := Trust.recorded record (Path.to_string p.repo);
    if List.is_empty items then IO.pure (outcome true Option.none)
    else decide_state (asker_of rp p items recorded read write) interactive
}

def asker_of (rp : Option Path) (p : SessionPlace) (items : List TrustItem) (recorded : Option (List TrustItem)) (read : Unit -> IO (Option String)) (write : String -> IO Unit) : Asker :=
    let a : Asker := { rp := rp, place := p, items := items, recorded := recorded,
        state := Trust.state recorded items, read := read, write := write } in
    a

/// `remember_at` when there is a record to write; false otherwise.
pub def Trust.remember (rp : Option Path) (root : Path) (items : List TrustItem) : IO Bool :=
    match rp {
        Option.some path => Trust.remember_at path (Path.to_string root) items,
        Option.none => IO.pure false,
    }

def record_at (rp : Option Path) : IO (BTreeMap String Json) :=
    match rp {
        Option.some path => Trust.read_record path,
        Option.none => IO.pure BTreeMap.empty,
    }

/// One prompt's context: the record, the place, the files, what the
/// record said about them, and the terminal to ask on.
struct Asker {
    rp : Option Path,
    place : SessionPlace,
    items : List TrustItem,
    recorded : Option (List TrustItem),
    state : TrustState,
    read : Unit -> IO (Option String),
    write : String -> IO Unit,
}

def decide_state (a : Asker) (interactive : Unit -> IO Bool) : IO TrustOutcome :=
    match a.state {
        TrustState.trust_ok => IO.pure (outcome true Option.none),
        _ => do {
            let tty <- interactive unit;
            ask_if a tty
        },
    }

def ask_if (a : Asker) (tty : Bool) : IO TrustOutcome :=
    if tty then ask a 3
    else IO.pure (outcome false (Option.some (Trust.declined_note " (no terminal to ask on; pass --trust)")))

def read_line_of (a : Asker) : IO (Option String) := a.read unit

#[partial]
def ask (a : Asker) (views : I64) : IO TrustOutcome := do {
    a.write (Trust.question a.place.repo a.state a.items);
    let line <- read_line_of a;
    match line {
        Option.none => IO.pure (outcome false (Option.some (Trust.declined_note ""))),
        Option.some l => answered a views (Trust.answer_of l),
    }
}

#[partial]
def answered (a : Asker) (views : I64) (ans : TrustAnswer) : IO TrustOutcome :=
    match ans {
        TrustAnswer.answer_yes => do {
            let _ <- Trust.remember a.rp a.place.repo a.items;
            IO.pure (outcome true Option.none)
        },
        TrustAnswer.answer_view =>
            if views < 1 then IO.pure (outcome false (Option.some (Trust.declined_note "")))
            else do {
                a.write (String.concat (Trust.view a.recorded a.items) "\n\n");
                ask a (views - 1)
            },
        TrustAnswer.answer_no => IO.pure (outcome false (Option.some (Trust.declined_note ""))),
    }
