/// Weaver's settings -- weaver.md Phase 6: the knobs a user does not
/// want to re-type every run, persisted as TOML. Two files, in
/// resolution order GLOBAL -> PROJECT -> RUNTIME: `~/.weaver/config.toml`
/// (the user's defaults) then `.weaver/config.toml` (the project's, in
/// the repo but gitignored) then the runtime `/`-commands and CLI flags,
/// which always win. `Settings.merge` is that resolution as one pure
/// function -- later wins, field by field, with the capability table
/// unioned key by key.
///
/// `max_turns` rides the settings too (the flag stays the runtime
/// override), and `mcp_caps` overrides the conservative `exec` default
/// on a mounted MCP server's proxy tools: a server's catalogue is
/// arbitrary code, so the override is an explicit, per-server trust
/// decision the file records.
use shuttle::gate {Capability}
use weaver::policy {Mode, Mode.parse}
use toml::toml {Toml.Value, Toml.parse, Toml.get_string, Toml.get_integer, Toml.get_table, Toml.table_get}
use std::io {IO.get_env, IO.read_file, IO.file_exists}
use std::path {Path.of}
use std::map {BTreeMap, BTreeMap.to_list}

/// One settings file's worth of knobs -- every field optional, an
/// absent file is simply all-absent.
pub struct Settings {
    mode : Option Mode,
    provider : Option String,
    model : Option String,
    max_turns : Option I64,
    caps : BTreeMap String Capability,
}

pub def Settings.empty : Settings := {
    mode := Option.none,
    provider := Option.none,
    model := Option.none,
    max_turns := Option.none,
    caps := BTreeMap.empty,
}

/// The resolution order as a function: `over` wins field by field, the
/// capability tables union with `over`'s entries winning per key.
pub def Settings.merge (base : Settings) (over : Settings) : Settings := {
    mode := merge_opt base.mode over.mode,
    provider := merge_opt base.provider over.provider,
    model := merge_opt base.model over.model,
    max_turns := merge_opt base.max_turns over.max_turns,
    caps := merge_caps base.caps (BTreeMap.to_list over.caps),
}

def merge_opt {A : Type} (base : Option A) (over : Option A) : Option A :=
    match over {
        Option.some v => Option.some v,
        Option.none => base,
    }

/// The union, `over`'s entries winning per key.
#[partial]
def merge_caps (base : BTreeMap String Capability) (entries : List (Pair String Capability)) : BTreeMap String Capability :=
    match entries {
        List.empty => base,
        List.cons kv rest => merge_caps (cap_insert kv base) rest,
    }

def cap_insert (kv : Pair String Capability) (acc : BTreeMap String Capability) : BTreeMap String Capability :=
    match kv { Pair.pair k v => Map.insert k v acc }

// ── Loading ─────────────────────────────────────────────────────────────

/// The resolved settings: the global file under the project file.
/// A missing or unparsable file contributes nothing -- an interactive
/// tool must start, not refuse, over its own config.
pub def Settings.load : IO Settings := do {
    let g <- Settings.load_global;
    let p <- Settings.load_project;
    return (Settings.merge g p)
}

pub def Settings.load_global : IO Settings :=
    load_home

def load_home : IO Settings := do {
    let home <- IO.get_env "HOME";
    home_settings home
}

def home_settings (home : Option String) : IO Settings :=
    match home {
        Option.none => IO.pure Settings.empty,
        Option.some h => Settings.load_of_path (String.concat h "/.weaver/config.toml"),
    }

/// The project file is relative to the working directory -- Weaver's
/// session starts wherever the user launched it.
pub def Settings.load_project : IO Settings :=
    Settings.load_of_path ".weaver/config.toml"

pub def Settings.load_of_path (path : String) : IO Settings :=
    match Path.of path {
        Result.err _ => IO.pure Settings.empty,
        Result.ok p => load_at p,
    }

def load_at (p : Path) : IO Settings := do {
    let exists <- IO.file_exists p;
    if Bool.not exists
    then IO.pure Settings.empty
    else do {
        let text <- IO.read_file p;
        return (parse_settings text)
    }
}

// ── Parsing ─────────────────────────────────────────────────────────────

/// The file's shape:
///
/// ```toml
/// mode = "plan"
/// provider = "ollama"
/// model = "qwen3:8b"
/// max_turns = 20
///
/// [mcp_caps]
/// mcp-server-filesystem = "read"
/// ```
///
/// A parse failure is the empty settings (see `Settings.load`); unknown
/// keys are ignored -- a settings file may well hold another tool's
/// keys too.
pub def parse_settings (text : String) : Settings :=
    match Toml.parse text {
        Result.err _ => Settings.empty,
        Result.ok root => settings_of root,
    }

def settings_of (root : BTreeMap String Toml.Value) : Settings := {
    mode := opt_mode (str_at "mode" root),
    provider := str_at "provider" root,
    model := str_at "model" root,
    max_turns := int_at "max_turns" root,
    caps := caps_of (table_at "mcp_caps" root),
}

def str_at (key : String) (root : BTreeMap String Toml.Value) : Option String :=
    match Toml.table_get key root {
        Option.none => Option.none,
        Option.some v => match Toml.get_string v {
            Result.ok s => Option.some s,
            Result.err _ => Option.none,
        },
    }

def int_at (key : String) (root : BTreeMap String Toml.Value) : Option I64 :=
    match Toml.table_get key root {
        Option.none => Option.none,
        Option.some v => match Toml.get_integer v {
            Result.ok n => Option.some n,
            Result.err _ => Option.none,
        },
    }

def table_at (key : String) (root : BTreeMap String Toml.Value) : Option (BTreeMap String Toml.Value) :=
    match Toml.table_get key root {
        Option.none => Option.none,
        Option.some v => match Toml.get_table v {
            Result.ok t => Option.some t,
            Result.err _ => Option.none,
        },
    }

def opt_mode (m : Option String) : Option Mode :=
    match m {
        Option.none => Option.none,
        Option.some s => Mode.parse s,
    }

/// The per-server capability overrides: a string -> capability table,
/// every entry validated (`read`/`write`/`exec`/`net`); an invalid
/// value drops that entry, not the whole file.
def caps_of (t : Option (BTreeMap String Toml.Value)) : BTreeMap String Capability :=
    match t {
        Option.none => BTreeMap.empty,
        Option.some tbl => caps_walk (BTreeMap.to_list tbl) BTreeMap.empty,
    }

#[partial]
def caps_walk (entries : List (Pair String Toml.Value)) (acc : BTreeMap String Capability) : BTreeMap String Capability :=
    match entries {
        List.empty => acc,
        List.cons kv rest => caps_walk rest (cap_entry kv acc),
    }

def cap_entry (kv : Pair String Toml.Value) (acc : BTreeMap String Capability) : BTreeMap String Capability :=
    match kv {
        Pair.pair k v => match Toml.get_string v {
            Result.ok s => match parse_cap s {
                Option.some c => Map.insert k c acc,
                Option.none => acc,
            },
            Result.err _ => acc,
        },
    }

/// The capability vocabulary, `/tools`' display names parsed back.
pub def parse_cap (s : String) : Option Capability :=
    if s == "read" then Option.some Capability.read
    else if s == "write" then Option.some Capability.write
    else if s == "exec" then Option.some Capability.exec
    else if s == "net" then Option.some Capability.net
    else Option.none

/// A mounted server's capability override: settings name the server by
/// its `--mcp` executable, so the key is that exact string.
pub def Settings.cap_of (server : String) (s : Settings) : Option Capability :=
    Map.lookup server s.caps
