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
use weaver::error {WeaverError}
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

/// The loaded settings: the resolved knobs PLUS the per-file parse
/// failures that were swallowed on the way. Phase 9's contract: the
/// empty-settings-on-parse-error BEHAVIOR stands (an interactive tool
/// must start, not refuse, over its own config), but the silence does
/// not -- each unparsable file contributes a `settings`-tagged warning
/// naming it, and the UI prints the warnings at startup. All the
/// warnings are recoverable by construction.
pub struct Loaded {
    settings : Settings,
    warnings : List WeaverError,
}

pub def Loaded.empty : Loaded := {
    settings := Settings.empty,
    warnings := List.empty,
}

/// The resolved settings: the global file under the project file, with
/// whatever either file failed to say riding alongside as warnings.
pub def Settings.load : IO Loaded := do {
    let g <- Settings.load_global;
    let p <- Settings.load_project;
    return (merge_loaded g p)
}

/// The resolution order's last step: settings merge field by field,
/// warnings concatenate in load order.
def merge_loaded (g : Loaded) (p : Loaded) : Loaded := {
    settings := Settings.merge g.settings p.settings,
    warnings := List.append g.warnings p.warnings,
}

pub def Settings.load_global : IO Loaded :=
    load_home

def load_home : IO Loaded := do {
    let home <- IO.get_env "HOME";
    home_settings home
}

def home_settings (home : Option String) : IO Loaded :=
    match home {
        Option.none => IO.pure Loaded.empty,
        Option.some h => Settings.load_warned_of (String.concat h "/.weaver/config.toml"),
    }

/// The project file is relative to the working directory -- Weaver's
/// session starts wherever the user launched it.
pub def Settings.load_project : IO Loaded :=
    Settings.load_warned_of ".weaver/config.toml"

/// One file, loaded with its failures visible: a missing or unreadable
/// path is nothing at all (the absent file contributes nothing and
/// says nothing), an unparsable one contributes nothing but warns.
pub def Settings.load_warned_of (path : String) : IO Loaded :=
    match Path.of path {
        Result.err _ => IO.pure Loaded.empty,
        Result.ok p => load_warned_at path p,
    }

def load_warned_at (path : String) (p : Path) : IO Loaded := do {
    let exists <- IO.file_exists p;
    if Bool.not exists
    then IO.pure Loaded.empty
    else do {
        let text <- IO.read_file p;
        return (parse_warned path text)
    }
}

/// The settings-only projection -- the phase 6 contract (`load_of_path`
/// stays `IO Settings`), for callers that do not surface warnings.
pub def Settings.load_of_path (path : String) : IO Settings := do {
    let l <- Settings.load_warned_of path;
    return (l.settings)
}

/// The pure half of the visibility: a parse failure contributes the
/// empty settings (exactly `parse_settings`'s contract) and a
/// `settings`-tagged warning naming the file; a good file contributes
/// its keys and no warnings.
pub def parse_warned (path : String) (text : String) : Loaded :=
    match Toml.parse text {
        Result.err e => parse_failed path e,
        Result.ok root => parse_loaded root,
    }

def parse_failed (path : String) (e : Toml.ParseError) : Loaded :=
    let w : WeaverError := WeaverError.settings (String.concat "could not parse " (String.concat path (String.concat ": " (parse_error_show e)))) in
    let l : Loaded := { settings := Settings.empty, warnings := [w] } in
    l

def parse_loaded (root : BTreeMap String Toml.Value) : Loaded :=
    let s : Settings := settings_of root in
    let l : Loaded := { settings := s, warnings := List.empty } in
    l

/// `toml`'s own `to_string` is package-private to that mote, so the
/// warning renders the shape here -- `show` stays Weaver's one render
/// point; this is the detail it renders.
def parse_error_show (e : Toml.ParseError) : String :=
    match e {
        Toml.ParseError.expected x f => String.concat "expected " (String.concat x (String.concat ", found " f)),
        Toml.ParseError.generic s => s,
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
