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
use toml::toml {
    Toml.Value, Toml.ParseError, Toml.parse, Toml.get_string, Toml.get_integer,
    Toml.get_boolean, Toml.get_table, Toml.table_get, Toml.make_string, Toml.make_integer,
    Toml.make_boolean, Toml.to_string,
}
use std::io {IO.get_env, IO.read_file, IO.write_file, IO.file_exists}
use std::stream {StreamError, StreamError.is_not_found}
use std::path {Path, Path.of}
use std::map {Map, BTreeMap, BTreeMap.to_list}
use std::list {List.intercalate}

/// One settings file's worth of knobs -- every field optional, an
/// absent file is simply all-absent.
pub struct Settings {
    mode : Option Mode,
    provider : Option String,
    model : Option String,
    max_turns : Option I64,
    thinking : Option Bool,
    max_tokens : Option I64,
    context_window : Option I64,
    compact_at : Option I64,
    caps : BTreeMap String Capability,
    api_keys : BTreeMap String String,
}

pub def Settings.empty : Settings := {
    mode := Option.none,
    provider := Option.none,
    model := Option.none,
    max_turns := Option.none,
    thinking := Option.none,
    max_tokens := Option.none,
    context_window := Option.none,
    compact_at := Option.none,
    caps := BTreeMap.empty,
    api_keys := BTreeMap.empty,
}

/// Range checks for the numeric knobs the config FILE can set. The slash
/// commands enforce the same ranges (`/settings max_tokens`, `compact_at`);
/// a hand-edited file must not be able to send `max_tokens = 0` (every
/// provider rejects it) or a negative `compact_at` (which silently
/// disables autocompact). `context_window = 0` is legal: it turns
/// autocompact off on purpose.
pub def Settings.validate (s : Settings) : Result String Unit :=
    match s.max_tokens {
        Option.some n =>
            if n < 16
            then Result.err "max_tokens must be at least 16 (use /settings or remove the key)"
            else validate_compact s,
        Option.none => validate_compact s,
    }

def validate_compact (s : Settings) : Result String Unit :=
    match s.compact_at {
        Option.some n =>
            if Bool.or (n < 0) (100 < n)
            then Result.err "compact_at must be between 0 and 100 (use /settings or remove the key)"
            else validate_window s,
        Option.none => validate_window s,
    }

def validate_window (s : Settings) : Result String Unit :=
    match s.context_window {
        Option.some n =>
            if n < 0
            then Result.err "context_window must be 0 (autocompact off) or positive (use /settings or remove the key)"
            else Result.ok unit,
        Option.none => Result.ok unit,
    }

/// The resolution order as a function: `over` wins field by field, the
/// capability tables union with `over`'s entries winning per key.
pub def Settings.merge (base : Settings) (over : Settings) : Settings := {
    mode := merge_opt base.mode over.mode,
    provider := merge_opt base.provider over.provider,
    model := merge_opt base.model over.model,
    max_turns := merge_opt base.max_turns over.max_turns,
    thinking := merge_opt base.thinking over.thinking,
    max_tokens := merge_opt base.max_tokens over.max_tokens,
    context_window := merge_opt base.context_window over.context_window,
    compact_at := merge_opt base.compact_at over.compact_at,
    caps := merge_table base.caps (BTreeMap.to_list over.caps),
    api_keys := merge_table base.api_keys (BTreeMap.to_list over.api_keys),
}

def merge_opt {A : Type} (base : Option A) (over : Option A) : Option A :=
    match over {
        Option.some v => Option.some v,
        Option.none => base,
    }

/// The table union, `over`'s entries winning per key -- the shape both
/// the capability overrides and the api keys resolve through.
#[partial]
def merge_table {A : Type} (base : BTreeMap String A) (entries : List (Pair String A)) : BTreeMap String A :=
    match entries {
        List.empty => base,
        List.cons kv rest => merge_table (tab_insert kv base) rest,
    }

def tab_insert {A : Type} (kv : Pair String A) (acc : BTreeMap String A) : BTreeMap String A :=
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
    project_keys : List String := List.empty,
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
/// warnings concatenate in load order, and the project-file key names
/// ride along (the global file is never the project file).
def merge_loaded (g : Loaded) (p : Loaded) : Loaded := {
    settings := Settings.merge g.settings p.settings,
    warnings := List.append g.warnings p.warnings,
    project_keys := List.append g.project_keys p.project_keys,
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
/// session starts wherever the user launched it. A key that came from
/// HERE is worth a startup line (weaver.md Phase 10): the project file
/// is plaintext in a repo, the deliberate act the entry represents
/// notwithstanding.
pub def Settings.load_project : IO Loaded := do {
    let l <- Settings.load_warned_of ".weaver/config.toml";
    return (mark_project_keys l)
}

def mark_project_keys (l : Loaded) : Loaded :=
    let l2 : Loaded := { l with project_keys := List.map key_name (BTreeMap.to_list l.settings.api_keys) } in
    l2

def key_name (kv : Pair String String) : String :=
    match kv { Pair.pair k _ => k }

/// One file, loaded with its failures visible: a missing path is
/// nothing at all (the absent file contributes nothing and says
/// nothing), an unreadable or unparsable one contributes nothing but
/// warns.
pub def Settings.load_warned_of (path : String) : IO Loaded :=
    match Path.of path {
        Result.err _ => IO.pure Loaded.empty,
        Result.ok p => load_warned_at path p,
    }

def load_warned_at (path : String) (p : Path) : IO Loaded := do {
    let r <- IO.read_file p;
    return (read_warned path r)
}

def read_warned (path : String) (r : Result StreamError String) : Loaded :=
    match r {
        Result.ok text => parse_warned path text,
        Result.err e =>
            if StreamError.is_not_found e
            then Loaded.empty
            else read_failed path e
    }

def read_failed (path : String) (e : StreamError) : Loaded :=
    let w : WeaverError := WeaverError.settings (String.concat "could not read " (String.concat path (String.concat ": " e.message))) in
    let l : Loaded := { settings := Settings.empty, warnings := [w] } in
    l

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
        Result.ok root => parse_loaded path root,
    }

def parse_failed (path : String) (e : Toml.ParseError) : Loaded :=
    let w : WeaverError := WeaverError.settings (String.concat "could not parse " (String.concat path (String.concat ": " (parse_error_show e)))) in
    let l : Loaded := { settings := Settings.empty, warnings := [w] } in
    l

def parse_loaded (path : String) (root : BTreeMap String Toml.Value) : Loaded :=
    let s : Settings := settings_of root in
    let l : Loaded := { settings := s, warnings := unknown_warnings path (unknown_keys (BTreeMap.to_list root) List.empty) } in
    l

/// Every key this mote reads at the top level. The TABLE keys
/// (`mcp_caps`, `api_keys`) hold user-named entries, so only the table
/// names are checked -- their contents are free-form.
pub def Settings.known_keys : List String :=
    ["api_keys", "compact_at", "context_window", "max_tokens", "max_turns", "mcp_caps", "mode", "model", "provider", "thinking"]

#[partial]
def known_key (k : String) (ks : List String) : Bool :=
    match ks {
        List.empty => false,
        List.cons h rest => if h == k then true else known_key k rest,
    }

#[partial]
def unknown_keys (entries : List (Pair String Toml.Value)) (acc : List String) : List String :=
    match entries {
        List.empty => List.reverse acc,
        List.cons kv rest =>
            match kv {
                Pair.pair k _ =>
                    if known_key k Settings.known_keys
                    then unknown_keys rest acc
                    else unknown_keys rest (List.cons k acc),
            },
    }

/// A near-miss suggestion: a known key that this one extends or that
/// extends this one (`api_key` -> `api_keys`, `max_turn` -> `max_turns`).
#[partial]
def suggest_in (k : String) (ks : List String) : Option String :=
    match ks {
        List.empty => Option.none,
        List.cons h rest =>
            if Bool.or (String.starts_with h k) (String.starts_with k h)
            then Option.some h
            else suggest_in k rest,
    }

def unknown_warning (path : String) (k : String) : WeaverError :=
    let hint : String := match suggest_in k Settings.known_keys {
        Option.none => "",
        Option.some s => String.concat " -- did you mean \"" (String.concat s "\"?"),
    } in
    WeaverError.settings (String.concat "unknown config key \"" (String.concat k
        (String.concat "\" in " (String.concat path (String.concat " (known: "
            (String.concat (List.intercalate ", " Settings.known_keys) (String.concat ")" hint)))))))

#[partial]
def unknown_warnings (path : String) (ks : List String) : List WeaverError :=
    match ks {
        List.empty => List.empty,
        List.cons k rest => List.cons (unknown_warning path k) (unknown_warnings path rest),
    }

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
///
/// [api_keys]
/// mistral = "..."
/// ```
///
/// A parse failure is the empty settings (see `Settings.load`); unknown
/// keys are ignored by this pure projection -- a settings file may well
/// hold another tool's keys too -- while the LOADING path
/// (`parse_warned`) reports each one so a typo like `[api_key]` for
/// `[api_keys]` is not silently dead.
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
    thinking := bool_at "thinking" root,
    max_tokens := int_at "max_tokens" root,
    context_window := int_at "context_window" root,
    compact_at := int_at "compact_at" root,
    caps := table_of (table_at "mcp_caps" root) parse_cap,
    api_keys := table_of (table_at "api_keys" root) key_value,
}

/// A TOML table of string values, every entry run through `validate`:
/// a value that is not a string, or one the validator refuses, drops
/// its own entry -- never the file. Both `[mcp_caps]` and `[api_keys]`
/// ride this walk.
def table_of {A : Type} (t : Option (BTreeMap String Toml.Value)) (validate : String -> Option A) : BTreeMap String A :=
    match t {
        Option.none => BTreeMap.empty,
        Option.some tbl => table_walk validate (BTreeMap.to_list tbl) BTreeMap.empty,
    }

#[partial]
def table_walk {A : Type} (validate : String -> Option A) (entries : List (Pair String Toml.Value)) (acc : BTreeMap String A) : BTreeMap String A :=
    match entries {
        List.empty => acc,
        List.cons kv rest => table_walk validate rest (table_entry validate kv acc),
    }

def table_entry {A : Type} (validate : String -> Option A) (kv : Pair String Toml.Value) (acc : BTreeMap String A) : BTreeMap String A :=
    match kv {
        Pair.pair k v => match Toml.get_string v {
            Result.ok s => match validate s {
                Option.some a => Map.insert k a acc,
                Option.none => acc,
            },
            Result.err _ => acc,
        },
    }

def str_at (key : String) (root : BTreeMap String Toml.Value) : Option String :=
    match Toml.table_get key root {
        Option.none => Option.none,
        Option.some v => match Toml.get_string v {
            Result.ok s => Option.some s,
            Result.err _ => Option.none,
        },
    }

def bool_at (key : String) (root : BTreeMap String Toml.Value) : Option Bool :=
    match Toml.table_get key root {
        Option.none => Option.none,
        Option.some v => match Toml.get_boolean v {
            Result.ok b => Option.some b,
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

/// The capability vocabulary, `/tools`' display names parsed back.
pub def parse_cap (s : String) : Option Capability :=
    if s == "read" then Option.some Capability.read
    else if s == "write" then Option.some Capability.write
    else if s == "exec" then Option.some Capability.exec
    else if s == "net" then Option.some Capability.net
    else Option.none

/// The `[api_keys]` validator: any string is a key -- except the empty
/// one, which says nothing and stays unsaid (an empty bearer header is
/// worse than no key at all).
def key_value (s : String) : Option String :=
    if String.is_empty s then Option.none else Option.some s

/// A mounted server's capability override: settings name the server by
/// its `--mcp` executable, so the key is that exact string.
pub def Settings.cap_of (server : String) (s : Settings) : Option Capability :=
    Map.lookup server s.caps

/// A provider's settings-stored key, when the file(s) spoke for it:
/// the value that lands in the config as the DIRECT key, and therefore
/// wins over the env var at send time (Design 8 -- the file entry is
/// the more deliberate act).
pub def Settings.key_of (provider : String) (s : Settings) : Option String :=
    Map.lookup provider s.api_keys

// ── Saving (the /settings dialog's explicit targets) ───────────────────
// Only the NAMED values are written; everything else in the target file
// (unknown keys, [mcp_caps], an [api_keys] table already there) survives
// because the parsed document is re-rendered rather than replaced. A
// file that fails to parse is never overwritten -- losing a user's config
// to a typo is worse than refusing the save.

pub struct SettingsUpdate {
    mode : Option String,
    provider : Option String,
    model : Option String,
    max_turns : Option I64,
    thinking : Option Bool,
    max_tokens : Option I64,
    context_window : Option I64,
    compact_at : Option I64,
}

pub def Settings.project_file : String := ".weaver/config.toml"

pub def Settings.target_file (target : String) : IO (Result String String) := do {
    if target == "global"
    then do {
        let home <- IO.get_env "HOME";
        match home {
            Option.none => IO.pure (Result.err "HOME is unset; cannot find the global config"),
            Option.some h => IO.pure (Result.ok (String.concat h "/.weaver/config.toml")),
        }
    }
    else if target == "project"
    then IO.pure (Result.ok Settings.project_file)
    else IO.pure (Result.err "unknown settings target: project | global")
}

/// The pure half of a save: parse the existing document (if any),
/// apply the update, render it back. An unparsable file is REFUSED, not
/// replaced -- losing a config to a typo is worse than a failed save.
pub def Settings.render_update (existing : String) (u : SettingsUpdate) : Result String String :=
    if String.is_empty existing
    then Result.ok (Toml.to_string (apply_update u BTreeMap.empty))
    else match Toml.parse existing {
        Result.err _ => Result.err "the existing config is not valid TOML; refusing to overwrite it",
        Result.ok root => Result.ok (Toml.to_string (apply_update u root)),
    }

pub def Settings.save (target : String) (u : SettingsUpdate) : IO (Result String String) := do {
    let tf <- Settings.target_file target;
    match tf {
        Result.err e => IO.pure (Result.err e),
        Result.ok path => do {
            let text_r <- read_text path;
            match text_r {
                Result.err e => IO.pure (Result.err e),
                Result.ok existing =>
                    match Settings.render_update existing u {
                        Result.err e => IO.pure (Result.err e),
                        Result.ok out => write_update path target out,
                    },
            }
        }
    }
}

def read_text (path : String) : IO (Result String String) := do {
    let p : Path := Path.path path;
    let exists <- IO.file_exists p;
    if Bool.not exists
    then IO.pure (Result.ok "")
    else do {
        let r <- IO.read_file p;
        match r {
            Result.err _ => IO.pure (Result.err (String.concat "could not read " path)),
            Result.ok text => IO.pure (Result.ok text),
        }
    }
}

def put_string (key : String) (v : Option String) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
    match v {
        Option.none => root,
        Option.some s => Map.insert key (Toml.make_string s) root,
    }

def put_integer (key : String) (v : Option I64) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
    match v {
        Option.none => root,
        Option.some n => Map.insert key (Toml.make_integer n) root,
    }

def put_boolean (key : String) (v : Option Bool) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
    match v {
        Option.none => root,
        Option.some b => Map.insert key (Toml.make_boolean b) root,
    }

def apply_update (u : SettingsUpdate) (root : BTreeMap String Toml.Value) : BTreeMap String Toml.Value :=
    let r1 : BTreeMap String Toml.Value := put_string "mode" u.mode root in
    let r2 : BTreeMap String Toml.Value := put_string "provider" u.provider r1 in
    let r3 : BTreeMap String Toml.Value := put_string "model" u.model r2 in
    let r4 : BTreeMap String Toml.Value := put_integer "max_turns" u.max_turns r3 in
    let r5 : BTreeMap String Toml.Value := put_boolean "thinking" u.thinking r4 in
    let r6 : BTreeMap String Toml.Value := put_integer "max_tokens" u.max_tokens r5 in
    let r7 : BTreeMap String Toml.Value := put_integer "context_window" u.context_window r6 in
    put_integer "compact_at" u.compact_at r7

def write_update (path : String) (target : String) (out : String) : IO (Result String String) := do {
    let r <- IO.write_file (Path.path path) out;
    match r {
        Result.err _ => IO.pure (Result.err (String.concat "could not write "
            (String.concat path " (does its directory exist?)"))),
        Result.ok _ => IO.pure (Result.ok (String.concat "settings saved to "
            (String.concat target (String.concat ": " path)))),
    }
}
