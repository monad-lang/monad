// lang / lock -- `mote.lock`: read, validate and render it.
//
// It lives in `lang` and not `build` because the LOADER has to read it to
// locate a git dependency, and `lang` cannot depend on `build`; the
// writing side (`monad fetch`) reaches it from `build` as a dependency of
// this one.
//
// The format is plans/packaging/package-system.md §2b. One `[[mote]]` entry
// per resolved dependency; a git entry carries the STRUCTURED `git_*` keys,
// which are what a resolver reads, plus a `source` line that is only for
// people -- it is rendered from the structured keys and never parsed back,
// so a URL holding `?`, `#` or `&` never has to be split out of a string.
//
// Reading is strict where a wrong answer would build the wrong thing: a
// missing name or checksum, a commit that is not a full hex id, or a pin that
// names no known kind is an error naming the entry. A lockfile `version`
// other than this module's is NOT an error: `Lock.parse` answers
// `LockRead.unsupported` so the caller can warn and regenerate, which is the
// package-system lockfile-versioning rule. Unknown keys inside an entry are
// ignored, so an older reader tolerates a newer writer's additions.
//
// Rendering is deterministic: entries sorted by name (then version, then
// commit), keys in the §2b order, so the same resolution always writes the
// same bytes and a diff of a committed `mote.lock` shows only real changes.

use std::io {}
use std::list {List.filter, List.sort_by}
use std::map {BTreeMap}
use std::stream {StreamError, StreamError.is_not_found}
use toml::toml {
  Toml.ParseError.to_string, Toml.Value, Toml.array_at, Toml.parse, Toml.table_get,
  Toml.value_to_string,
}

/// What a git entry was asked to follow. `head` is the remote's default
/// branch: a dependency that named no `tag`, `branch` or `rev`.
pub type GitPin {
    tag (name : String),
    branch (name : String),
    rev (id : String),
    head,
}

/// The git half of a lock entry. `commit` is always a full id: a tag or
/// branch is resolved once, by `monad fetch`, and never moves afterwards.
pub struct LockedGit {
    url : String,
    pin : GitPin,
    commit : String,
    subdir : Option String,
}

/// One `[[mote]]` entry. `checksum` is `sha256:<hex>` over the canonical
/// tree digest of the mote's directory (§2b). `git` is `none` for a source
/// that is not a git checkout.
pub struct LockedMote {
    name : String,
    version : String,
    checksum : String,
    git : Option LockedGit,
}

pub struct Lockfile {
    motes : List LockedMote,
}

/// A successfully read `mote.lock`: either one this reader understands, or
/// the `version` it does not -- which the caller warns about and
/// regenerates rather than failing on.
pub type LockRead {
    loaded (lock : Lockfile),
    unsupported (version : I64),
}

/// Every `string` key an entry understands. A present key of another type
/// is an error rather than an absent one, the same rule `lang/src/mote.mo`
/// applies to dependency tables.
struct LockFields {
    name : Option String,
    version : Option String,
    checksum : Option String,
    git_url : Option String,
    git_ref : Option String,
    git_commit : Option String,
    git_subdir : Option String,
}

with Lock {
    /// The lockfile format this module reads and writes.
    pub def format_version : I64 := 1

    /// Parse `mote.lock` text. `err` carries a message naming what is wrong.
    #[partial]
    pub def parse (text : String) : Result String LockRead :=
        match Toml.parse text {
            Result.err e => err (String.concat "mote.lock is not valid TOML: " (Toml.ParseError.to_string e)),
            Result.ok root => Lock.of_root root,
        }

    def of_root (root : BTreeMap String Toml.Value) : Result String LockRead :=
        match Toml.table_get "version" root {
            Option.none => err "mote.lock has no `version`",
            Option.some v => match v {
                Toml.Value.integer n =>
                    if n == Lock.format_version
                    then Lock.loaded_of (Lock.entries_of root)
                    else ok (LockRead.unsupported n),
                _ => err "mote.lock `version` must be an integer",
            }
        }

    def loaded_of (r : Result String (List LockedMote)) : Result String LockRead :=
        match r {
            Result.err e => err e,
            Result.ok motes =>
                let lock : Lockfile := { motes := motes } in
                ok (LockRead.loaded lock),
        }

    /// `mote` absent is an empty lock; present, it must be the `[[mote]]`
    /// array -- a single `[mote]` table is a hand edit gone wrong, and
    /// reading it as "no entries" would quietly unlock everything.
    def entries_of (root : BTreeMap String Toml.Value) : Result String (List LockedMote) :=
        match Toml.table_get "mote" root {
            Option.none => ok List.empty,
            Option.some v => match v {
                Toml.Value.array _ => Lock.entries_go 1 (Toml.array_at "mote" root),
                _ => err "mote.lock `mote` must be an array of tables (`[[mote]]`)",
            }
        }

    #[partial]
    def entries_go (i : I64) (xs : List Toml.Value) : Result String (List LockedMote) :=
        match xs {
            List.empty => ok List.empty,
            List.cons x rest => Lock.cons_entry (Lock.entry_of_value i x) (Lock.entries_go (i + 1) rest),
        }

    def cons_entry (here : Result String LockedMote) (later : Result String (List LockedMote)) : Result String (List LockedMote) :=
        match here {
            Result.err e => err e,
            Result.ok m => Lock.cons_onto m later,
        }

    def cons_onto (m : LockedMote) (later : Result String (List LockedMote)) : Result String (List LockedMote) :=
        match later {
            Result.err e => err e,
            Result.ok ms => ok (List.cons m ms),
        }

    def entry_of_value (i : I64) (v : Toml.Value) : Result String LockedMote :=
        match v {
            Toml.Value.table t => Lock.entry_of_table i t,
            _ => err (String.concat (Lock.entry_label i Option.none) " is not a table"),
        }

    def entry_of_table (i : I64) (t : BTreeMap String Toml.Value) : Result String LockedMote :=
        match List.filter (fn (key : String) => Lock.key_not_string t key) Lock.string_keys {
            List.cons key _ => err (String.concat (String.concat (String.concat
                (Lock.entry_label i (Lock.string_at t "name")) ": `") key) "` must be a string"),
            List.empty => Lock.entry_of_fields i (Lock.fields_of t),
        }

    def string_keys : List String :=
        ["name", "version", "checksum", "source", "git_url", "git_ref", "git_commit", "git_subdir"]

    def key_not_string (t : BTreeMap String Toml.Value) (key : String) : Bool :=
        match Toml.table_get key t {
            Option.none => false,
            Option.some v => match v {
                Toml.Value.string _ => false,
                _ => true,
            }
        }

    def string_at (t : BTreeMap String Toml.Value) (key : String) : Option String :=
        match Toml.table_get key t {
            Option.none => Option.none,
            Option.some v => match v {
                Toml.Value.string s => Option.some s,
                _ => Option.none,
            }
        }

    def fields_of (t : BTreeMap String Toml.Value) : LockFields :=
        let f : LockFields := {
            name := Lock.string_at t "name",
            version := Lock.string_at t "version",
            checksum := Lock.string_at t "checksum",
            git_url := Lock.string_at t "git_url",
            git_ref := Lock.string_at t "git_ref",
            git_commit := Lock.string_at t "git_commit",
            git_subdir := Lock.string_at t "git_subdir",
        } in
        f

    /// `mote.lock entry 3` before the name is known, `mote.lock entry
    /// `http`` after -- whichever a reader can find in the file.
    def entry_label (i : I64) (name : Option String) : String :=
        match name {
            Option.some n => String.concat (String.concat "mote.lock entry `" n) "`",
            Option.none => String.concat "mote.lock entry " (I64.to_string i),
        }

    def entry_of_fields (i : I64) (f : LockFields) : Result String LockedMote :=
        match f.name {
            Option.none => err (String.concat (Lock.entry_label i Option.none) ": missing `name`"),
            Option.some name => Lock.entry_named name f,
        }

    def entry_named (name : String) (f : LockFields) : Result String LockedMote :=
        match f.version {
            Option.none => err (Lock.entry_error name "missing `version`"),
            Option.some version => match f.checksum {
                Option.none => err (Lock.entry_error name "missing `checksum`"),
                Option.some checksum =>
                    if Lock.is_checksum checksum
                    then Lock.entry_with_git name version checksum (Lock.git_of name f)
                    else err (Lock.entry_error name "`checksum` must be `sha256:` followed by 64 lowercase hex digits"),
            }
        }

    def entry_error (name : String) (what : String) : String :=
        String.concat (String.concat (Lock.entry_label 0 (Option.some name)) ": ") what

    def entry_with_git (name : String) (version : String) (checksum : String) (g : Result String (Option LockedGit)) : Result String LockedMote :=
        match g {
            Result.err e => err e,
            Result.ok git =>
                let m : LockedMote := { name := name, version := version, checksum := checksum, git := git } in
                ok m,
        }

    /// No `git_*` key at all is a non-git entry. Any one of them makes it a
    /// git entry, and then `git_url`, `git_ref` and `git_commit` are all
    /// required: a half-written git entry has no safe reading.
    def git_of (name : String) (f : LockFields) : Result String (Option LockedGit) :=
        if Lock.no_git_keys f
        then ok Option.none
        else match f.git_url {
            Option.none => err (Lock.entry_error name "a git entry needs `git_url`"),
            Option.some url => match f.git_commit {
                Option.none => err (Lock.entry_error name "a git entry needs `git_commit`"),
                Option.some commit =>
                    if Lock.is_commit commit
                    then Lock.git_with_pin name url commit f
                    else err (Lock.entry_error name "`git_commit` must be a full commit id (40 or 64 lowercase hex digits)"),
            }
        }

    def git_with_pin (name : String) (url : String) (commit : String) (f : LockFields) : Result String (Option LockedGit) :=
        match Lock.pin_of (Option.get_or_default "" f.git_ref) {
            Option.none => err (Lock.entry_error name "`git_ref` must be `tag:<name>`, `branch:<name>`, `rev:<id>` or `head`"),
            Option.some pin =>
                let g : LockedGit := { url := url, pin := pin, commit := commit, subdir := f.git_subdir } in
                ok (Option.some g),
        }

    def no_git_keys (f : LockFields) : Bool :=
        Lock.absent f.git_url && Lock.absent f.git_ref && Lock.absent f.git_commit && Lock.absent f.git_subdir

    def absent (o : Option String) : Bool :=
        match o {
            Option.none => true,
            Option.some _ => false,
        }

    /// `tag:<name>` / `branch:<name>` / `rev:<id>` / `head`. An empty name
    /// is no pin at all, so it is rejected with the rest.
    pub def pin_of (s : String) : Option GitPin :=
        if String.beq s "head" then Option.some GitPin.head
        else if String.starts_with "tag:" s then Lock.named_pin (fn (n : String) => GitPin.tag n) (String.drop 4 s)
        else if String.starts_with "branch:" s then Lock.named_pin (fn (n : String) => GitPin.branch n) (String.drop 7 s)
        else if String.starts_with "rev:" s then Lock.named_pin (fn (n : String) => GitPin.rev n) (String.drop 4 s)
        else Option.none

    // The constructors are wrapped in lambdas, not passed bare: compiled, a
    // bare `GitPin.tag` VALUE builds the wrong constructor, so `pin_of
    // "tag:v1"` answered `head` (the Rust host was right). Applied directly,
    // `GitPin.tag n` is fine. Filed as
    // plans/implementations/constructor-value-name-collision.md.
    def named_pin (mk : String -> GitPin) (rest : String) : Option GitPin :=
        if String.is_empty rest then Option.none else Option.some (mk rest)

    /// `git_ref`'s spelling of a pin; the inverse of `pin_of`.
    pub def pin_to_string (p : GitPin) : String :=
        match p {
            GitPin.tag n => String.concat "tag:" n,
            GitPin.branch n => String.concat "branch:" n,
            GitPin.rev id => String.concat "rev:" id,
            GitPin.head => "head",
        }

    def is_checksum (s : String) : Bool :=
        String.starts_with "sha256:" s && Lock.is_hex_of_length (String.drop 7 s) 64

    /// SHA-1 repositories have 40-digit ids, SHA-256 ones 64. Public
    /// because `build::git` resolves a `rev` against exactly this rule --
    /// one definition, so a commit the lock accepts is a commit the
    /// transport will look up.
    pub def is_commit (s : String) : Bool :=
        Lock.is_hex_of_length s 40 || Lock.is_hex_of_length s 64

    def is_hex_of_length (s : String) (n : I64) : Bool :=
        String.length s == n && Lock.is_hex_from s 0 n

    #[partial]
    def is_hex_from (s : String) (i : I64) (n : I64) : Bool :=
        if i == n then true
        else String.contains "0123456789abcdef" (String.slice s i 1) && Lock.is_hex_from s (i + 1) n

    // ─── Rendering ───

    /// The lockfile's text. Deterministic for a given set of entries,
    /// whatever order they arrive in.
    #[partial]
    pub def render (lock : Lockfile) : String :=
        String.concat (String.concat (String.concat
            "# mote.lock -- written by `monad fetch` / `monad update`. Do not edit by hand.\nversion = "
            (I64.to_string Lock.format_version)) "\n")
            (Lock.render_entries (List.sort_by Lock.entry_lt lock.motes))

    #[partial]
    def render_entries (ms : List LockedMote) : String :=
        match ms {
            List.empty => "",
            List.cons m rest => String.concat (Lock.render_entry m) (Lock.render_entries rest),
        }

    #[partial]
    def render_entry (m : LockedMote) : String :=
        String.concat (String.concat (String.concat (String.concat
            "\n[[mote]]\n" (Lock.kv "name" m.name)) (Lock.kv "version" m.version))
            (Lock.render_git m.git)) (Lock.kv "checksum" m.checksum)

    #[partial]
    def render_git (g : Option LockedGit) : String :=
        match g {
            Option.none => "",
            Option.some git => String.concat (String.concat (String.concat (String.concat
                (Lock.kv "source" (Lock.source_of git)) (Lock.kv "git_url" git.url))
                (Lock.kv "git_ref" (Lock.pin_to_string git.pin))) (Lock.kv "git_commit" git.commit))
                (Lock.render_subdir git.subdir),
        }

    #[partial]
    def render_subdir (subdir : Option String) : String :=
        match subdir {
            Option.none => "",
            Option.some d => Lock.kv "git_subdir" d,
        }

    #[partial]
    def kv (key : String) (value : String) : String :=
        String.concat (String.concat (String.concat key " = ") (Toml.value_to_string (Toml.Value.string value))) "\n"

    /// `git+<url>?tag=v1&subdir=x#<commit>`: the display spelling only.
    pub def source_of (g : LockedGit) : String :=
        String.concat (String.concat (String.concat (String.concat "git+" g.url)
            (Lock.source_query (Lock.pin_param g.pin) g.subdir)) "#") g.commit

    def pin_param (p : GitPin) : Option String :=
        match p {
            GitPin.tag n => Option.some (String.concat "tag=" n),
            GitPin.branch n => Option.some (String.concat "branch=" n),
            GitPin.rev id => Option.some (String.concat "rev=" id),
            GitPin.head => Option.none,
        }

    def source_query (pin : Option String) (subdir : Option String) : String :=
        match pin {
            Option.none => match subdir {
                Option.none => "",
                Option.some d => String.concat "?subdir=" d,
            },
            Option.some p => match subdir {
                Option.none => String.concat "?" p,
                Option.some d => String.concat (String.concat (String.concat "?" p) "&subdir=") d,
            }
        }

    def entry_lt (a : LockedMote) (b : LockedMote) : Bool :=
        if String.lt a.name b.name then true
        else if String.lt b.name a.name then false
        else if String.lt a.version b.version then true
        else if String.lt b.version a.version then false
        else String.lt (Lock.commit_of a) (Lock.commit_of b)

    def commit_of (m : LockedMote) : String :=
        match m.git {
            Option.none => "",
            Option.some g => g.commit,
        }

    // ─── Files ───

    /// Read the lockfile at `path`: `none` when there is none (the ordinary
    /// first-fetch case), `err` when it exists but cannot be read or parsed.
    #[partial]
    pub def read (path : Path) : IO (Result String (Option LockRead)) := do {
        let r <- IO.read_file path;
        return (Lock.of_read path r)
    }

    #[partial]
    def of_read (path : Path) (r : Result StreamError String) : Result String (Option LockRead) :=
        match r {
            Result.err e =>
                if StreamError.is_not_found e
                then ok Option.none
                else err (String.concat (String.concat (String.concat "reading " (Path.to_string path)) ": ") e.message),
            Result.ok text => Lock.some_read (Lock.parse text),
        }

    def some_read (r : Result String LockRead) : Result String (Option LockRead) :=
        match r {
            Result.err e => err e,
            Result.ok l => ok (Option.some l),
        }

    /// Write `lock` to `path`, replacing whatever is there.
    #[partial]
    pub def write (path : Path) (lock : Lockfile) : IO (Result String Unit) := do {
        let r <- IO.write_file path (Lock.render lock);
        return (Lock.of_write path r)
    }

    def of_write (path : Path) (r : Result StreamError Unit) : Result String Unit :=
        match r {
            Result.err e => err (String.concat (String.concat (String.concat "writing " (Path.to_string path)) ": ") e.message),
            Result.ok u => ok u,
        }
}
