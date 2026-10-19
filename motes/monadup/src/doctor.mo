/// `monadup doctor` and `doctor --json`.
///
/// The observable state is gathered once into `Doctor.Env`; `Doctor.checks`
/// is pure, so every check is unit-testable against a synthetic
/// environment. Checks 4/8/9 mirror exactly what the compiler's
/// `Mote.toolchain_root` / `toolchain_missing_hint` require, so doctor and
/// compiler diagnostics never disagree.
use std::list {List.length}
use std::process {Proc.capture}
use std::io {IO.get_env}
use json::json {
    Json, Json.make_null, Json.make_bool, Json.make_num_int, Json.make_str,
    Json.make_array, Json.make_object_pairs, Json.to_string,
}
use lib::platform {*}
use lib::text {*}
use lib::layout {*}
use lib::release {*}
use lib::shell {*}
use lib::install {*}

pub type Doctor.Status {
    st_ok,
    st_warn,
    st_fail,
}

pub struct Doctor.Check {
    name : String,
    status : Doctor.Status,
    detail : String,
    hint : String,
}

pub struct Doctor.Tools {
    curl : Bool,
    tar : Bool,
    llc : Bool,
    clang : Bool,
    pkg_config : Bool,
    bdw_gc : Bool,
}

pub struct Doctor.Env {
    platform : Platform.Resolution,
    home : Layout.Home,
    home_exists : Bool,
    home_writable : Bool,
    active : Option String,
    active_dir_exists : Bool,
    binary : Option String,
    binary_exec : Bool,
    commit : Option String,
    binary_version : Option String,
    sources : List String,
    root_manifest : Bool,
    monad_link : Option String,
    monad_link_ok : Bool,
    link_is_symlink : Bool,
    path_has_bin : Bool,
    overrides : List (Pair String String),
    monad_root_bad : Bool,
    api_ok : Bool,
    downloads : List String,
    tools : Doctor.Tools,
    no_network : Bool,
}

pub def Doctor.check (name : String) (status : Doctor.Status) (detail : String) (hint : String) : Doctor.Check :=
    let c : Doctor.Check := { name := name, status := status, detail := detail, hint := hint } in c

pub def Doctor.status_text (s : Doctor.Status) : String :=
    match s { Doctor.Status.st_ok => "ok", Doctor.Status.st_warn => "warn", Doctor.Status.st_fail => "fail" }

def Doctor.status_ok (s : Doctor.Status) : Bool :=
    match s { Doctor.Status.st_ok => true, _ => false }

// ─── Gathering ─────────────────────────────────────────────────────────

#[partial]
def Doctor.nightly_entries (entries : List String) : List String :=
    match entries {
        List.empty => List.empty,
        List.cons e rest =>
            if String.starts_with "nightly-" e
            then List.cons e (Doctor.nightly_entries rest)
            else Doctor.nightly_entries rest,
    }

#[partial]
def Doctor.collect_sources (dir : String) (names : List String) : IO (List String) := do {
    match names {
        List.empty => return List.empty,
        List.cons n rest => do {
            let present <- Shell.is_dir (String.concat dir (String.concat "/" n));
            let tail <- Doctor.collect_sources dir rest;
            if present then return (List.cons n tail) else return tail
        },
    }
}

#[partial]
def Doctor.collect_overrides (items : List String) : IO (List (Pair String String)) := do {
    match items {
        List.empty => return List.empty,
        List.cons name rest => do {
            let v <- IO.get_env name;
            let tail <- Doctor.collect_overrides rest;
            match v {
                Option.none => return tail,
                Option.some raw =>
                    let t : String := Text.trim raw in
                    if String.is_empty t then return tail
                    else return (List.cons (Pair.pair name t) tail),
            }
        },
    }
}

#[partial]
def Doctor.first_env (names : List String) : IO (Option String) := do {
    match names {
        List.empty => return Option.none,
        List.cons n rest => do {
            let v <- IO.get_env n;
            match v {
                Option.some raw =>
                    let t : String := Text.trim raw in
                    if String.is_empty t then Doctor.first_env rest else return (Option.some t),
                Option.none => Doctor.first_env rest,
            }
        },
    }
}

pub def Doctor.gather (no_network : Bool) : IO Doctor.Env := do {
    let ctx <- Install.context;
    let h : Layout.Home := ctx.home;
    let pf : String := ctx.platform.platform;
    let active <- Install.active_tag h;
    let active_dir : String :=
        match active {
            Option.some tag => Layout.version_dir h tag,
            Option.none => "",
        };
    let active_dir_exists <-
        if String.is_empty active_dir then return false else Shell.is_dir active_dir;
    let entries <-
        if active_dir_exists then Shell.list_dir active_dir else return List.empty;
    let binary : Option String := Layout.find_nightly_binary entries;
    let binary_path : String :=
        match binary {
            Option.some b => String.concat active_dir (String.concat "/" b),
            Option.none => "",
        };
    let binary_exec <-
        if String.is_empty binary_path then return false else Shell.is_executable binary_path;
    let commit_path : String :=
        match active {
            Option.some tag => Layout.commit_file h tag,
            Option.none => "",
        };
    let commit_exists <-
        if String.is_empty commit_path then return false else Shell.file_exists commit_path;
    let commit <-
        if commit_exists then do {
            let raw <- Shell.read_file commit_path;
            return (Option.some (Text.trim raw))
        } else return Option.none;
    let binary_version <-
        if binary_exec then Shell.capture_line binary_path ["version"] else return Option.none;
    let sources <-
        if active_dir_exists then Doctor.collect_sources active_dir Layout.source_names else return List.empty;
    let root_manifest <-
        if active_dir_exists then Shell.file_exists (String.concat active_dir "/mote.toml") else return false;
    let link <- Shell.readlink (Layout.monad_link h);
    let link_is_symlink <- Shell.is_symlink (Layout.monad_link h);
    let link_ok <- Shell.file_exists (Layout.monad_link h);
    let home_exists <- Shell.is_dir h.path;
    let home_writable <-
        if home_exists then Shell.is_writable h.path else return true;
    let path_has_bin <- Shell.path_has (Layout.bin_dir h);
    let overrides <- Doctor.collect_overrides ["MONAD_HOME", "MONAD_ROOT", "MONADUP_API_URL", "MONADUP_UNAME"];
    let root <- IO.get_env "MONAD_ROOT";
    let root_bad <-
        match root {
            Option.none => return false,
            Option.some raw =>
                let t : String := Text.trim raw in
                if String.is_empty t then return false
                else do {
                    let isdir <- Shell.is_dir t;
                    return (Bool.not isdir)
                },
        };
    let api_ok <-
        if no_network then return true
        else if String.starts_with "file://" ctx.api_url then return true
        else do {
            let code <- Shell.curl_head ctx.api_url;
            return (I64.beq code 0)
        };
    let dl_dir : String := Layout.downloads h;
    let dl_exists <- Shell.is_dir dl_dir;
    let downloads <-
        if dl_exists then do {
            let es <- Shell.list_dir dl_dir;
            return (Text.sort (Doctor.nightly_entries es))
        } else return List.empty;
    let curl <- Shell.tool_exists "curl";
    let tar <- Shell.tool_exists "tar";
    let llc <- Shell.tool_exists "llc";
    let clang <- Shell.tool_exists "clang";
    let pkg_config <- Shell.tool_exists "pkg-config";
    let gc <- Proc.capture "pkg-config" ["--exists", "bdw-gc"];
    let bdw_gc <-
        match gc {
            Pair.pair code _ => return (I64.beq code 0),
        };
    let tools : Doctor.Tools := {
        curl := curl,
        tar := tar,
        llc := llc,
        clang := clang,
        pkg_config := pkg_config,
        bdw_gc := bdw_gc,
    };
    let env : Doctor.Env := {
        platform := ctx.platform,
        home := h,
        home_exists := home_exists,
        home_writable := home_writable,
        active := active,
        active_dir_exists := active_dir_exists,
        binary := binary,
        binary_exec := binary_exec,
        commit := commit,
        binary_version := binary_version,
        sources := sources,
        root_manifest := root_manifest,
        monad_link := link,
        monad_link_ok := link_ok,
        link_is_symlink := link_is_symlink,
        path_has_bin := path_has_bin,
        overrides := overrides,
        monad_root_bad := root_bad,
        api_ok := api_ok,
        downloads := downloads,
        tools := tools,
        no_network := no_network,
    };
    return env
}

// ─── Checks (pure) ─────────────────────────────────────────────────────

pub def Doctor.checks (e : Doctor.Env) : List Doctor.Check := [
    Doctor.tool_check "curl" e.tools.curl "curl is required to download releases",
    Doctor.tool_check "tar" e.tools.tar "tar is required to unpack the sources asset",
    Doctor.platform_check e,
    Doctor.home_check e,
    Doctor.active_check e,
    Doctor.binary_check e,
    Doctor.commit_check e,
    Doctor.runs_check e,
    Doctor.sources_check e,
    Doctor.link_check e,
    Doctor.path_check e,
    Doctor.overrides_check e,
    Doctor.api_check e,
    Doctor.downloads_check e,
    Doctor.tool_check "llc" e.tools.llc "install LLVM (the compiler invokes bare `llc` to build programs)",
    Doctor.tool_check "clang" e.tools.clang "install clang (the compiler invokes bare `clang` to build programs)",
    Doctor.tool_check "pkg-config" e.tools.pkg_config "install pkg-config (needed for `[link] pkg-config` motes and Darwin Boehm GC discovery)",
    Doctor.tool_check "boehm-gc" e.tools.bdw_gc "install Boehm GC development files (libgc-dev / gc-devel / bdw-gc)",
]

def Doctor.tool_check (name : String) (present : Bool) (hint : String) : Doctor.Check :=
    if present
    then Doctor.check name Doctor.Status.st_ok (String.concat name " found") ""
    else Doctor.check name Doctor.Status.st_fail (String.concat name " not found") hint

def Doctor.home_check (e : Doctor.Env) : Doctor.Check :=
    let suffix : String := if e.home_exists then ")" else ", will be created)" in
    let detail : String := String.concat e.home.path (String.concat " (" (String.concat e.home.source suffix)) in
    if e.home_exists && Bool.not e.home_writable
    then Doctor.check "home" Doctor.Status.st_fail (String.concat detail " is not writable")
        (String.concat "make " (String.concat e.home.path " writable (or point MONAD_HOME elsewhere)"))
    else Doctor.check "home" Doctor.Status.st_ok detail ""

def Doctor.platform_check (e : Doctor.Env) : Doctor.Check :=
    if String.is_empty e.platform.uname_sm
    then Doctor.check "platform" Doctor.Status.st_fail e.platform.note "check that `uname` is on PATH and can run"
    else if e.platform.used_fallback
    then Doctor.check "platform" Doctor.Status.st_warn e.platform.note "install a tag that ships this platform, or use the x86_64 artifacts"
    else Doctor.check "platform" Doctor.Status.st_ok
        (String.concat e.platform.platform (String.concat " (from '" (String.concat e.platform.uname_sm "')"))) ""

def Doctor.active_check (e : Doctor.Env) : Doctor.Check :=
    match e.active {
        Option.none => Doctor.check "active-installed" Doctor.Status.st_fail "no active nightly" "monadup default",
        Option.some tag =>
            if e.active_dir_exists
            then Doctor.check "active-installed" Doctor.Status.st_ok (String.concat tag " installed") ""
            else Doctor.check "active-installed" Doctor.Status.st_fail
                (String.concat "active names '" (String.concat tag "', but its version directory is missing"))
                (String.concat "monadup install " tag),
    }

def Doctor.binary_check (e : Doctor.Env) : Doctor.Check :=
    match e.binary {
        Option.none => Doctor.check "binary" Doctor.Status.st_fail "no monad-nightly-* binary in the active version directory" "monadup install <tag>",
        Option.some name =>
            if e.binary_exec
            then Doctor.check "binary" Doctor.Status.st_ok name ""
            else Doctor.check "binary" Doctor.Status.st_warn (String.concat name " is not executable") "chmod +x <version dir>/<binary>",
    }

def Doctor.commit_check (e : Doctor.Env) : Doctor.Check :=
    match e.commit {
        Option.none => Doctor.check "commit" Doctor.Status.st_warn "commit.txt is missing" "re-run monadup install <tag>",
        Option.some c =>
            match e.binary_version {
                Option.none => Doctor.check "commit" Doctor.Status.st_ok (String.concat "commit.txt: " c) "",
                Option.some v =>
                    if String.beq (Text.trim v) (Text.trim c)
                    then Doctor.check "commit" Doctor.Status.st_ok (String.concat "commit.txt matches the binary: " c) ""
                    else Doctor.check "commit" Doctor.Status.st_warn
                        (String.concat "commit.txt (" (String.concat c (String.concat ") does not match the binary's stamp (" (String.concat (Text.trim v) ")"))))
                        "re-run monadup install <tag>",
            },
    }

def Doctor.runs_check (e : Doctor.Env) : Doctor.Check :=
    match e.binary_version {
        Option.none => Doctor.check "binary-runs" Doctor.Status.st_warn "the installed compiler did not run (`monad version` failed)" "check the platform/fallback note; re-run monadup install <tag>",
        Option.some v => Doctor.check "binary-runs" Doctor.Status.st_ok (String.concat "monad version: " (Text.trim v)) "",
    }

#[partial]
def Doctor.missing_sources (names : List String) (present : List String) : List String :=
    match names {
        List.empty => List.empty,
        List.cons n rest =>
            if Doctor.list_has n present
            then Doctor.missing_sources rest present
            else List.cons n (Doctor.missing_sources rest present),
    }

#[partial]
def Doctor.list_has (name : String) (xs : List String) : Bool :=
    match xs {
        List.empty => false,
        List.cons x rest => if String.beq x name then true else Doctor.list_has name rest,
    }

#[partial]
pub def Doctor.join_names (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons x rest =>
            match rest {
                List.empty => x,
                List.cons _ _ => String.concat x (String.concat " " (Doctor.join_names rest)),
            },
    }

def Doctor.sources_check (e : Doctor.Env) : Doctor.Check :=
    let missing : List String := Doctor.missing_sources Layout.source_names e.sources in
    if List.is_empty missing && e.root_manifest
    then Doctor.check "toolchain-root" Doctor.Status.st_ok "init, std, llvm, runtime and mote.toml are present" ""
    else
        let detail : String :=
            if List.is_empty missing
            then "missing: mote.toml"
            else if e.root_manifest
                 then String.concat "missing: " (Doctor.join_names missing)
                 else String.concat "missing: " (String.concat (Doctor.join_names missing) " mote.toml") in
        Doctor.check "toolchain-root" Doctor.Status.st_warn detail
            "monadup install <tag> (re-running install repairs a source-less version directory)"

def Doctor.link_check (e : Doctor.Env) : Doctor.Check :=
    if e.link_is_symlink
    then
        if e.monad_link_ok
        then Doctor.check "monad-symlink" Doctor.Status.st_ok
            (String.concat "bin/monad -> " (match e.monad_link { Option.some t => t, Option.none => "" })) ""
        else Doctor.check "monad-symlink" Doctor.Status.st_fail "bin/monad is dangling" "monadup use <tag>"
    else if e.monad_link_ok
    then Doctor.check "monad-symlink" Doctor.Status.st_ok "bin/monad is a regular file (not a symlink)" ""
    else Doctor.check "monad-symlink" Doctor.Status.st_fail "bin/monad does not exist" "monadup use <tag>"

def Doctor.path_check (e : Doctor.Env) : Doctor.Check :=
    if e.path_has_bin
    then Doctor.check "path" Doctor.Status.st_ok "the monad bin directory is on PATH" ""
    else Doctor.check "path" Doctor.Status.st_warn "the monad bin directory is not on PATH"
        (String.concat "export PATH=\"" (String.concat (Layout.bin_dir e.home) ":$PATH\""))

def Doctor.overrides_check (e : Doctor.Env) : Doctor.Check :=
    if e.monad_root_bad
    then Doctor.check "overrides" Doctor.Status.st_warn "MONAD_ROOT names a directory that does not exist" "unset MONAD_ROOT or point it at a directory holding init/std/runtime"
    else if List.is_empty e.overrides
         then Doctor.check "overrides" Doctor.Status.st_ok "none" ""
         else Doctor.check "overrides" Doctor.Status.st_ok (Doctor.join_names (Doctor.override_names e.overrides)) ""

#[partial]
pub def Doctor.override_names (xs : List (Pair String String)) : List String :=
    match xs {
        List.empty => List.empty,
        List.cons p rest => match p { Pair.pair k v => List.cons (String.concat k (String.concat "=" v)) (Doctor.override_names rest) },
    }

def Doctor.api_check (e : Doctor.Env) : Doctor.Check :=
    if e.no_network
    then Doctor.check "api" Doctor.Status.st_ok "skipped (--no-network)" ""
    else if e.api_ok
         then Doctor.check "api" Doctor.Status.st_ok "releases API reachable" ""
         else Doctor.check "api" Doctor.Status.st_warn "releases API unreachable (offline is valid for local builds)" "check the network, or use --no-network"

#[partial]
def Doctor.download_join (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons x rest =>
            match rest {
                List.empty => x,
                List.cons _ _ => String.concat x (String.concat " " (Doctor.download_join rest)),
            },
    }

def Doctor.downloads_check (e : Doctor.Env) : Doctor.Check :=
    if List.is_empty e.downloads
    then Doctor.check "downloads" Doctor.Status.st_ok "no other nightlies installed" ""
    else Doctor.check "downloads" Doctor.Status.st_ok
        (String.concat (I64.to_string (List.length e.downloads)) (String.concat ": " (Doctor.download_join e.downloads)))
        "monadup update prunes older nightlies"

// ─── Reporting ─────────────────────────────────────────────────────────

#[partial]
def Doctor.print_human_loop (checks : List Doctor.Check) : IO Unit :=
    match checks {
        List.empty => return unit,
        List.cons c rest => do {
            IO.println (String.concat "[" (String.concat (Doctor.status_text c.status)
                (String.concat "] " (String.concat c.name (String.concat ": " c.detail)))));
            if String.is_empty c.hint || Doctor.status_ok c.status then Doctor.print_human_loop rest
            else do {
                IO.println (String.concat "       fix: " c.hint);
                Doctor.print_human_loop rest
            }
        },
    }

pub def Doctor.print_human (checks : List Doctor.Check) : IO Unit := do {
    IO.println "monadup doctor";
    IO.println "";
    Doctor.print_human_loop checks;
    IO.println "";
    IO.println (Doctor.summary_line checks)
}

#[partial]
def Doctor.count_status (s : Doctor.Status) (checks : List Doctor.Check) : I64 :=
    match checks {
        List.empty => 0,
        List.cons c rest =>
            let n : I64 := if Doctor.status_eq s c.status then 1 else 0 in
            I64.add n (Doctor.count_status s rest),
    }

def Doctor.status_eq (a : Doctor.Status) (b : Doctor.Status) : Bool :=
    match a {
        Doctor.Status.st_ok => match b { Doctor.Status.st_ok => true, _ => false },
        Doctor.Status.st_warn => match b { Doctor.Status.st_warn => true, _ => false },
        Doctor.Status.st_fail => match b { Doctor.Status.st_fail => true, _ => false },
    }

pub def Doctor.summary_line (checks : List Doctor.Check) : String :=
    String.concat "summary: " (String.concat (I64.to_string (Doctor.count_status Doctor.Status.st_ok checks))
        (String.concat " ok, " (String.concat (I64.to_string (Doctor.count_status Doctor.Status.st_warn checks))
            (String.concat " warn, " (String.concat (I64.to_string (Doctor.count_status Doctor.Status.st_fail checks)) " fail")))))

pub def Doctor.exit_code (checks : List Doctor.Check) : I64 :=
    if I64.lt 0 (Doctor.count_status Doctor.Status.st_fail checks) then 1 else 0

def Doctor.opt_json (o : Option String) : Json :=
    match o {
        Option.some s => Json.make_str s,
        Option.none => Json.make_null,
    }

def Doctor.check_json (c : Doctor.Check) : Json :=
    Json.make_object_pairs [
        Pair.pair "name" (Json.make_str c.name),
        Pair.pair "status" (Json.make_str (Doctor.status_text c.status)),
        Pair.pair "detail" (Json.make_str c.detail),
        Pair.pair "hint" (if String.is_empty c.hint then Json.make_null else Json.make_str c.hint),
    ]

#[partial]
def Doctor.checks_json (checks : List Doctor.Check) : List Json :=
    match checks {
        List.empty => List.empty,
        List.cons c rest => List.cons (Doctor.check_json c) (Doctor.checks_json rest),
    }

pub def Doctor.env_json (e : Doctor.Env) (checks : List Doctor.Check) : Json :=
    let root : Json :=
        match e.active {
            Option.some tag => Json.make_str (Layout.version_dir e.home tag),
            Option.none => Json.make_null,
        } in
    Json.make_object_pairs [
        Pair.pair "tool" (Json.make_str "monadup"),
        Pair.pair "version" (Json.make_str "0.1.0"),
        Pair.pair "platform" (Json.make_str e.platform.platform),
        Pair.pair "uname" (Json.make_str e.platform.uname_sm),
        Pair.pair "platform_fallback" (Json.make_bool e.platform.used_fallback),
        Pair.pair "home" (Json.make_str e.home.path),
        Pair.pair "home_source" (Json.make_str e.home.source),
        Pair.pair "active" (Doctor.opt_json e.active),
        Pair.pair "toolchain_root" root,
        Pair.pair "sources" (Json.make_array (Doctor.strings_json e.sources)),
        Pair.pair "checks" (Json.make_array (Doctor.checks_json checks)),
        Pair.pair "summary" (Json.make_object_pairs [
            Pair.pair "ok" (Json.make_num_int (Doctor.count_status Doctor.Status.st_ok checks)),
            Pair.pair "warn" (Json.make_num_int (Doctor.count_status Doctor.Status.st_warn checks)),
            Pair.pair "fail" (Json.make_num_int (Doctor.count_status Doctor.Status.st_fail checks)),
        ]),
    ]

#[partial]
def Doctor.strings_json (xs : List String) : List Json :=
    match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons (Json.make_str x) (Doctor.strings_json rest),
    }

pub def Doctor.run (no_network : Bool) (as_json : Bool) : IO I64 := do {
    let env <- Doctor.gather no_network;
    let checks : List Doctor.Check := Doctor.checks env;
    if as_json
    then IO.println (Json.to_string (Doctor.env_json env checks))
    else Doctor.print_human checks;
    return (Doctor.exit_code checks)
}
