/// Plan files and the plan repo.
///
/// A plan is a Markdown file with YAML frontmatter. Every plan a session
/// captures lands in the plan repo (`plans.repo`, `WEAVER_PLAN_REPO`, or
/// `~/.weaver/plans`) under `<dir>/<date>-<slug>.md`, so a later run --
/// any session, any day -- can list it (`/plans`) and load it again. The
/// session links its plan through `plan_file.txt`: a revision rewrites the
/// same file, and the frontmatter's `sessions` grows with each session
/// that worked on it.
///
/// Frontmatter is advisory: a malformed block yields a warning and the
/// body is still shown, because losing the plan is worse than losing its
/// metadata.
use init::string {}
use std::list {List.filter, List.sort_by, List.any}
use std::map {Map, BTreeMap, BTreeMap.to_list}
use std::io {IO.read_file, IO.file_exists, IO.is_dir, IO.list_dir}
use std::path {Path, Path.of, Path.to_string, Path.join, Path.file_name}
use std::process {exec_cmd, Proc.capture}
use std::sha256 {Sha256.hash}
use time::types {DateTime}
use time::instant {Instant.now}
use time::datetime {DateTime.of_instant}
use time::datetime {DateTime.to_iso}
use markdown::parse {Markdown.split_frontmatter}
use markdown::scan {Markdown.split_lines}
use markdown::types {Markdown.FrontSplit, Markdown.FrontFormat, Markdown.Frontmatter}
use yaml::yaml {Yaml, Yaml.ParseError, Yaml.parse, Yaml.to_string, Yaml.get_mapping, Yaml.get_str, Yaml.get_int, Yaml.get_seq, Yaml.make_mapping_pairs, Yaml.make_str, Yaml.make_int, Yaml.make_seq}
use weaver::store {StoreState, Store.read_named, Store.write_named, Store.write_atomic_at}

pub struct PlanMeta {
    title : String,
    created : String,
    updated : String,
    /// draft | approved | in-progress | done | abandoned
    status : String,
    model : String,
    /// The repo the plan is about (`SessionPlace.repo`).
    project : String := "",
    /// Every session that captured, revised or loaded the plan, oldest first.
    sessions : List String := List.empty,
    /// 0-100, set through the `plan` tool.
    completion : I64 := 0,
    next_action : String := "",
    /// Frontmatter keys weaver does not own (a hand-written plan's
    /// `priority`, `depends_on`, ...), written back unchanged.
    extra : List (Pair String Yaml) := List.empty,
}

pub struct PlanDoc {
    meta : PlanMeta,
    body : String,
}

/// A parsed plan plus a non-fatal frontmatter warning.
pub struct PlanParse {
    doc : PlanDoc,
    warning : Option String,
}

pub def PlanMeta.empty : PlanMeta :=
    { title := "", created := "", updated := "", status := "draft", model := "",
        project := "", sessions := List.empty, completion := 0, next_action := "", extra := List.empty }

// ─── Rendering ─────────────────────────────────────────────────────────

pub def PlanFile.render (d : PlanDoc) : String :=
    let pairs : List (Pair String Yaml) := [
        Pair.pair "title" (Yaml.make_str d.meta.title),
        Pair.pair "status" (Yaml.make_str d.meta.status),
        Pair.pair "project" (Yaml.make_str d.meta.project),
        Pair.pair "sessions" (Yaml.make_seq (List.map Yaml.make_str d.meta.sessions)),
        Pair.pair "created" (Yaml.make_str d.meta.created),
        Pair.pair "updated" (Yaml.make_str d.meta.updated),
        Pair.pair "model" (Yaml.make_str d.meta.model),
        Pair.pair "completion" (Yaml.make_int d.meta.completion),
        Pair.pair "next_action" (Yaml.make_str d.meta.next_action),
    ] in
    let all : List (Pair String Yaml) := List.append pairs d.meta.extra in
    let front : Yaml := Yaml.make_mapping_pairs all in
    String.concat "---\n" (String.concat (Yaml.to_string front) (String.concat "\n---\n\n" d.body))

// ─── Parsing ───────────────────────────────────────────────────────────

def yaml_str (key : String) (m : BTreeMap String Yaml) : String :=
    match Map.lookup key m {
        Option.none => "",
        Option.some y => match Yaml.get_str y {
            Result.ok s => s,
            Result.err _ => "",
        },
    }

def yaml_int (key : String) (m : BTreeMap String Yaml) : I64 :=
    match Map.lookup key m {
        Option.none => 0,
        Option.some y => match Yaml.get_int y {
            Result.ok n => n,
            Result.err _ => 0,
        },
    }

def str_of_yaml (y : Yaml) : Option String :=
    match Yaml.get_str y {
        Result.ok s => Option.some s,
        Result.err _ => Option.none,
    }

#[partial]
def strs_of (ys : List Yaml) : List String :=
    match ys {
        List.empty => List.empty,
        List.cons y rest => match str_of_yaml y {
            Option.some s => List.cons s (strs_of rest),
            Option.none => strs_of rest,
        },
    }

/// `sessions` as a list; a legacy single `session` string counts as one.
def yaml_sessions (m : BTreeMap String Yaml) : List String :=
    match Map.lookup "sessions" m {
        Option.some y => match Yaml.get_seq y {
            Result.ok ys => strs_of ys,
            Result.err _ => List.empty,
        },
        Option.none =>
            let one : String := yaml_str "session" m in
            if String.is_empty one then List.empty else [one],
    }

/// A UTF-8-safe prefix: `String.slice` answers "" at a continuation
/// byte, so back off up to three bytes.
#[partial]
def cap_title (s : String) (max : I64) (back : I64) : String :=
    if I64.gt back 3 then ""
    else if I64.lt (max - back) 1 then ""
    else
        let x : String := String.slice s 0 (max - back) in
        if String.is_empty x then cap_title s max (back + 1) else x

/// The first heading or non-empty line, for a plan with no frontmatter.
#[partial]
def title_of (lines : List String) : String :=
    match lines {
        List.empty => "Untitled plan",
        List.cons l rest =>
            let t : String := String.trim l in
            if String.is_empty t then title_of rest
            else if String.starts_with "# " t then String.trim (String.drop 2 t)
            else if I64.gt (String.length t) 80 then cap_title t 80 0 else t,
    }

pub def PlanFile.title_of_text (text : String) : String :=
    title_of (Markdown.split_lines text)

def bare_parse (body : String) (warning : Option String) : PlanParse :=
    let meta : PlanMeta := { PlanMeta.empty with title := PlanFile.title_of_text body } in
    let doc : PlanDoc := { meta := meta, body := body } in
    let r : PlanParse := { doc := doc, warning := warning } in
    r

/// The frontmatter keys weaver writes itself (`session` is the legacy
/// single-session key, folded into `sessions`).
pub def PlanFile.own_keys : List String :=
    ["title", "status", "project", "sessions", "session", "created", "updated", "model", "completion", "next_action"]

def is_own_key (k : String) : Bool :=
    List.any (fn (o : String) => o == k) PlanFile.own_keys

def extra_of (m : BTreeMap String Yaml) : List (Pair String Yaml) :=
    List.filter (fn (kv : Pair String Yaml) => match kv { Pair.pair k _ => Bool.not (is_own_key k) }) (BTreeMap.to_list m)

def mapped_parse (body : String) (m : BTreeMap String Yaml) : PlanParse :=
    let status0 : String := yaml_str "status" m in
    let meta : PlanMeta := {
        title := yaml_str "title" m,
        created := yaml_str "created" m,
        updated := yaml_str "updated" m,
        status := if String.is_empty status0 then "draft" else status0,
        model := yaml_str "model" m,
        project := yaml_str "project" m,
        sessions := yaml_sessions m,
        completion := yaml_int "completion" m,
        next_action := yaml_str "next_action" m,
        extra := extra_of m,
    } in
    let meta2 : PlanMeta := if String.is_empty meta.title then { meta with title := PlanFile.title_of_text body } else meta in
    let doc : PlanDoc := { meta := meta2, body := body } in
    let r : PlanParse := { doc := doc, warning := Option.none } in
    r

def yaml_parse (body : String) (literal : String) : PlanParse :=
    match Yaml.parse literal {
        Result.err e => bare_parse body (Option.some (String.concat "frontmatter: " (Yaml.ParseError.to_string e))),
        Result.ok y => match Yaml.get_mapping y {
            Result.err e => bare_parse body (Option.some (String.concat "frontmatter: " e)),
            Result.ok m => mapped_parse body m,
        },
    }

pub def PlanFile.parse (text : String) : PlanParse :=
    let split : Markdown.FrontSplit := Markdown.split_frontmatter text in
    match split.front {
        Option.none => bare_parse text Option.none,
        Option.some f => match f.format {
            Markdown.FrontFormat.front_toml => bare_parse split.body (Option.some "frontmatter is TOML, not YAML"),
            Markdown.FrontFormat.front_yaml => yaml_parse split.body f.literal,
        },
    }

// ─── Date and slug ─────────────────────────────────────────────────────

/// Now, UTC, ISO 8601 to the second: `created`/`updated`. Plans changed
/// on the same day still sort.
pub def PlanFile.stamp : IO String := do {
    let now <- Instant.now;
    let dt : DateTime := DateTime.of_instant now 0;
    IO.pure (DateTime.to_iso dt)
}

/// The calendar day of a stamp (its first ten bytes, `YYYY-MM-DD`).
pub def PlanFile.day_of (stamp : String) : String :=
    if I64.lt (String.length stamp) 11 then stamp else String.slice stamp 0 10

def lower_u8 (b : U8) : U8 :=
    let n : U32 := U8.to_u32 b in
    if Bool.and (U32.lt 64u32 n) (U32.lt n 91u32)
    then U32.to_u8 (U32.add n 32u32)
    else b

def alnum_u8 (b : U8) : Bool :=
    let n : U32 := U8.to_u32 b in
    Bool.or (Bool.and (U32.lt 47u32 n) (U32.lt n 58u32))
        (Bool.and (U32.lt 96u32 n) (U32.lt n 123u32))

/// Lowercase ASCII, punctuation to `-`, runs collapsed, capped at 40
/// bytes. A title with no ASCII letters/numbers yields "plan".
#[partial]
def slug_go (bs : List U8) (last_dash : Bool) (n : I64) (acc : List U8) : List U8 :=
    if I64.lt n 1 then acc
    else match bs {
        List.empty => acc,
        List.cons b rest =>
            let lower : U8 := lower_u8 b in
            if alnum_u8 lower
            then slug_go rest false (n - 1) (List.append acc (List.cons lower List.empty))
            else if Bool.not last_dash
            then slug_go rest true (n - 1) (List.append acc (List.cons 45u8 List.empty))
            else slug_go rest true (n - 1) acc,
    }

#[partial]
def drop_leading_dashes (bs : List U8) : List U8 :=
    match bs {
        List.empty => List.empty,
        List.cons b rest => if U8.beq b 45u8 then drop_leading_dashes rest else bs,
    }

#[partial]
def drop_trailing_dashes (bs : List U8) : List U8 :=
    List.reverse (drop_leading_dashes (List.reverse bs))

pub def PlanFile.slug (title : String) : String :=
    // The byte cap lives in slug_go, so a multibyte title is never cut
    // mid-character.
    let chars : List U8 := drop_trailing_dashes (drop_leading_dashes (slug_go (String.to_list title) true 40 List.empty)) in
    let s : String := String.from_list chars in
    if String.is_empty s then "plan" else s

// ─── The changelog ─────────────────────────────────────────────────────

pub def PlanFile.changelog_heading : String := "\n## Changelog\n"

/// The body before its `## Changelog` section, and the section's entries
/// (without the heading). A body with no section has no entries.
pub def PlanFile.split_changelog (body : String) : Pair String String :=
    let at : I64 := String.find_last body PlanFile.changelog_heading in
    if I64.lt at 0 then Pair.pair body ""
    else
        let skip : I64 := at + String.length PlanFile.changelog_heading in
        Pair.pair (String.slice body 0 at) (String.drop skip body)

/// A body with one more changelog line, newest first.
pub def PlanFile.with_entry (body : String) (day : String) (line : String) : String :=
    match PlanFile.split_changelog body {
        Pair.pair main entries =>
            let entry : String := String.concat "\n- **" (String.concat day (String.concat "**: " line)) in
            String.concat (String.trim main) (String.concat "\n" (String.concat PlanFile.changelog_heading (String.concat entry entries))),
    }

/// A revised body that keeps the old file's changelog entries.
pub def PlanFile.revise_body (old_body : String) (new_body : String) : String :=
    match PlanFile.split_changelog old_body {
        Pair.pair _ entries =>
            if String.is_empty (String.trim entries) then new_body
            else
                match PlanFile.split_changelog new_body {
                    Pair.pair main _ => String.concat (String.trim main) (String.concat "\n" (String.concat PlanFile.changelog_heading entries)),
                },
    }

// ─── The plan repo ─────────────────────────────────────────────────────

/// Where plans live: `root` is the plan repo, `dir` the directory this
/// project's plans go in (inside `root`), `commit` whether each write is
/// committed when `root` is a git work tree.
pub struct PlanRepo {
    root : String,
    dir : String,
    commit : Bool,
}

/// The `plans` settings, as read from the config files.
pub struct PlanSettings {
    repo : Option String := Option.none,
    dir : Option String := Option.none,
    commit : Option Bool := Option.none,
}

pub def PlanSettings.empty : PlanSettings :=
    { repo := Option.none, dir := Option.none, commit := Option.none }

def hash_prefix (s : String) : String :=
    if I64.lt (String.length s) 13 then s else String.slice s 0 12

/// A stable directory name per project: the repo's basename as a slug and
/// a short hash of its full path, so two checkouts named alike differ.
pub def PlanFile.project_key (repo : String) : String :=
    let base : String := Path.file_name (Path.path repo) in
    String.concat (PlanFile.slug base) (String.concat "-" (hash_prefix (Sha256.hash repo)))

def plan_nonempty (o : Option String) : Option String :=
    match o {
        Option.none => Option.none,
        Option.some s => if String.is_empty (String.trim s) then Option.none else Option.some (String.trim s),
    }

/// `~/x` against HOME, `/x` as is, anything else against the project.
def plan_expand (s : String) (home : Option String) (project : Option String) : Option String :=
    if String.starts_with "/" s then Option.some s
    else if String.starts_with "~/" s
    then match home {
        Option.none => Option.none,
        Option.some h => Option.some (String.concat h (String.drop 1 s)),
    }
    else match project {
        Option.none => Option.none,
        Option.some p => Option.some (String.concat p (String.concat "/" s)),
    }

def plan_default_root (home : Option String) : Option String :=
    match plan_nonempty home {
        Option.none => Option.none,
        Option.some h => Option.some (String.concat h "/.weaver/plans"),
    }

def plan_root_of (env : Option String) (home : Option String) (setting : Option String) (project : Option String) : Option String :=
    match plan_nonempty env {
        Option.some e => plan_expand e home project,
        Option.none => match plan_nonempty setting {
            Option.some s => plan_expand s home project,
            Option.none => plan_default_root home,
        },
    }

def plan_dir_of (root : String) (setting : Option String) (project : Option String) : String :=
    match plan_nonempty setting {
        Option.some d => String.concat root (String.concat "/" d),
        Option.none => match project {
            Option.none => String.concat root "/default",
            Option.some p => String.concat root (String.concat "/" (PlanFile.project_key p)),
        },
    }

/// The plan repo from `WEAVER_PLAN_REPO`, HOME, the `plans` settings and
/// the project's repo root. None only when nothing names a place (no
/// env, no setting, no HOME).
pub def PlanRepo.resolve (env : Option String) (home : Option String) (s : PlanSettings) (project : Option String) : Option PlanRepo :=
    match plan_root_of env home s.repo project {
        Option.none => Option.none,
        Option.some root =>
            let commit : Bool := match s.commit { Option.some b => b, Option.none => true } in
            let r : PlanRepo := { root := root, dir := plan_dir_of root s.dir project, commit := commit } in
            Option.some r,
    }

def plan_mkdir (dir : String) : IO Unit := do {
    let _ <- exec_cmd "mkdir" ["-p", dir];
    IO.pure unit
}

def candidate (dir : String) (base : String) (n : I64) : String :=
    if I64.lt n 2
    then String.concat dir (String.concat "/" (String.concat base ".md"))
    else String.concat dir (String.concat "/" (String.concat base (String.concat "-" (String.concat (I64.to_string n) ".md"))))

#[partial]
def unique_path (dir : String) (base : String) (n : I64) : IO String := do {
    let p : String := candidate dir base n;
    let exists <- IO.file_exists (Path.path p);
    if exists then unique_path dir base (n + 1) else IO.pure p
}

/// Read one plan file; none when it is missing or empty.
pub def PlanFile.read (path : String) : IO (Option PlanDoc) := do {
    let r <- IO.read_file (Path.path path);
    match r {
        Result.err _ => IO.pure Option.none,
        Result.ok text =>
            if String.is_empty text then IO.pure Option.none
            else do {
                let p : PlanParse := PlanFile.parse text;
                IO.pure (Option.some p.doc)
            }
    }
}

/// Commit one plan file in the plan repo when it is a git work tree.
/// Never pushes. Hooks run. Answers a notice on failure.
pub def PlanRepo.commit_file (r : PlanRepo) (path : String) (subject : String) : IO (Option String) :=
    if Bool.not r.commit then IO.pure Option.none
    else do {
        let inside <- Proc.capture "git" ["-C", r.root, "rev-parse", "--is-inside-work-tree"];
        match inside {
            Pair.pair code _ =>
                if Bool.not (code == 0) then IO.pure Option.none
                else commit_in r path subject
        }
    }

def commit_in (r : PlanRepo) (path : String) (subject : String) : IO (Option String) := do {
    let add <- Proc.capture "git" ["-C", r.root, "add", "--", path];
    match add {
        Pair.pair code out =>
            if Bool.not (code == 0)
            then IO.pure (Option.some (String.concat "plan not committed: " (String.trim out)))
            else do {
                let c <- Proc.capture "git" ["-C", r.root, "commit", "-q", "-m", subject, "--", path];
                match c {
                    Pair.pair code2 out2 =>
                        if code2 == 0 then IO.pure Option.none
                        else IO.pure (Option.some (String.concat "plan not committed: " (String.trim out2)))
                }
            }
    }
}

def commit_subject (d : PlanDoc) : String :=
    String.concat "plan: " (String.concat d.meta.title (String.concat " -- " d.meta.status))

/// Write a plan file atomically and commit it. The answer is a notice for
/// the user when something went wrong, none when all went well.
pub def PlanRepo.write (r : PlanRepo) (path : String) (d : PlanDoc) : IO (Option String) := do {
    let ok <- Store.write_atomic_at (Path.path path) (PlanFile.render d);
    if Bool.not ok
    then IO.pure (Option.some (String.concat "plan not stored: could not write " path))
    else PlanRepo.commit_file r path (commit_subject d)
}

def with_session_id (ss : List String) (id : String) : List String :=
    if String.is_empty id then ss
    else if List.any (fn (s : String) => s == id) ss then ss
    else List.append ss [id]

/// A captured plan's new file.
pub def PlanFile.fresh (day : String) (session : String) (model : String) (project : String) (text : String) : PlanDoc :=
    let meta : PlanMeta := { PlanMeta.empty with title := PlanFile.title_of_text text, created := day, updated := day,
        status := "draft", model := model, project := project, sessions := with_session_id List.empty session } in
    let d : PlanDoc := { meta := meta, body := text } in
    d

/// A revision of `old` with the new text: the changelog survives, the
/// title follows the new text, the session is recorded.
pub def PlanFile.revised (old : PlanDoc) (day : String) (session : String) (text : String) : PlanDoc :=
    let meta : PlanMeta := { old.meta with title := PlanFile.title_of_text text, updated := day,
        sessions := with_session_id old.meta.sessions session } in
    let d : PlanDoc := { meta := meta, body := PlanFile.revise_body old.body text } in
    d

/// The plan file this session is linked to, if any.
pub def PlanFile.linked (st : StoreState) : IO (Option String) := do {
    let r <- Store.read_named st "plan_file.txt";
    match r {
        Option.none => IO.pure Option.none,
        Option.some p => IO.pure (Option.some (String.trim p)),
    }
}

pub def PlanFile.link (st : StoreState) (path : String) : IO Unit :=
    Store.write_named st "plan_file.txt" path

/// The outcome of storing a plan: its path, and a notice when something
/// went wrong on the way.
pub struct Stored {
    path : Option String,
    notice : Option String,
}

def stored_of (path : Option String) (notice : Option String) : Stored :=
    let s : Stored := { path := path, notice := notice } in
    s

/// Store a captured plan: a session's first plan makes a new `draft`, a
/// later one rewrites the linked file.
pub def PlanRepo.capture (r : PlanRepo) (st : StoreState) (model : String) (project : String) (text : String) : IO Stored := do {
    let day <- PlanFile.stamp;
    let linked <- PlanFile.linked st;
    capture_linked r st day model project text linked
}

def capture_linked (r : PlanRepo) (st : StoreState) (day : String) (model : String) (project : String) (text : String) (linked : Option String) : IO Stored :=
    match linked {
        Option.none => capture_new r st day model project text,
        Option.some p => do {
            let old <- PlanFile.read p;
            capture_over r st day model project text p old
        },
    }

def capture_over (r : PlanRepo) (st : StoreState) (day : String) (model : String) (project : String) (text : String) (p : String) (old : Option PlanDoc) : IO Stored :=
    match old {
        Option.some d => plan_store_at r st p (PlanFile.revised d day st.id text),
        Option.none => capture_new r st day model project text,
    }

def capture_new (r : PlanRepo) (st : StoreState) (day : String) (model : String) (project : String) (text : String) : IO Stored := do {
    let _ <- plan_mkdir r.dir;
    let _ <- note_project r.dir project;
    let d : PlanDoc := PlanFile.fresh day st.id model project text;
    let base : String := String.concat (PlanFile.day_of day) (String.concat "-" (PlanFile.slug d.meta.title));
    let path <- unique_path r.dir base 1;
    plan_store_at r st path d
}

def plan_store_at (r : PlanRepo) (st : StoreState) (path : String) (d : PlanDoc) : IO Stored := do {
    let notice <- PlanRepo.write r path d;
    let _ <- PlanFile.link st path;
    IO.pure (stored_of (Option.some path) notice)
}

/// `project.txt` names the repo a key directory belongs to.
def note_project (dir : String) (project : String) : IO Unit :=
    if String.is_empty project then IO.pure unit
    else do {
        let p : Path := Path.path (String.concat dir "/project.txt");
        let there <- IO.file_exists p;
        if there then IO.pure unit
        else do {
            let _ <- Store.write_atomic_at p (String.concat project "\n");
            IO.pure unit
        }
    }

/// Change a stored plan's frontmatter and log the change.
pub def PlanRepo.update (r : PlanRepo) (path : String) (f : PlanMeta -> PlanMeta) (line : String) : IO (Result String PlanDoc) := do {
    let old <- PlanFile.read path;
    update_doc r path f line old
}

def update_doc (r : PlanRepo) (path : String) (f : PlanMeta -> PlanMeta) (line : String) (old : Option PlanDoc) : IO (Result String PlanDoc) :=
    match old {
        Option.none => IO.pure (Result.err (String.concat "no plan at " path)),
        Option.some d => do {
            let day <- PlanFile.stamp;
            let d2 : PlanDoc := PlanFile.updated d (f d.meta) day line;
            let notice <- PlanRepo.write r path d2;
            IO.pure (update_result d2 notice)
        },
    }

/// `d` with new metadata, stamped, and one more changelog line (dated by
/// the stamp's day).
pub def PlanFile.updated (d : PlanDoc) (m0 : PlanMeta) (stamp : String) (line : String) : PlanDoc :=
    let m : PlanMeta := { m0 with updated := stamp } in
    let d2 : PlanDoc := { meta := m, body := PlanFile.with_entry d.body (PlanFile.day_of stamp) line } in
    d2

/// A failed write is an error; a failed commit is not (the file is there).
def update_result (d : PlanDoc) (notice : Option String) : Result String PlanDoc :=
    match notice {
        Option.none => Result.ok d,
        Option.some n => if String.starts_with "plan not stored" n then Result.err n else Result.ok d,
    }

pub def PlanMeta.with_status (status : String) (m : PlanMeta) : PlanMeta :=
    let m2 : PlanMeta := { m with status := status } in
    m2

pub def PlanMeta.with_session (session : String) (m : PlanMeta) : PlanMeta :=
    let m2 : PlanMeta := { m with sessions := with_session_id m.sessions session } in
    m2

pub def PlanMeta.with_progress (completion : Option I64) (next_action : Option String) (m : PlanMeta) : PlanMeta :=
    let c : I64 := match completion { Option.some n => n, Option.none => m.completion } in
    let a : String := match next_action { Option.some s => s, Option.none => m.next_action } in
    let m2 : PlanMeta := { m with completion := c, next_action := a } in
    m2

pub def PlanRepo.set_status (r : PlanRepo) (path : String) (status : String) (why : String) : IO (Result String PlanDoc) :=
    PlanRepo.update r path (PlanMeta.with_status status)
        (if String.is_empty why then String.concat "status: " status else String.concat "status: " (String.concat status (String.concat " -- " why)))

/// Record that a session picked the plan up (`/plans load`, `--plan`).
pub def PlanRepo.add_session (r : PlanRepo) (path : String) (session : String) : IO (Result String PlanDoc) :=
    PlanRepo.update r path (PlanMeta.with_session session)
        (String.concat "loaded by session " session)

// ─── Listing ───────────────────────────────────────────────────────────

/// One listed plan: its path and the parsed doc, or none when the file
/// could not be read.
pub struct PlanEntry {
    path : String,
    doc : Option PlanDoc,
}

def is_plan_name (name : String) : Bool :=
    Bool.and (String.ends_with name ".md") (Bool.not (String.starts_with "." name))

def plan_entry_of (p : Path) : IO PlanEntry := do {
    let d <- PlanFile.read (Path.to_string p);
    let e : PlanEntry := { path := Path.to_string p, doc := d };
    IO.pure e
}

#[partial]
def plan_entries_of (ps : List Path) : IO (List PlanEntry) :=
    match ps {
        List.empty => IO.pure List.empty,
        List.cons p rest => do {
            let e <- plan_entry_of p;
            let es <- plan_entries_of rest;
            IO.pure (List.cons e es)
        },
    }

def plan_updated_of (e : PlanEntry) : String :=
    match e.doc {
        Option.none => "",
        Option.some d => d.meta.updated,
    }

/// Newest first: `updated`, then the file name (dated, so it sorts too).
pub def PlanEntry.newer (a : PlanEntry) (b : PlanEntry) : Bool :=
    let ua : String := plan_updated_of a in
    let ub : String := plan_updated_of b in
    if ua == ub then String.gt a.path b.path else String.gt ua ub

/// The plans in one directory, newest first.
pub def PlanFile.list_dir (dir : String) : IO (List PlanEntry) := do {
    let there <- IO.is_dir (Path.path dir);
    if Bool.not there then IO.pure List.empty
    else do {
        let names <- IO.list_dir (Path.path dir);
        let mds : List Path := List.filter (fn (p : Path) => is_plan_name (Path.file_name p)) names;
        let es <- plan_entries_of mds;
        IO.pure (List.sort_by PlanEntry.newer es)
    }
}

#[partial]
def plan_list_dirs (ds : List Path) : IO (List PlanEntry) :=
    match ds {
        List.empty => IO.pure List.empty,
        List.cons d rest => do {
            let here <- PlanFile.list_dir (Path.to_string d);
            let more <- plan_list_dirs rest;
            IO.pure (List.append here more)
        },
    }

/// Every project's plans: each directory of the repo. The root's own
/// Markdown (a repo's index or README) is not a plan.
pub def PlanRepo.list_all (r : PlanRepo) : IO (List PlanEntry) := do {
    let there <- IO.is_dir (Path.path r.root);
    if Bool.not there then IO.pure List.empty
    else do {
        let names <- IO.list_dir (Path.path r.root);
        let dirs : List Path := List.filter (fn (p : Path) => Bool.not (String.starts_with "." (Path.file_name p))) names;
        let nested <- plan_list_dirs dirs;
        IO.pure (List.sort_by PlanEntry.newer nested)
    }
}

/// This project's plans, newest first.
pub def PlanRepo.list (r : PlanRepo) : IO (List PlanEntry) :=
    PlanFile.list_dir r.dir

/// One listing line: `n. title · status · completion% · updated`.
pub def PlanEntry.line (n : I64) (e : PlanEntry) : String :=
    let head : String := String.concat (I64.to_string n) ". " in
    match e.doc {
        Option.none => String.concat head (String.concat "(unreadable) " (Path.file_name (Path.path e.path))),
        Option.some d =>
            let pct : String := if I64.lt d.meta.completion 1 then "" else String.concat " · " (String.concat (I64.to_string d.meta.completion) "%") in
            String.concat head (String.concat d.meta.title (String.concat " · " (String.concat d.meta.status (String.concat pct (String.concat " · " (PlanFile.day_of d.meta.updated)))))),
    }
