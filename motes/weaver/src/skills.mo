/// Agent Skills: folders of instructions the model loads when a task
/// calls for them.
///
/// A skill is a directory holding `SKILL.md` -- YAML frontmatter with a
/// `name` and a `description`, then the instructions -- plus any files the
/// instructions refer to. The layout is the open Agent Skills one, so skill
/// folders written for other agents work unchanged.
///
/// Discovery: the user's `$XDG_CONFIG_HOME/weaver/skills/*/SKILL.md` (else
/// `~/.config/weaver/skills`), and -- for a trusted project only --
/// `<repo>/.weaver/skills/*` and `<repo>/.agents/skills/*`. A project skill
/// overrides a user skill of the same name.
///
/// Progressive disclosure: the system prompt carries one line per skill
/// (name and description); the `skill` tool returns the instructions and
/// the paths of the bundled files when the model decides a skill fits;
/// `/<name> [args]` runs a turn with them directly.
use init::string {}
use init::transformers {ResultT}
use std::list {List.filter, List.any, List.intercalate}
use std::io {IO.read_file, IO.is_dir, IO.list_dir, IO.get_env}
use std::path {Path, Path.to_string, Path.join, Path.file_name}
use std::process {Proc.capture}
use std::stream {StreamError}
use std::map {Map, BTreeMap}
use markdown::parse {Markdown.split_frontmatter}
use markdown::types {Markdown.FrontSplit, Markdown.FrontFormat, Markdown.Frontmatter}
use markdown::scan {Markdown.split_lines}
use yaml::yaml {Yaml, Yaml.parse, Yaml.get_mapping, Yaml.get_str}
use json::json {Json, Json.make_object_pairs, Json.make_array, Json.make_str, Json.get_object, Json.get_str, Json.object_get}
use shuttle::tool {ToolSpec, ToolImpl}
use shuttle::gate {Capability}
use shuttle::message_types {Content}
use weaver::place {SessionPlace}

pub struct Skill {
    name : String,
    description : String,
    /// `user` or `project`.
    source : String,
    /// The `SKILL.md` path.
    path : String,
    /// The skill's directory: bundled files live here.
    dir : String,
}

/// The skills found, and one notice per skill folder that was skipped.
pub struct SkillScan {
    skills : List Skill,
    skipped : List String,
}

pub def Skills.file_name : String := "SKILL.md"

/// The system prompt's skill index is capped; the rest is named in an
/// overflow line and still reachable through `/skills` and the tool.
pub def Skills.index_cap : I64 := 8192

/// A skill body larger than this is cut, with a marker.
pub def Skills.body_cap : I64 := 65536

/// How many bundled files the tool lists.
pub def Skills.files_cap : I64 := 50

// ─── Parsing ───────────────────────────────────────────────────────────

def skill_yaml_str (key : String) (m : BTreeMap String Yaml) : String :=
    match Map.lookup key m {
        Option.none => "",
        Option.some y => match Yaml.get_str y {
            Result.ok s => String.trim s,
            Result.err _ => "",
        },
    }

def name_byte_ok (b : U8) : Bool :=
    let n : U32 := U8.to_u32 b in
    Bool.or (Bool.and (U32.lt 47u32 n) (U32.lt n 58u32))
        (Bool.or (Bool.and (U32.lt 96u32 n) (U32.lt n 123u32)) (Bool.or (U32.beq n 45u32) (U32.beq n 95u32)))

#[partial]
def all_name_bytes (bs : List U8) : Bool :=
    match bs {
        List.empty => true,
        List.cons b rest => if name_byte_ok b then all_name_bytes rest else false,
    }

/// Lowercase letters, digits, `-` and `_`, at most 64 bytes: a name that
/// can follow a `/` on the input line.
pub def Skills.valid_name (n : String) : Bool :=
    Bool.not (String.is_empty n) && I64.lt (String.length n) 65 && all_name_bytes (String.to_list n)

def skill_of_map (path : String) (dir : String) (source : String) (m : BTreeMap String Yaml) : Result String Skill :=
    let name : String := skill_yaml_str "name" m in
    let desc : String := skill_yaml_str "description" m in
    if String.is_empty name then Result.err "no name in the frontmatter"
    else if Bool.not (Skills.valid_name name) then Result.err (String.concat "name must be lowercase letters, digits, - or _: " name)
    else if String.is_empty desc then Result.err "no description in the frontmatter"
    else
        let s : Skill := { name := name, description := desc, source := source, path := path, dir := dir } in
        Result.ok s

def skill_of_yaml (path : String) (dir : String) (source : String) (literal : String) : Result String Skill :=
    match Yaml.parse literal {
        Result.err _ => Result.err "the frontmatter is not valid YAML",
        Result.ok y => match Yaml.get_mapping y {
            Result.err _ => Result.err "the frontmatter is not a mapping",
            Result.ok m => skill_of_map path dir source m,
        },
    }

/// One `SKILL.md`, parsed: the frontmatter must be YAML with a `name` and a
/// `description`.
pub def Skills.parse (path : String) (dir : String) (source : String) (text : String) : Result String Skill :=
    let split : Markdown.FrontSplit := Markdown.split_frontmatter text in
    match split.front {
        Option.none => Result.err "no frontmatter (--- name/description ---)",
        Option.some f => match f.format {
            Markdown.FrontFormat.front_toml => Result.err "the frontmatter is TOML; skills use YAML",
            Markdown.FrontFormat.front_yaml => skill_of_yaml path dir source f.literal,
        },
    }

/// The instructions: the file without its frontmatter.
pub def Skills.body_of (text : String) : String :=
    let split : Markdown.FrontSplit := Markdown.split_frontmatter text in
    String.trim split.body

// ─── Discovery ─────────────────────────────────────────────────────────

def skills_non_empty (o : Option String) : Option String :=
    match o {
        Option.some s => if String.is_empty s then Option.none else Option.some s,
        Option.none => Option.none,
    }

/// `$XDG_CONFIG_HOME/weaver/skills`, else `~/.config/weaver/skills`.
pub def Skills.user_root_of (xdg : Option String) (home : Option String) : Option String :=
    match skills_non_empty xdg {
        Option.some x => Option.some (String.concat x "/weaver/skills"),
        Option.none => match skills_non_empty home {
            Option.some h => Option.some (String.concat h "/.config/weaver/skills"),
            Option.none => Option.none,
        },
    }

pub def Skills.user_root : IO (Option String) := do {
    let xdg <- IO.get_env "XDG_CONFIG_HOME";
    let home <- IO.get_env "HOME";
    IO.pure (Skills.user_root_of xdg home)
}

pub def Skills.project_roots (repo : Path) : List String :=
    let r : String := Path.to_string repo in
    [String.concat r "/.agents/skills", String.concat r "/.weaver/skills"]

def skipped_note (path : String) (why : String) : String :=
    String.concat_list ["[skill skipped: ", path, ": ", why, "]"]

def scan_one (source : String) (d : Path) (acc : SkillScan) : IO SkillScan := do {
    let path : String := String.concat (Path.to_string d) (String.concat "/" Skills.file_name);
    let r <- IO.read_file (Path.path path);
    IO.pure (scanned source path (Path.to_string d) r acc)
}

def scanned (source : String) (path : String) (dir : String) (r : Result StreamError String) (acc : SkillScan) : SkillScan :=
    match r {
        // A directory without SKILL.md is not a skill: no notice.
        Result.err _ => acc,
        Result.ok text => match Skills.parse path dir source text {
            Result.ok s =>
                let a : SkillScan := { acc with skills := List.append acc.skills [s] } in
                a,
            Result.err why =>
                let a : SkillScan := { acc with skipped := List.append acc.skipped [skipped_note path why] } in
                a,
        },
    }

#[partial]
def scan_dirs (source : String) (ds : List Path) (acc : SkillScan) : IO SkillScan :=
    match ds {
        List.empty => IO.pure acc,
        List.cons d rest => do {
            let a <- scan_one source d acc;
            scan_dirs source rest a
        },
    }

pub def Skills.empty_scan : SkillScan :=
    let s : SkillScan := { skills := List.empty, skipped := List.empty } in
    s

/// Every skill folder directly under `root`.
pub def Skills.scan_root (root : String) (source : String) (acc : SkillScan) : IO SkillScan := do {
    let there <- IO.is_dir (Path.path root);
    if Bool.not there then IO.pure acc
    else do {
        let names <- IO.list_dir (Path.path root);
        let dirs : List Path := List.filter (fn (p : Path) => Bool.not (String.starts_with "." (Path.file_name p))) names;
        scan_dirs source dirs acc
    }
}

#[partial]
def scan_roots (roots : List String) (source : String) (acc : SkillScan) : IO SkillScan :=
    match roots {
        List.empty => IO.pure acc,
        List.cons r rest => do {
            let a <- Skills.scan_root r source acc;
            scan_roots rest source a
        },
    }

def project_roots_if (place : Option SessionPlace) (trusted : Bool) : List String :=
    match place {
        Option.none => List.empty,
        Option.some p => if trusted then Skills.project_roots p.repo else List.empty,
    }

def user_roots (user : Option String) : List String :=
    match user {
        Option.none => List.empty,
        Option.some u => [u],
    }

/// Later skills win a name: project over user.
#[partial]
pub def Skills.dedupe (ss : List Skill) : List Skill :=
    match ss {
        List.empty => List.empty,
        List.cons s rest =>
            if List.any (fn (t : Skill) => t.name == s.name) rest then Skills.dedupe rest
            else List.cons s (Skills.dedupe rest),
    }

/// The session's skills: the user's, then (trusted projects) the project's.
pub def Skills.discover (user : Option String) (place : Option SessionPlace) (trusted : Bool) : IO SkillScan := do {
    let mine <- scan_roots (user_roots user) "user" Skills.empty_scan;
    let all <- scan_roots (project_roots_if place trusted) "project" mine;
    let s : SkillScan := { all with skills := Skills.dedupe all.skills };
    IO.pure s
}

/// The project `SKILL.md` paths, for the trust record: a changed project
/// skill asks for trust again, as a changed AGENTS.md does.
pub def Skills.project_files (repo : Path) : IO (List Path) := do {
    let scan <- scan_roots (Skills.project_roots repo) "project" Skills.empty_scan;
    IO.pure (List.map (fn (s : Skill) => Path.path s.path) scan.skills)
}

#[partial]
pub def Skills.find (ss : List Skill) (name : String) : Option Skill :=
    match ss {
        List.empty => Option.none,
        List.cons s rest => if s.name == name then Option.some s else Skills.find rest name,
    }

// ─── The system prompt's index ────────────────────────────────────────

def index_line (s : Skill) : String :=
    String.concat_list ["- ", s.name, ": ", s.description]

#[partial]
def index_lines (ss : List Skill) (room : I64) (acc : List String) : Pair (List String) I64 :=
    match ss {
        List.empty => Pair.pair (List.reverse acc) 0,
        List.cons s rest =>
            let line : String := index_line s in
            if I64.lt room (String.length line + 1) then Pair.pair (List.reverse acc) (List.length ss)
            else index_lines rest (room - String.length line - 1) (List.cons line acc),
    }

/// The prompt block naming each skill; empty with no skills.
pub def Skills.index (ss : List Skill) : String :=
    match ss {
        List.empty => "",
        List.cons _ _ => match index_lines ss Skills.index_cap List.empty {
            Pair.pair lines left =>
                let more : String := if I64.lt left 1 then "" else String.concat_list ["\n- (", I64.to_string left, " more: /skills lists them)"] in
                String.concat_list ["# Skills\n\nWhen a task matches a skill's description, call the skill tool with its name before starting, and follow what it returns.\n\n",
                    List.intercalate "\n" lines, more],
        },
    }

/// A system prompt with the skill index appended.
pub def Skills.with_index (prompt : String) (ss : List Skill) : String :=
    let block : String := Skills.index ss in
    if String.is_empty block then prompt else String.concat_list [prompt, "\n\n", block]

// ─── Loading one ───────────────────────────────────────────────────────

def cap_body (body : String) : String :=
    if I64.lt Skills.body_cap (String.length body)
    then String.concat (String.slice body 0 Skills.body_cap) "\n[skill truncated at 64 KiB]"
    else body

/// The instructions, capped; an error when the file cannot be read.
pub def Skills.load_body (s : Skill) : IO (Result String String) := do {
    let r <- IO.read_file (Path.path s.path);
    match r {
        Result.err _ => IO.pure (Result.err (String.concat "could not read " s.path)),
        Result.ok text => IO.pure (Result.ok (cap_body (Skills.body_of text))),
    }
}

#[partial]
def take_files (n : I64) (ls : List String) : List String :=
    if I64.lt n 1 then List.empty
    else match ls {
        List.empty => List.empty,
        List.cons l rest =>
            if String.is_empty (String.trim l) || String.ends_with l "/SKILL.md" then take_files n rest
            else List.cons l (take_files (n - 1) rest),
    }

/// The skill's other files (absolute paths), for the model to read.
/// `find` runs inside the skill directory, so only dot-paths within the
/// skill are skipped -- the directory itself usually sits under a dotted
/// one (`~/.config`, `.weaver`, `.agents`).
pub def Skills.bundled (s : Skill) : IO (List String) := do {
    let r <- Proc.capture "sh" ["-c", "cd \"$1\" && find . -type f -not -path '*/.*'", "sh", s.dir];
    match r {
        Pair.pair code out =>
            if Bool.not (code == 0) then IO.pure List.empty
            else IO.pure (List.map (fn (l : String) => String.concat s.dir (String.drop 1 l)) (take_files Skills.files_cap (Markdown.split_lines out)))
    }
}

/// What the model gets for one skill: its instructions, the bundled
/// files, and the arguments it was invoked with.
pub def Skills.render (s : Skill) (body : String) (files : List String) (args : String) : String :=
    let head : String := String.concat_list ["Skill ", s.name, " (", s.source, ", ", s.dir, ")\n\n"] in
    let files_part : String := match files {
        List.empty => "",
        List.cons _ _ => String.concat "\n\nBundled files (read them as the instructions say):\n" (List.intercalate "\n" (List.map (fn (f : String) => String.concat "- " f) files)),
    } in
    let args_part : String := if String.is_empty (String.trim args) then "" else String.concat "\n\nArguments: " (String.trim args) in
    String.concat_list [head, body, files_part, args_part]

/// One skill, loaded and rendered.
pub def Skills.expand (s : Skill) (args : String) : IO (Result String String) := do {
    let b <- Skills.load_body s;
    match b {
        Result.err e => IO.pure (Result.err e),
        Result.ok body => do {
            let files <- Skills.bundled s;
            IO.pure (Result.ok (Skills.render s body files args))
        }
    }
}

// ─── The listing ───────────────────────────────────────────────────────

/// The startup note: the skills found and any skipped; none for neither.
pub def Skills.note (scan : SkillScan) : Option String :=
    let found : List String := match scan.skills {
        List.empty => List.empty,
        List.cons _ _ => [String.concat "skills: " (List.intercalate ", " (List.map (fn (sk : Skill) => sk.name) scan.skills))],
    } in
    match List.append found scan.skipped {
        List.empty => Option.none,
        List.cons _ _ => Option.some (List.intercalate "\n" (List.append found scan.skipped)),
    }

def list_line (s : Skill) : String :=
    String.concat_list ["/", s.name, "  (", s.source, ")  ", s.description]

pub def Skills.listing (ss : List Skill) (skipped : List String) (clashes : List String) : String :=
    let head : String := match ss {
        List.empty => "no skills (add one as ~/.config/weaver/skills/<name>/SKILL.md, or .weaver/skills/<name>/SKILL.md in a trusted project)",
        List.cons _ _ => String.concat "skills:\n" (List.intercalate "\n" (List.map list_line ss)),
    } in
    let clash : String := match clashes {
        List.empty => "",
        List.cons _ _ => String.concat "\n\nshadowed by a built-in command (use the skill tool, or rename): " (List.intercalate ", " clashes),
    } in
    let skip : String := match skipped {
        List.empty => "",
        List.cons _ _ => String.concat "\n\n" (List.intercalate "\n" skipped),
    } in
    String.concat_list [head, clash, skip]

// ─── The tool ──────────────────────────────────────────────────────────

def skill_str_prop (d : String) : Json :=
    Json.make_object_pairs [Pair.pair "type" (Json.make_str "string"), Pair.pair "description" (Json.make_str d)]

def skill_schema : Json :=
    Json.make_object_pairs
        [Pair.pair "type" (Json.make_str "object"),
            Pair.pair "properties" (Json.make_object_pairs
                [Pair.pair "name" (skill_str_prop "The skill's name, as the system prompt lists it."),
                    Pair.pair "args" (skill_str_prop "Optional arguments for the skill.")]),
            Pair.pair "required" (Json.make_array [Json.make_str "name"])]

pub def SkillTool.spec : ToolSpec :=
    { name := "skill",
        description := "Load a skill: its instructions and the paths of its bundled files. Call it before starting a task whose description matches a skill in the system prompt's Skills list, then follow the instructions.",
        schema := skill_schema }

/// `read`-tagged: it only reads skill files the session already discovered.
pub def SkillTool.impl (ss : List Skill) : ToolImpl :=
    { spec := SkillTool.spec, cap := Capability.read, run := skill_tool_run ss }

def skill_tool_failed (id : String) (msg : String) : IO (Result String Content) :=
    IO.pure (Result.ok (Content.tool_result id (String.concat "skill: " msg) true))

def skill_input_str (key : String) (j : Json) : String :=
    match Json.get_object j {
        Result.err _ => "",
        Result.ok obj => match Json.object_get key obj {
            Option.none => "",
            Option.some v => match Json.get_str v {
                Result.ok s => String.trim s,
                Result.err _ => "",
            },
        },
    }

def known_names (ss : List Skill) : String :=
    match ss {
        List.empty => "no skills are installed",
        List.cons _ _ => String.concat "known: " (List.intercalate ", " (List.map (fn (s : Skill) => s.name) ss)),
    }

def skill_tool_run (ss : List Skill) (id : String) (j : Json) : ResultT String IO Content :=
    ResultT.mk (skill_tool_go ss id (skill_input_str "name" j) (skill_input_str "args" j))

def skill_tool_go (ss : List Skill) (id : String) (name : String) (args : String) : IO (Result String Content) :=
    match Skills.find ss name {
        Option.none => skill_tool_failed id (String.concat_list ["no skill named ", name, " (", known_names ss, ")"]),
        Option.some s => do {
            let r <- Skills.expand s args;
            match r {
                Result.err e => skill_tool_failed id e,
                Result.ok text => IO.pure (Result.ok (Content.tool_result id text false)),
            }
        },
    }
