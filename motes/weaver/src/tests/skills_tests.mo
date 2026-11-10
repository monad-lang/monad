/// Agent Skills: SKILL.md parsing, the user/project discovery and its
/// precedence and trust gate, the system prompt's capped index, and the
/// `skill` tool's output (instructions, bundled files, arguments).
use init::string {}
use init::transformers {ResultT}
use std::list {List.intercalate}
use std::path {Path}
use std::process {process_id, exec_cmd}
use std::io {IO.write_file}
use json::json {Json, Json.parse, Json.make_str}
use shuttle::message_types {Content}
use shuttle::tool {ToolImpl}
use weaver::place {SessionPlace}
use weaver::skills {
    Skill, SkillScan, Skills.parse, Skills.body_of, Skills.valid_name, Skills.user_root_of, Skills.discover,
    Skills.index, Skills.with_index, Skills.index_cap, Skills.find, Skills.expand, Skills.listing, Skills.dedupe,
    SkillTool.impl,
}

def good_md : String := "---\nname: release-notes\ndescription: Write release notes from the git log.\n---\n\n# Release notes\n\nRead CHANGES.md first.\n"

def parsed_ok (r : Result String Skill) : Bool :=
    match r { Result.ok _ => true, Result.err _ => false }

def parse_err (r : Result String Skill) : String :=
    match r { Result.ok _ => "", Result.err e => e }

#[test]
def test_a_skill_parses : Bool :=
    match Skills.parse "/s/release-notes/SKILL.md" "/s/release-notes" "user" good_md {
        Result.err _ => false,
        Result.ok s => s.name == "release-notes" && s.description == "Write release notes from the git log." && s.source == "user",
    }

#[test]
def test_a_skill_needs_a_description : Bool :=
    String.contains (parse_err (Skills.parse "p" "d" "user" "---\nname: x\n---\nbody\n")) "description"

#[test]
def test_a_skill_needs_frontmatter : Bool :=
    String.contains (parse_err (Skills.parse "p" "d" "user" "# just text\n")) "frontmatter"

#[test]
def test_bad_yaml_is_refused : Bool :=
    Bool.not (parsed_ok (Skills.parse "p" "d" "user" "---\nname: [x\n---\nbody\n"))

#[test]
def test_a_name_must_be_slash_friendly : Bool :=
    Skills.valid_name "pdf_tools-2" && Bool.not (Skills.valid_name "Has Space") && Bool.not (Skills.valid_name "")
        && Bool.not (parsed_ok (Skills.parse "p" "d" "user" "---\nname: Bad Name\ndescription: d\n---\n"))

#[test]
def test_the_body_drops_the_frontmatter : Bool :=
    let b : String := Skills.body_of good_md in
    String.starts_with "# Release notes" b && Bool.not (String.contains b "description:")

#[test]
def test_the_user_root_prefers_xdg : Bool :=
    let a : Option String := Skills.user_root_of (Option.some "/x") (Option.some "/h") in
    let b : Option String := Skills.user_root_of Option.none (Option.some "/h") in
    (match a { Option.some r => r == "/x/weaver/skills", Option.none => false })
        && (match b { Option.some r => r == "/h/.config/weaver/skills", Option.none => false })

def skill_named (name : String) (desc : String) (source : String) : Skill :=
    let s : Skill := { name := name, description := desc, source := source, path := String.concat "/s/" name, dir := "/s" } in
    s

#[test]
def test_a_later_skill_wins_its_name : Bool :=
    let ss : List Skill := Skills.dedupe [skill_named "a" "user a" "user", skill_named "b" "user b" "user", skill_named "a" "project a" "project"] in
    List.length ss == 2 && (match Skills.find ss "a" { Option.some s => s.source == "project", Option.none => false })

#[test]
def test_no_skills_leave_the_prompt_alone : Bool :=
    Skills.with_index "base" List.empty == "base"

#[test]
def test_the_index_names_each_skill : Bool :=
    let p : String := Skills.with_index "base" [skill_named "a" "does A" "user"] in
    String.starts_with "base\n\n# Skills" p && String.contains p "- a: does A"

#[test]
def test_the_index_is_capped : Bool :=
    let desc : String := String.repeat "x" 500 in
    let many : List Skill := List.map (fn (i : I64) => skill_named (String.concat "s" (I64.to_string i)) desc "user") (range_list 0 40) in
    let ix : String := Skills.index many in
    I64.lt (String.length ix) (Skills.index_cap + 400) && String.contains ix "more: /skills lists them"

#[partial]
def range_list (i : I64) (n : I64) : List I64 :=
    if I64.lt i n then List.cons i (range_list (i + 1) n) else List.empty

// ── discovery and the tool (scratch directories) ───────────────────────

def base_dir (name : String) : String :=
    String.concat "/tmp/weaver_skills_" (String.concat (I64.to_string process_id) (String.concat "_" name))

def put (path : String) (text : String) : IO Unit := do {
    let dir : String := String.slice path 0 (String.find_last path "/");
    let _ <- exec_cmd "mkdir" ["-p", dir];
    let _ <- IO.write_file (Path.path path) text;
    IO.pure unit
}

def skill_md (name : String) (desc : String) (body : String) : String :=
    String.concat_list ["---\nname: ", name, "\ndescription: ", desc, "\n---\n\n", body, "\n"]

def setup (base : String) : IO SessionPlace := do {
    let _ <- exec_cmd "rm" ["-rf", base];
    let _ <- put (String.concat base "/user/shared/SKILL.md") (skill_md "shared" "the user's version" "USER BODY");
    let _ <- put (String.concat base "/user/only-user/SKILL.md") (skill_md "only-user" "a user skill" "ONLY USER");
    let _ <- put (String.concat base "/user/only-user/scripts/run.sh") "echo hi\n";
    let _ <- put (String.concat base "/user/broken/SKILL.md") "no frontmatter here\n";
    let _ <- put (String.concat base "/repo/.weaver/skills/shared/SKILL.md") (skill_md "shared" "the project's version" "PROJECT BODY");
    let place : SessionPlace := { cwd := Path.path (String.concat base "/repo"), repo := Path.path (String.concat base "/repo") };
    IO.pure place
}

def source_of (ss : List Skill) (name : String) : String :=
    match Skills.find ss name { Option.some s => s.source, Option.none => "" }

#[test]
def test_a_trusted_project_overrides_a_user_skill : IO Bool := do {
    let base : String := base_dir "trusted";
    let place <- setup base;
    let scan <- Skills.discover (Option.some (String.concat base "/user")) (Option.some place) true;
    IO.pure (List.length scan.skills == 2
        && source_of scan.skills "shared" == "project"
        && source_of scan.skills "only-user" == "user"
        && List.length scan.skipped == 1
        && String.contains (List.intercalate "\n" scan.skipped) "broken/SKILL.md")
}

#[test]
def test_an_untrusted_project_adds_no_skills : IO Bool := do {
    let base : String := base_dir "untrusted";
    let place <- setup base;
    let scan <- Skills.discover (Option.some (String.concat base "/user")) (Option.some place) false;
    IO.pure (List.length scan.skills == 2 && source_of scan.skills "shared" == "user")
}

def json_of (s : String) : Json :=
    match Json.parse s { Result.ok j => j, Result.err _ => Json.make_str "" }

def tool_text (r : Result String Content) : String :=
    match r {
        Result.err e => e,
        Result.ok c => match c { Content.tool_result _ t _ => t, _ => "" },
    }

def tool_error (r : Result String Content) : Bool :=
    match r {
        Result.err _ => true,
        Result.ok c => match c { Content.tool_result _ _ e => e, _ => true },
    }

#[test]
def test_the_tool_returns_the_body_files_and_args : IO Bool := do {
    let base : String := base_dir "tool";
    let place <- setup base;
    let scan <- Skills.discover (Option.some (String.concat base "/user")) (Option.some place) false;
    let t : ToolImpl := SkillTool.impl scan.skills;
    let r <- ResultT.run (t.run "c1" (json_of "{\"name\":\"only-user\",\"args\":\"v2\"}"));
    let text : String := tool_text r;
    IO.pure (Bool.not (tool_error r)
        && String.contains text "ONLY USER"
        && String.contains text "scripts/run.sh"
        && String.contains text "Arguments: v2"
        && Bool.not (String.contains text "description:"))
}

#[test]
def test_an_unknown_skill_is_an_error_naming_the_known_ones : IO Bool := do {
    let base : String := base_dir "unknown";
    let place <- setup base;
    let scan <- Skills.discover (Option.some (String.concat base "/user")) (Option.some place) false;
    let t : ToolImpl := SkillTool.impl scan.skills;
    let r <- ResultT.run (t.run "c1" (json_of "{\"name\":\"nope\"}"));
    IO.pure (tool_error r && String.contains (tool_text r) "only-user")
}

#[test]
def test_the_listing_names_shadowed_skills : Bool :=
    let out : String := Skills.listing [skill_named "plan" "clashes" "user"] List.empty ["plan"] in
    String.contains out "/plan  (user)  clashes" && String.contains out "shadowed by a built-in command"

#[test]
def test_bundled_files_are_found_under_a_dotted_root : IO Bool := do {
    let base : String := base_dir "dotted";
    let _ <- exec_cmd "rm" ["-rf", base];
    let root : String := String.concat base "/.config/weaver/skills";
    let _ <- put (String.concat root "/kit/SKILL.md") (skill_md "kit" "a kit" "KIT BODY");
    let _ <- put (String.concat root "/kit/templates/a.txt") "a\n";
    let _ <- put (String.concat root "/kit/.hidden/b.txt") "b\n";
    let scan <- Skills.discover (Option.some root) Option.none false;
    let t : ToolImpl := SkillTool.impl scan.skills;
    let r <- ResultT.run (t.run "c1" (json_of "{\"name\":\"kit\"}"));
    let text : String := tool_text r;
    IO.pure (String.contains text (String.concat root "/kit/templates/a.txt")
        && Bool.not (String.contains text "b.txt")
        && Bool.not (String.contains text "kit/SKILL.md\n"))
}
