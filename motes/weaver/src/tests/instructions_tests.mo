/// Finding, capping and rendering AGENTS.md files.
use weaver::instructions {
    InstrFile, Instructions.chain, Instructions.user_path_of, Instructions.discover, Instructions.cut_at,
    Instructions.capped, Instructions.cap_total, Instructions.render, Instructions.label,
    Instructions.note, Prompt.base, Prompt.system, Prompt.with_files,
    Instructions.read_one, Instructions.refresh, Instructions.take_notes,
    Instructions.attaching, Instructions.inside,
}
use shuttle::tools::file_tools {ReadTool.impl}
use shuttle::registry {ToolRegistry}
use shuttle::message_types {Content}
use init::transformers {ResultT}
use json::json {Json, Json.make_object, Json.make_str}
use std::map {Map, BTreeMap}
use std::ref {Ref.new, Ref.get}
use weaver::place {SessionPlace}
use std::path {Path, Path.to_string}
use std::list {List.intercalate, List.all}
use std::process {process_id, exec_cmd}
use std::io {IO.write_file}

def paths (ps : List Path) : String :=
    List.intercalate "|" (List.map Path.to_string ps)

#[test]
def test_chain_is_root_first : Bool :=
    String.beq (paths (Instructions.chain (Path.path "/r") (Path.path "/r/a/b"))) "/r|/r/a|/r/a/b"

#[test]
def test_chain_at_the_root_is_the_root_once : Bool :=
    String.beq (paths (Instructions.chain (Path.path "/r") (Path.path "/r"))) "/r"

#[test]
def test_chain_outside_the_repo_is_the_cwd : Bool :=
    String.beq (paths (Instructions.chain (Path.path "/r") (Path.path "/elsewhere/x"))) "/elsewhere/x"

#[test]
def test_user_path_prefers_xdg : Bool :=
    let a : String := match Instructions.user_path_of (Option.some "/x") (Option.some "/h") { Option.some p => Path.to_string p, Option.none => "" } in
    let b : String := match Instructions.user_path_of (Option.some "") (Option.some "/h") { Option.some p => Path.to_string p, Option.none => "" } in
    String.beq a "/x/weaver/AGENTS.md" && String.beq b "/h/.config/weaver/AGENTS.md"

#[test]
def test_cut_lands_after_a_newline : Bool :=
    Instructions.cut_at "ab\ncd\nef" 7 == 6 && Instructions.cut_at "abc" 10 == 3 && Instructions.cut_at "abcdef" 3 == 0

#[test]
def test_capped_marks_truncation : Bool :=
    let f : InstrFile := Instructions.capped (Path.path "/r/AGENTS.md") "repo" "one\ntwo\nthree\n" 9 in
    String.beq f.text "one\ntwo\n" && f.truncated

#[test]
def test_total_cap_spends_in_order : Bool :=
    let a : InstrFile := Instructions.capped (Path.path "/a") "user" "1234\n" 100 in
    let b : InstrFile := Instructions.capped (Path.path "/b") "repo" "5678\n9\n" 100 in
    let capped : List InstrFile := Instructions.cap_total [a, b] 7 in
    String.beq (List.intercalate "|" (List.map (fn (f : InstrFile) => f.text) capped)) "1234\n|"
        && List.all (fn (f : InstrFile) => f.truncated == String.is_empty f.text) capped

#[test]
def test_render_empty_and_one : Bool :=
    let f : InstrFile := Instructions.capped (Path.path "/r/AGENTS.md") "repo" "Use tabs.\n" 100 in
    String.beq (Instructions.render []) ""
        && String.contains (Instructions.render [f]) "## /r/AGENTS.md (repo)\nUse tabs.\n"
        && String.beq (Instructions.label f) "/r/AGENTS.md (repo, 10 B)"

def temp_root : String :=
    String.concat "/tmp/weaver_instr_test_" (I64.to_string process_id)

def discover_case (root : String) : IO Bool := do {
    let place : SessionPlace := { cwd := Path.path (String.concat root "/sub/deeper"), repo := Path.path root };
    let fs <- Instructions.discover Option.none (Option.some place) true;
    let none <- Instructions.discover Option.none (Option.some place) false;
    let _ <- exec_cmd "rm" ["-rf", root];
    IO.pure (String.beq (List.intercalate "|" (List.map (fn (f : InstrFile) => f.scope) fs)) "repo|dir"
        && List.length none == 0)
}

#[test]
def test_discover_reads_root_and_nested_but_only_when_trusted : IO Bool := do {
    let root : String := temp_root;
    let _ <- exec_cmd "mkdir" ["-p", String.concat root "/sub/deeper"];
    let _ <- IO.write_file (Path.path (String.concat root "/AGENTS.md")) "root rules\n";
    let _ <- IO.write_file (Path.path (String.concat root "/sub/AGENTS.md")) "sub rules\n";
    discover_case root
}

def one_file : InstrFile :=
    Instructions.capped (Path.path "/r/AGENTS.md") "repo" "Always answer in haiku.\n" 32768

/// The base prompt tells the model to attribute the commits it makes.
#[test]
def test_base_prompt_carries_the_commit_trailer : Bool :=
    String.contains Prompt.base "Assisted by Weaver agent weaver@monad-lang.org"
        && String.contains Prompt.base "git commit"

/// No files leaves the base prompt byte-identical; a file is appended
/// after it under the instructions header.
#[test]
def test_system_prompt_appends_the_files : Bool :=
    let p : String := Prompt.system [one_file] in
    String.beq (Prompt.system List.empty) Prompt.base
        && String.starts_with Prompt.base p
        && String.contains p "# Project instructions"
        && String.contains p "Always answer in haiku."

/// A subagent's prompt gets the same block after its own base.
#[test]
def test_with_files_keeps_its_own_base : Bool :=
    let p : String := Prompt.with_files "child base" [one_file] in
    String.starts_with "child base" p && String.contains p "Always answer in haiku."

#[test]
def test_note_lists_files_or_is_absent : Bool :=
    (match Instructions.note List.empty { Option.none => true, Option.some _ => false })
        && (match Instructions.note [one_file] {
            Option.some n => String.contains n "instructions: /r/AGENTS.md (repo",
            Option.none => false,
        })

// ── mid-session changes ──

def refresh_root : String :=
    String.concat "/tmp/weaver_instr_refresh_" (I64.to_string process_id)

/// Read `name` under the refresh root as a loaded repo file.
def loaded (name : String) : IO (List InstrFile) := do {
    let f <- Instructions.read_one (Path.path (String.concat refresh_root name)) "repo";
    IO.pure (match f { Option.some x => [x], Option.none => List.empty })
}

def notes_of (pr : Pair (List InstrFile) (List String)) : List String :=
    match pr { Pair.pair _ ns => ns }

/// Unchanged: no note. Edited: one note with the diff, told once.
/// Deleted: the removal note, and the file leaves the set.
#[test]
def test_refresh_notes_an_edit_once_and_a_removal : IO Bool := do {
    let _ <- exec_cmd "mkdir" ["-p", refresh_root];
    let path : Path := Path.path (String.concat refresh_root "/AGENTS.md");
    let _ <- IO.write_file path "keep tests green\n";
    let fs <- loaded "/AGENTS.md";
    let same <- Instructions.refresh fs;
    let seen <- Ref.new fs;
    let _ <- IO.write_file path "keep tests green\nalways answer in haiku\n";
    let first <- Instructions.take_notes (Option.some seen);
    let second <- Instructions.take_notes (Option.some seen);
    let _ <- exec_cmd "rm" ["-f", Path.to_string path];
    let gone <- Instructions.take_notes (Option.some seen);
    let left <- Ref.get seen;
    let _ <- exec_cmd "rm" ["-rf", refresh_root];
    IO.pure (List.length fs == 1
        && List.is_empty (notes_of same)
        && List.length first == 1
        && String.contains (List.intercalate "" first) "changed during the session"
        && String.contains (List.intercalate "" first) "+ always answer in haiku"
        && List.is_empty second
        && String.contains (List.intercalate "" gone) "was deleted during the session"
        && List.is_empty left)
}

// ── a subdirectory's AGENTS.md ──

def attach_root : String :=
    String.concat "/tmp/weaver_instr_attach_" (I64.to_string process_id)

#[test]
def test_inside_is_the_repo_or_below : Bool :=
    Instructions.inside (Path.path "/r") (Path.path "/r")
        && Instructions.inside (Path.path "/r") (Path.path "/r/a/b")
        && Bool.not (Instructions.inside (Path.path "/r") (Path.path "/rx/a"))
        && Bool.not (Instructions.inside (Path.path "/r") (Path.path "/elsewhere"))

def read_input (path : String) : Json :=
    Json.make_object (Map.insert "path" (Json.make_str path) BTreeMap.empty)

def output_of (r : Result String Content) : String :=
    match r {
        Result.ok c => match c { Content.tool_result _ out _ => out, _ => "" },
        Result.err e => e,
    }

/// Run the wrapped `read` on `path`.
def read_via (reg : ToolRegistry) (path : String) : IO String :=
    match ToolRegistry.lookup "read" reg {
        Option.none => IO.pure "",
        Option.some impl => match impl {
            { run, .. } => do {
                let r <- ResultT.run (run "id-1" (read_input path));
                IO.pure (output_of r)
            },
        },
    }

/// The first read under `motes/x` attaches its AGENTS.md; the second
/// does not; an untrusted project attaches nothing.
#[test]
def test_a_read_attaches_a_nested_file_once : IO Bool := do {
    let root : String := attach_root;
    let _ <- exec_cmd "mkdir" ["-p", String.concat root "/motes/x/src"];
    let _ <- IO.write_file (Path.path (String.concat root "/AGENTS.md")) "root rules\n";
    let _ <- IO.write_file (Path.path (String.concat root "/motes/x/AGENTS.md")) "x rules\n";
    let _ <- IO.write_file (Path.path (String.concat root "/motes/x/src/a.mo")) "def a : I64 := 1\n";
    let place : SessionPlace := { cwd := Path.path root, repo := Path.path root };
    let start <- Instructions.discover Option.none (Option.some place) true;
    let seen <- Ref.new start;
    let reg : ToolRegistry := Instructions.attaching (Option.some seen) (Option.some place) true (ToolRegistry.register ReadTool.impl ToolRegistry.empty);
    let file : String := String.concat root "/motes/x/src/a.mo";
    let first <- read_via reg file;
    let second <- read_via reg file;
    let fresh <- Ref.new start;
    let untrusted <- read_via (Instructions.attaching (Option.some fresh) (Option.some place) false (ToolRegistry.register ReadTool.impl ToolRegistry.empty)) file;
    let now <- Ref.get seen;
    let _ <- exec_cmd "rm" ["-rf", root];
    IO.pure (String.contains first "def a : I64 := 1"
        && String.contains first "[Instructions for "
        && String.contains first "x rules"
        && Bool.not (String.contains first "root rules")
        && Bool.not (String.contains second "[Instructions for ")
        && Bool.not (String.contains untrusted "[Instructions for ")
        && List.length now == 2)
}
