/// Finding, capping and rendering AGENTS.md files.
use weaver::instructions {
    InstrFile, Instructions.chain, Instructions.user_path_of, Instructions.discover, Instructions.cut_at,
    Instructions.capped, Instructions.cap_total, Instructions.render, Instructions.label,
    Instructions.note, Prompt.base, Prompt.system, Prompt.with_files,
    Instructions.read_one, Instructions.refresh, Instructions.take_notes,
}
use std::ref {Ref, Ref.new, Ref.get}
use weaver::place {SessionPlace}
use std::path {Path, Path.to_string}
use std::list {List.length, List.intercalate, List.all}
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
