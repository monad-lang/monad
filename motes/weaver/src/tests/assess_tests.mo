/// Where a pick reaches: file targets, command paths, `cd`, redirects and
/// the expansions the gate cannot read.
use weaver::assess {Assessment, Reach, Assess.command, Assess.path, Assess.pick, Assess.scope_line}
use shuttle::gate {Pick, Capability}
use std::path {Path, Path.to_string}
use std::list {List.intercalate}
use json::json {Json, Json.make_object, Json.make_str}
use std::map {Map, BTreeMap}

def root : Option Path := Option.some (Path.path "/repo")

/// `inside`, `unknown`, or `outside:` and the paths.
def shape (a : Assessment) : String :=
    match a.scope {
        Reach.inside => "inside",
        Reach.unknown => "unknown",
        Reach.outside ps => String.concat "outside:" (List.intercalate "," (List.map Path.to_string ps)),
    }

def cmd (s : String) : String := shape (Assess.command root s)

#[test]
def test_commands_without_outside_paths_are_inside : Bool :=
    String.beq (cmd "cargo test -p core") "inside"
        && String.beq (cmd "ls src/ && cat ./README.md") "inside"
        && String.beq (cmd "git log origin/main --oneline") "inside"
        && String.beq (cmd "make 2>/dev/null > build/out.log") "inside"
        && String.beq (cmd "curl https://example.com/x") "inside"

#[test]
def test_outside_paths_are_listed : Bool :=
    String.beq (cmd "cat /etc/hosts") "outside:/etc/hosts"
        && String.beq (cmd "ls ../other") "outside:/other"
        && String.beq (cmd "cp a.txt ~/backup/") "outside:~/backup/"
        && String.beq (cmd "echo hi > /tmp/x") "outside:/tmp/x"
        && String.beq (cmd "tool --out=/var/log/x") "outside:/var/log/x"

#[test]
def test_cd_moves_the_base : Bool :=
    String.beq (cmd "cd src && ls ../docs") "inside"
        && String.beq (cmd "cd .. && ls ../x") "outside:/,/x"
        && String.beq (cmd "cd && ls") "outside:~"
        && String.beq (cmd "cd - && ls") "unknown"

#[test]
def test_expansions_are_unknown : Bool :=
    String.beq (cmd "ls $HOME/x") "unknown"
        && String.beq (cmd "echo 'unterminated") "unknown"
        && String.beq (cmd "echo $USER") "inside"

/// A substituted or `sh -c` command is scanned too.
#[test]
def test_nested_commands_are_scanned : Bool :=
    String.beq (cmd "echo $(cat /etc/passwd)") "outside:/etc/passwd"
        && String.beq (cmd "bash -c 'cat /etc/shadow'") "outside:/etc/shadow"
        && String.beq (cmd "sh -c \"ls src\"") "inside"

#[test]
def test_file_targets : Bool :=
    String.beq (shape (Assess.path root "src/a.mo")) "inside"
        && String.beq (shape (Assess.path root "/repo/b.mo")) "inside"
        && String.beq (shape (Assess.path root "/repo-evil/b.mo")) "outside:/repo-evil/b.mo"
        && String.beq (shape (Assess.path Option.none "src/a.mo")) "unknown"

def proc_pick (command : String) (cwd : String) : Pick :=
    let input : Json := Json.make_object (Map.insert "command" (Json.make_str command)
        (Map.insert "cwd" (Json.make_str cwd) BTreeMap.empty)) in
    { name := "start_process", cap := Capability.exec, input := input }

/// `start_process` runs from its `cwd`, which is itself a reach.
#[test]
def test_start_process_cwd : Bool :=
    String.beq (shape (Assess.pick root (proc_pick "ls" "/repo/sub"))) "inside"
        && String.beq (shape (Assess.pick root (proc_pick "ls" "/srv"))) "outside:/srv"

#[test]
def test_scope_lines : Bool :=
    String.beq (Assess.scope_line root Reach.inside) "inside /repo"
        && String.beq (Assess.scope_line root (Reach.outside [Path.path "/etc/hosts"])) "outside the workspace: /etc/hosts"
        && String.beq (Assess.scope_line root Reach.unknown) "can't tell where this runs"
