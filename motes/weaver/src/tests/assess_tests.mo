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
        Reach.scratch => "scratch",
        Reach.unknown => "unknown",
        Reach.outside ps => String.concat "outside:" (List.intercalate "," (List.map Path.to_string ps)),
    }

def cmd (s : String) : String := shape (Assess.command root Option.none s)

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
    String.beq (shape (Assess.path root Option.none "src/a.mo")) "inside"
        && String.beq (shape (Assess.path root Option.none "/repo/b.mo")) "inside"
        && String.beq (shape (Assess.path root Option.none "/repo-evil/b.mo")) "outside:/repo-evil/b.mo"
        && String.beq (shape (Assess.path Option.none Option.none "src/a.mo")) "unknown"

def shell_pick (command : String) : Pick :=
    let input : Json := Json.make_object (Map.insert "command" (Json.make_str command) BTreeMap.empty) in
    { name := "shell", cap := Capability.exec, input := input }

/// A `shell` pick is judged by its command's words.
#[test]
def test_shell_pick_reads_the_command : Bool :=
    String.beq (shape (Assess.pick root Option.none (shell_pick "ls src"))) "inside"
        && String.beq (shape (Assess.pick root Option.none (shell_pick "cat /srv/x"))) "outside:/srv/x"

#[test]
def test_scope_lines : Bool :=
    String.beq (Assess.scope_line root Reach.inside) "inside /repo"
        && String.beq (Assess.scope_line root (Reach.outside [Path.path "/etc/hosts"])) "outside the workspace: /etc/hosts"
        && String.beq (Assess.scope_line root Reach.unknown) "can't tell where this runs"

// ── the session scratch dir ─────────────────────────────────────────────

def scratch : Option Path := Option.some (Path.path "/home/u/.w/s-1/scratch")

def scmd (s : String) : String := shape (Assess.command root scratch s)

#[test]
def test_scratch_paths_are_scratch : Bool :=
    String.beq (scmd "cd /home/u/.w/s-1/scratch && rm -rf *") "scratch"
        && String.beq (scmd "rm -rf $WEAVER_SCRATCH/build") "scratch"
        && String.beq (scmd "cd $WEAVER_SCRATCH && make") "scratch"
        && String.beq (shape (Assess.path root scratch "/home/u/.w/s-1/scratch/a.mo")) "scratch"
        && String.beq (shape (Assess.path root scratch "/home/u/.w/s-1/scratch")) "scratch"

#[test]
def test_a_mixed_pick_is_not_scratch : Bool :=
    String.beq (scmd "rm -rf /home/u/.w/s-1/scratch/x && rm src/a.mo") "inside"

#[test]
def test_a_pathless_command_runs_in_the_workspace : Bool :=
    String.beq (scmd "make test") "inside"

#[test]
def test_other_variables_stay_dynamic : Bool :=
    String.beq (scmd "rm -rf $HOME/x") "unknown"

#[test]
def test_a_scratch_scope_line : Bool :=
    String.beq (Assess.scope_line root Reach.scratch) "inside the scratch directory"

/// A script that ASSIGNS either name loses the expansion: the shell could
/// point the variable anywhere, so the word stays dynamic.
#[test]
def test_an_assignment_disables_the_scratch_expansion : Bool :=
    String.beq (scmd "WEAVER_SCRATCH=$HOME rm -rf \"$WEAVER_SCRATCH\"/Documents") "unknown"
        && String.beq (scmd "export TMPDIR=/elsewhere; rm -rf \"$TMPDIR\"/x") "unknown"
        && String.beq (scmd "rm -rf \"$WEAVER_SCRATCH\"/build") "scratch"
