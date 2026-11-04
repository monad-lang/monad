/// weaver / danger -- the destructive-command rules auto mode checks before
/// it lets a command run. Each rule reads one simple command's name and
/// words (`shell_words.mo`) and names why it must still be approved. The
/// rules that depend on WHERE a path points (`rm -r` outside the
/// workspace, a write redirect outside it) live in `assess.mo`, which
/// knows the working directory.
use std::list {List.any}
use weaver::shell_words {ShellWord}

/// Why `name args` needs approval even in auto mode; none when no rule
/// matches. `name` is the command word as written (`/bin/rm` reads as `rm`).
pub def Danger.command (name : String) (args : List ShellWord) : Option String :=
    let n : String := Danger.base_name name in
    let ts : List String := texts args in
    if one_of n ["sudo", "su", "doas", "pkexec", "run0"] then Option.some (String.concat n " runs as another user")
    else if is_disk_tool n then Option.some (String.concat n " formats or repartitions a disk")
    else if one_of n ["shutdown", "reboot", "poweroff", "halt"] then Option.some (String.concat n " stops the machine")
    else if String.beq n "systemctl" then systemctl_rule ts
    else if one_of n ["killall", "pkill"] then Option.some (String.concat n " kills processes by name")
    else if String.beq n "kill" then kill_rule ts
    else if String.beq n "dd" then dd_rule ts
    else if String.beq n "find" then find_rule ts
    else if String.beq n "xargs" then xargs_rule ts
    else if one_of n ["shred", "truncate", "wipe"] then Option.some (String.concat n " destroys file contents")
    else if String.beq n "git" then Danger.git ts
    else if String.beq n "gh" then gh_rule ts
    else if one_of n ["cargo", "npm", "yarn", "pnpm", "gem", "twine", "poetry"] then publish_rule n ts
    else if String.starts_with "nix-collect-garbage" n then nix_gc_rule ts
    else if one_of n ["docker", "podman"] then prune_rule n ts
    else Option.none

/// `/usr/bin/rm` -> `rm`.
pub def Danger.base_name (t : String) : String :=
    String.from_list (List.reverse (after_slash (String.to_list t) List.empty))

/// The bytes after the last `/`, reversed.
#[partial]
def after_slash (bs : List U8) (acc : List U8) : List U8 :=
    match bs {
        List.empty => acc,
        List.cons b rest => after_slash rest (if U8.to_i64 b == 47 then List.empty else List.cons b acc),
    }

#[partial]
def texts (ws : List ShellWord) : List String :=
    match ws {
        List.empty => List.empty,
        List.cons w rest => List.cons w.text (texts rest),
    }

def one_of (t : String) (ks : List String) : Bool :=
    List.any (fn (k : String) => String.beq k t) ks

def has (k : String) (ts : List String) : Bool :=
    List.any (fn (t : String) => String.beq k t) ts

def has_prefix (k : String) (ts : List String) : Bool :=
    List.any (fn (t : String) => String.starts_with k t) ts

/// A short-flag cluster (`-fdx`) holding `c`; never a `--long` flag.
pub def Danger.short_flag (c : String) (ts : List String) : Bool :=
    List.any (fn (t : String) => Bool.and (String.starts_with "-" t)
        (Bool.and (Bool.not (String.starts_with "--" t)) (String.contains t c))) ts

def is_disk_tool (n : String) : Bool :=
    String.starts_with "mkfs" n
        || one_of n ["mke2fs", "mkswap", "wipefs", "fdisk", "sfdisk", "gdisk", "sgdisk", "cfdisk", "parted", "blkdiscard"]

def systemctl_rule (ts : List String) : Option String :=
    if List.any (fn (t : String) => one_of t ["reboot", "poweroff", "halt", "kexec", "suspend", "hibernate"]) ts
    then Option.some "systemctl stops the machine"
    else Option.none

/// `kill -9 -1` signals every process the user owns.
def kill_rule (ts : List String) : Option String :=
    match List.last ts {
        Option.some t => if String.beq t "-1" then Option.some "kill -1 signals every process" else Option.none,
        Option.none => Option.none,
    }

def dd_rule (ts : List String) : Option String :=
    if has_prefix "of=" ts then Option.some "dd writes raw bytes over its target" else Option.none

def find_rule (ts : List String) : Option String :=
    if has "-delete" ts then Option.some "find -delete removes files"
    else if Bool.and (Bool.or (has "-exec" ts) (has "-execdir" ts)) (has_rm ts) then Option.some "find -exec rm removes files"
    else Option.none

def xargs_rule (ts : List String) : Option String :=
    if has_rm ts then Option.some "xargs rm removes files" else Option.none

def has_rm (ts : List String) : Bool :=
    List.any (fn (t : String) => one_of (Danger.base_name t) ["rm", "shred", "unlink"]) ts

// ── git ─────────────────────────────────────────────────────────────────

/// The git subcommand and its words, after the global options
/// (`-C dir`, `-c k=v`, `--git-dir=..`, `--no-pager`).
#[partial]
def git_sub (ts : List String) : List String :=
    match ts {
        List.empty => ts,
        List.cons t rest =>
            if Bool.or (String.beq t "-C") (String.beq t "-c") then git_sub (List.tail rest)
            else if String.starts_with "-" t then git_sub rest
            else ts,
    }

pub def Danger.git (ts : List String) : Option String :=
    match git_sub ts {
        List.empty => Option.none,
        List.cons sub rest => git_rule sub rest,
    }

def git_rule (sub : String) (ts : List String) : Option String :=
    if String.beq sub "push" then git_push ts
    else if String.beq sub "reset" then
        (if Bool.or (has "--hard" ts) (has "--merge" ts) then Option.some "git reset --hard discards uncommitted changes" else Option.none)
    else if String.beq sub "clean" then
        (if Bool.or (Danger.short_flag "f" ts) (has "--force" ts) then Option.some "git clean deletes untracked files" else Option.none)
    else if String.beq sub "checkout" then git_checkout ts
    else if String.beq sub "restore" then
        (if Bool.and (has "--staged" ts) (Bool.not (Bool.or (has "--worktree" ts) (Danger.short_flag "W" ts))) then Option.none
            else Option.some "git restore discards working-tree changes")
    else if String.beq sub "branch" then
        (if Bool.or (Danger.short_flag "D" ts) (Bool.and (Bool.or (has "--delete" ts) (Danger.short_flag "d" ts)) (Bool.or (has "--force" ts) (Danger.short_flag "f" ts)))
            then Option.some "git branch -D deletes an unmerged branch" else Option.none)
    else if String.beq sub "stash" then
        (if Bool.or (has "drop" ts) (has "clear" ts) then Option.some "git stash drop/clear discards stashed work" else Option.none)
    else if one_of sub ["filter-branch", "filter-repo"] then Option.some (String.concat "git " (String.concat sub " rewrites history"))
    else if String.beq sub "reflog" then
        (if has "expire" ts then Option.some "git reflog expire drops recovery points" else Option.none)
    else if String.beq sub "update-ref" then
        (if Danger.short_flag "d" ts then Option.some "git update-ref -d deletes a ref" else Option.none)
    else Option.none

def git_push (ts : List String) : Option String :=
    let forced : Bool := has_prefix "--force" ts || Danger.short_flag "f" ts || has "--mirror" ts in
    let deletes : Bool := has "--delete" ts || Danger.short_flag "d" ts || has "--prune" ts
        || List.any (fn (t : String) => String.starts_with ":" t) ts in
    let plus : Bool := List.any (fn (t : String) => String.starts_with "+" t) ts in
    if Bool.or forced plus then Option.some "git push --force rewrites remote history"
    else if deletes then Option.some "git push deletes remote refs"
    else Option.none

/// `git checkout -- <paths>`, `git checkout .` and `-f` overwrite local
/// changes.
def git_checkout (ts : List String) : Option String :=
    if has "--" ts || has "." ts || has "--force" ts || Danger.short_flag "f" ts
    then Option.some "git checkout discards working-tree changes"
    else Option.none

// ── hosts, packages, stores ─────────────────────────────────────────────

def gh_rule (ts : List String) : Option String :=
    match ts {
        List.cons area rest => match rest {
            List.cons verb _ =>
                if Bool.and (one_of area ["repo", "release"]) (one_of verb ["delete", "archive"])
                then Option.some (String.concat "gh " (String.concat area (String.concat " " (String.concat verb " cannot be undone here"))))
                else Option.none,
            List.empty => Option.none,
        },
        List.empty => Option.none,
    }

def publish_rule (n : String) (ts : List String) : Option String :=
    if Bool.or (has "publish" ts) (Bool.or (has "upload" ts) (Bool.and (String.beq n "gem") (has "push" ts)))
    then Option.some (String.concat n " publishes a package")
    else Option.none

def nix_gc_rule (ts : List String) : Option String :=
    if Bool.or (has "-d" ts) (has_prefix "--delete-old" ts) then Option.some "nix-collect-garbage -d deletes old generations"
    else Option.none

def prune_rule (n : String) (ts : List String) : Option String :=
    if has "prune" ts then Option.some (String.concat n " prune deletes containers, images or volumes")
    else if Bool.and (has "system" ts) (has "reset" ts) then Option.some (String.concat n " system reset deletes everything")
    else Option.none
