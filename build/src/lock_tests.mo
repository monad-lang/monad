/// Tests for `build/src/lock.mo`: the `mote.lock` reader and writer.
///
/// The acceptance row they carry is Phase 3's "`mote.lock` survives a
/// write -> read -> write round trip" -- checked as byte equality of the two
/// renders, which is the property a committed lockfile needs (re-running
/// `monad fetch` with nothing changed must not dirty the working tree).
/// The rest pin the strictness: every way an entry can be wrong is an error
/// naming that entry, and only a foreign `version` is soft.

use build::lock {
  GitPin, LockRead, LockedGit, LockedMote, Lockfile,
  Lock.parse, Lock.pin_of, Lock.pin_to_string, Lock.read, Lock.render, Lock.source_of, Lock.write,
}
use std::io {}
use std::list {List.all, List.length}
use std::process {exec_cmd, process_id}

def commit_a : String := "0123456789abcdef0123456789abcdef01234567"
def commit_b : String := "89abcdef0123456789abcdef0123456789abcdef"
def sum_a : String := "sha256:00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"

def http_git : LockedGit :=
    let g : LockedGit := {
        url := "https://example.org/http",
        pin := GitPin.tag "v0.1.0",
        commit := commit_a,
        subdir := Option.some "motes/http",
    } in
    g

def http_entry : LockedMote :=
    let m : LockedMote := { name := "http", version := "0.1.0", checksum := sum_a, git := Option.some http_git } in
    m

def json_entry : LockedMote :=
    let m : LockedMote := { name := "json", version := "0.2.0", checksum := sum_a, git := Option.none } in
    m

def head_entry : LockedMote :=
    let g : LockedGit := { url := "file:///srv/a b?c#d", pin := GitPin.head, commit := commit_b, subdir := Option.none } in
    let m : LockedMote := { name := "aaa", version := "1.0.0", checksum := sum_a, git := Option.some g } in
    m

/// Deliberately out of name order: the render sorts.
def sample_lock : Lockfile :=
    let l : Lockfile := { motes := [json_entry, http_entry, head_entry] } in
    l

/// Render, parse the render, render again.
def rerender (text : String) : Option String :=
    match Lock.parse text {
        Result.err _ => Option.none,
        Result.ok r => match r {
            LockRead.loaded l => Option.some (Lock.render l),
            LockRead.unsupported _ => Option.none,
        }
    }

def loaded_count (text : String) : I64 :=
    match Lock.parse text {
        Result.err _ => 0 - 1,
        Result.ok r => match r {
            LockRead.loaded l => List.length l.motes,
            LockRead.unsupported _ => 0 - 2,
        }
    }

def parse_error (text : String) : String :=
    match Lock.parse text {
        Result.err e => e,
        Result.ok _ => "",
    }

#[test]
def test_render_round_trips_byte_for_byte : Bool :=
    let once := Lock.render sample_lock in
    match rerender once {
        Option.none => false,
        Option.some twice => String.beq once twice
    }

/// Sorted by name, keys in the §2b order, the display `source` built from
/// the structured keys, and a URL holding `?`/`#`/space survives because the
/// resolver never reads it back out of `source`.
#[test]
def test_render_is_sorted_and_in_spec_order : Bool :=
    let text := Lock.render sample_lock in
    String.beq text (String.concat_all [
        "# mote.lock -- written by `monad fetch` / `monad update`. Do not edit by hand.\nversion = 1\n",
        "\n[[mote]]\nname = \"aaa\"\nversion = \"1.0.0\"\n",
        "source = \"git+file:///srv/a b?c#d#", commit_b, "\"\n",
        "git_url = \"file:///srv/a b?c#d\"\ngit_ref = \"head\"\ngit_commit = \"", commit_b, "\"\n",
        "checksum = \"", sum_a, "\"\n",
        "\n[[mote]]\nname = \"http\"\nversion = \"0.1.0\"\n",
        "source = \"git+https://example.org/http?tag=v0.1.0&subdir=motes/http#", commit_a, "\"\n",
        "git_url = \"https://example.org/http\"\ngit_ref = \"tag:v0.1.0\"\ngit_commit = \"", commit_a, "\"\n",
        "git_subdir = \"motes/http\"\nchecksum = \"", sum_a, "\"\n",
        "\n[[mote]]\nname = \"json\"\nversion = \"0.2.0\"\nchecksum = \"", sum_a, "\"\n",
    ])

#[test]
def test_entry_order_does_not_change_the_render : Bool :=
    let other : Lockfile := { motes := [head_entry, json_entry, http_entry] } in
    String.beq (Lock.render other) (Lock.render sample_lock)

#[test]
def test_empty_lock_reads_as_no_entries : Bool :=
    loaded_count "version = 1\n" == 0

#[test]
def test_pins_round_trip_through_git_ref : Bool :=
    List.all (fn (s : String) => match Lock.pin_of s {
        Option.none => false,
        Option.some p => String.beq (Lock.pin_to_string p) s
    }) ["head", "tag:v1", "branch:main", "rev:abc"]

#[test]
def test_unknown_pins_are_rejected : Bool :=
    List.all (fn (s : String) => match Lock.pin_of s {
        Option.none => true,
        Option.some _ => false
    }) ["", "tag:", "branch", "HEAD", "commit:abc"]

#[test]
def test_source_has_no_query_for_a_head_pin_without_subdir : Bool :=
    let g : LockedGit := { url := "https://e.org/x", pin := GitPin.head, commit := commit_a, subdir := Option.none } in
    String.beq (Lock.source_of g) (String.concat "git+https://e.org/x#" commit_a)

/// A lockfile from a newer (or older) writer is not an error: the caller
/// warns and regenerates.
#[test]
def test_foreign_version_is_unsupported_not_an_error : Bool :=
    match Lock.parse "version = 2\n\n[[mote]]\nname = \"x\"\nfuture_key = 1\n" {
        Result.err _ => false,
        Result.ok r => match r {
            LockRead.unsupported n => n == 2,
            LockRead.loaded _ => false,
        }
    }

/// Keys this reader does not know are ignored, so a newer writer's
/// additions do not break an older reader.
#[test]
def test_unknown_entry_keys_are_ignored : Bool :=
    loaded_count (String.concat_all ["version = 1\n[[mote]]\nname = \"j\"\nversion = \"1\"\nchecksum = \"", sum_a, "\"\nmodules = 3\n"]) == 1

def entry_with (body : String) : String :=
    String.concat "version = 1\n[[mote]]\nname = \"bad\"\n" body

def full_git (commit : String) (git_ref : String) : String :=
    String.concat_all ["version = \"1\"\nchecksum = \"", sum_a, "\"\ngit_url = \"https://e.org/b\"\ngit_ref = \"", git_ref, "\"\ngit_commit = \"", commit, "\"\n"]

/// Every malformed shape is an error, and every message names the entry.
#[test]
def test_malformed_entries_are_errors_naming_the_entry : Bool :=
    List.all (fn (body : String) => String.starts_with "mote.lock entry `bad`" (parse_error (entry_with body))) [
        "checksum = \"sha256:00\"\n",
        String.concat_all ["checksum = \"", sum_a, "\"\n"],
        String.concat_all ["version = \"1\"\nchecksum = \"md5:", "00", "\"\n"],
        full_git "abc123" "tag:v1",
        full_git commit_a "latest",
        full_git (String.concat commit_a "0") "tag:v1",
        String.concat_all ["version = \"1\"\nchecksum = \"", sum_a, "\"\ngit_commit = \"", commit_a, "\"\n"],
        String.concat_all ["version = 1\nchecksum = \"", sum_a, "\"\n"],
    ]

#[test]
def test_structural_errors_are_reported : Bool :=
    String.beq (parse_error "[[mote]]\nname = \"x\"\n") "mote.lock has no `version`"
    && String.beq (parse_error "version = \"1\"\n") "mote.lock `version` must be an integer"
    && String.beq (parse_error "version = 1\n[mote]\nname = \"x\"\n") "mote.lock `mote` must be an array of tables (`[[mote]]`)"
    && String.starts_with "mote.lock entry 1: missing `name`" (parse_error "version = 1\n[[mote]]\nversion = \"1\"\n")
    && String.starts_with "mote.lock is not valid TOML" (parse_error "version = = 1\n")

// ─── Files ───

/// Pid-scoped: the corpus sweep runs sharded, and a fixed `/tmp` name would
/// collide across concurrent shards.
def scratch_lock_path : Path :=
    Path.path (String.concat_all ["/tmp/monad_lock_test_", I64.to_string process_id, ".lock"])

/// Write, read back, write again: the file's bytes are a fixed point.
#[test]
def test_write_then_read_is_a_fixed_point : IO Bool := do {
    let path : Path := scratch_lock_path;
    let w <- Lock.write path sample_lock;
    let r <- Lock.read path;
    let _rc <- exec_cmd "rm" ["-f", Path.to_string path];
    return (written_ok w && read_back_renders_as r (Lock.render sample_lock))
}

def written_ok (w : Result String Unit) : Bool :=
    match w {
        Result.err _ => false,
        Result.ok _ => true,
    }

def read_back_renders_as (r : Result String (Option LockRead)) (want : String) : Bool :=
    match r {
        Result.err _ => false,
        Result.ok found => match found {
            Option.none => false,
            Option.some l => match l {
                LockRead.loaded lock => String.beq (Lock.render lock) want,
                LockRead.unsupported _ => false,
            }
        }
    }

/// No lockfile is the ordinary first-fetch state: `none`, not an error.
#[test]
def test_missing_lock_reads_as_none : IO Bool := do {
    let r <- Lock.read (Path.path "/nonexistent/monad/mote.lock");
    return (match r {
        Result.err _ => false,
        Result.ok found => match found {
            Option.none => true,
            Option.some _ => false,
        }
    })
}
