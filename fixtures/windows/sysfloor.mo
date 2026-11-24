#![mote { name := "sysfloor", deps := [init, std] }]

// The sys floor, which is the one place this target is BROADER than the wasm
// profiles: `sys_int`/`sys_str`/`sys_stat`/`sys_dir_*` are implemented over
// Win32 in `platform_win32.c` (GetEnvironmentVariable, _stat64,
// FindFirstFile), so a Windows program can ask about its environment and its
// files. The wasm profiles refuse all of it.
//
// Every check below is relative to the process's own working directory, and
// that is deliberate: under wine a Unix absolute path is not a path the
// Windows API can read (there is a `Z:` mapping, but `_stat64` on the raw
// spelling is not it), so a fixture that took one would be asserting about
// wine's path translation rather than about this runtime. The gate starts the
// process in a directory it prepared, so `"."` and a sibling name are enough.
//
// This is a genuine difference from POSIX and is worth stating: a Monad
// program compiled for Windows reads Windows paths.
use std::path {Path}
use std::process {process_id}
open IO {println}

def flag (b : Bool) : String := if b then "true" else "false"

/// Written as an explicit walk rather than `List.any (fn (p : Path) => ...)`:
/// the polymorphic `pred` there resolves to `false` for this predicate shape,
/// and this fixture is a test of the RUNTIME's directory listing, not of the
/// checker's lambda inference. (Recorded because it is a real divergence worth
/// its own investigation on the native target.)
#[decreasing xs]
def has_name (want : String) (xs : List Path) : Bool :=
    match xs {
        List.empty => false,
        List.cons p rest =>
            if String.beq (Path.file_name p) want then true else has_name want rest,
    }

def main (args : List String) : IO Unit := do {
    let env <- IO.get_env "MONAD_WINDOWS_GATE";
    println ("env: " ++ flag (Bool.not (Option.is_none env)));
    let here : Path := Path.path ".";
    let names <- IO.list_dir here;
    // The gate puts `present.txt` here, so a listing that WORKS contains it by
    // name. Counted by membership rather than by length: `FindFirstFile`
    // reports "." and ".." and the native strips them, so a small directory is
    // a legitimate answer and a length threshold would be testing the gate's
    // own setup. An unreadable directory is the empty listing.
    let listed := has_name "present.txt" names;
    println ("dir: " ++ flag listed);
    let present <- IO.file_exists (Path.join here (Path.path "present.txt"));
    println ("found: " ++ flag present);
    let missing <- IO.file_exists (Path.join here (Path.path "absent.txt"));
    println ("absent: " ++ flag (Bool.not missing));
    // `_stat64`'s size for a one-byte file, which is also the check that
    // `sys_stat`'s field order matches the Monad side's parser.
    let size <- IO.file_size (Path.join here (Path.path "present.txt"));
    println ("size: " ++ flag (match size {
        Option.some n => I64.beq n 1,
        Option.none => false,
    }));
    println ("pid: " ++ flag (I64.gt process_id 0))
}
