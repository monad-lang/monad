// OS-specific I/O: console output and the filesystem. The `IO` type
// itself lives in init/io.mo (pure, portable); everything here is a
// genuine side effect, hence std/. See AGENTS.md's "init vs std"
// section.

// Qualified (not bare `use path {...}`) deliberately: the Rust
// reference's module loader registers std/*.mo siblings under their
// full `std.<name>` path (to avoid colliding with init/io.mo's own
// bare `io`), and has no base-dir-relative fallback the way the
// self-hosted loader does -- a bare `use path {...}` here resolves
// fine self-hosted but fails "module not found: path" under `cargo
// run`. Qualified works identically on both sides.
use std.path {Path}

#[native print_str]
def IO.println (s: String) : IO Unit

#[native "write_file"]
def IO.write_file_native (path : String) (content : String) : IO Unit

// TODO Return Option and none on failure
#[native "read_file"]
def IO.read_file_native (path : String) : IO String

#[native "file_exists"]
def IO.file_exists_native (path : String) : IO Bool

#[native "is_dir"]
def IO.is_dir_native (path : String) : IO Bool

// Bare entry names (not full paths), sorted, one directory level.
#[native "list_dir"]
def IO.list_dir_native (path : String) : IO (List String)

#[native "get_env"]
def IO.get_env (s : String) : IO (Option String)

// Milliseconds from an arbitrary fixed origin (CLOCK_MONOTONIC). Only
// DIFFERENCES between two readings mean anything -- the origin is not an
// epoch and is not comparable across processes.
//
// `IO` because reading a clock is a side effect in the same sense
// reading a file is: two calls in one expression may legitimately differ,
// so it must not be something the evaluator can duplicate, reorder or
// share. `std/bench.mo`'s `Bench.now` is the name callers use.
#[native current_time]
def IO.current_time : IO I64

def IO.write_file (path : Path) (content : String) : IO Unit :=
    IO.write_file_native (Path.to_string path) content

def IO.read_file (path : Path) : IO String :=
    IO.read_file_native (Path.to_string path)

def IO.file_exists (path : Path) : IO Bool :=
    IO.file_exists_native (Path.to_string path)

def IO.is_dir (path : Path) : IO Bool :=
    IO.is_dir_native (Path.to_string path)

def IO.list_dir (path : Path) : IO (List String) :=
    IO.list_dir_native (Path.to_string path)

// TODO support constraints
// def IO.fprintln [ToString A] (a: A) : IO Unit :=
//   IO.println (ToString.to_string a)
