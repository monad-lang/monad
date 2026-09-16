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
use lib::path {Path}

#[native print_str]
pub def IO.println (s: String) : IO Unit

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

// Nanoseconds from the same arbitrary `CLOCK_MONOTONIC` origin as
// `IO.current_time` above -- same caveats (differences only, not an
// epoch, not comparable across processes), just finer.
//
// Exists because per-test timing needs sub-millisecond resolution: the
// self-hosted test runner reports each test's duration the way the Rust
// runner's `format_duration` does (`core/src/lib.rs`), and most tests
// finish well inside one millisecond, where `current_time` can only
// ever say "0ms". The native hands over RAW NANOSECONDS and nothing
// else -- every unit conversion and all the ns/us/ms/s formatting is
// done in Monad, by the driver this runner synthesizes
// (`lang/codegen/test_driver.mo`).
#[native current_time_nano]
def IO.current_time_nano : IO I64

def IO.write_file (path : Path) (content : String) : IO Unit :=
    IO.write_file_native (Path.to_string path) content

pub def IO.read_file (path : Path) : IO String :=
    IO.read_file_native (Path.to_string path)

pub def IO.file_exists (path : Path) : IO Bool :=
    IO.file_exists_native (Path.to_string path)

pub def IO.is_dir (path : Path) : IO Bool :=
    IO.is_dir_native (Path.to_string path)

pub def IO.list_dir (path : Path) : IO (List String) :=
    IO.list_dir_native (Path.to_string path)

// TODO support constraints
// def IO.fprintln [ToString A] (a: A) : IO Unit :=
//   IO.println (ToString.to_string a)
