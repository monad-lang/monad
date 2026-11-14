/// Live tests for the floor's user-facing surface (`sys/src/sys.mo`).
///
/// Separate from `errno_tests.mo`/`signal_tests.mo`/`text_tests.mo`, which
/// are PURE: this file touches the operating system, so it is the one place
/// a native's four wiring points are exercised rather than type-checked.
///
/// The reference is `process_id`: `Sys.pid` must answer the same number, on
/// the interpreter (which reads `libc::getpid`) and compiled (which calls
/// `monad_sys_int`).

use sys::signal {Signal}
use sys::sys {
    Host.uname, Stat, Stat.is_dir, Stat.is_file, Sys.kill, Sys.list_dir,
    Sys.pid, Sys.stat, SysError, Uname,
}

/// Our own pid, through the floor, against the runtime's own answer.
/// `process_id` is the runtime's pid native and `Sys.pid` is the floor's;
/// both exist during the migration, so this pins them to each other.
#[test]
def test_pid_equals_the_runtimes_process_id : IO Bool := do {
    let me <- Sys.pid;
    let runtime : I64 := process_id;
    return (I64.beq me runtime)
}

/// `/` is a directory on every POSIX system, so this reads what the test
/// needs from one known-good path.
#[test]
def test_stat_reports_a_directory : IO Bool := do {
    let r <- Sys.stat "/";
    return (stat_is_dir r)
}

def stat_is_dir (r : Result SysError Stat) : Bool :=
    match r {
        Result.ok s => Stat.is_dir s,
        Result.err _ => false,
    }

def stat_is_file (r : Result SysError Stat) : Bool :=
    match r {
        Result.ok s => Stat.is_file s,
        Result.err _ => false,
    }

/// A missing path is `not_found`, not a zeroed `Stat`: `file_exists` is
/// built on that distinction.
#[test]
def test_stat_of_a_missing_path_is_not_found : IO Bool := do {
    let r <- Sys.stat "/no/such/path/at/all";
    return (stat_err_is_missing r)
}

def stat_err_is_missing (r : Result SysError Stat) : Bool :=
    match r {
        Result.ok _ => false,
        Result.err e => SysError.is_missing e,
    }

/// A file we create ourselves: `is_file` true and `is_dir` false, the pair
/// the two type-bit decoders have to keep apart.
#[test]
def test_stat_tells_a_file_from_a_directory : IO Bool := do {
    let pid <- Sys.pid;
    let path := "/tmp/monad_sys_stat_" ++ I64.to_string pid;
    let _ <- IO.write_file (Path.path path) "x";
    let r <- Sys.stat path;
    let _ <- exec_cmd "rm" ["-f", path];
    return (stat_is_file r)
}

/// `Sys.list_dir` drops `.`/`..` and sorts; `/` always has entries.
#[test]
def test_list_dir_of_root_is_not_empty : IO Bool := do {
    let r <- Sys.list_dir "/";
    return (list_ok r)
}

def list_ok (r : Result SysError (List String)) : Bool :=
    match r {
        Result.ok names => I64.gt (List.length names) 0,
        Result.err _ => false,
    }

/// `uname`'s sysname is `Linux` on the first backend; Phase 10 moves the
/// table behind `SystemBackend`, at which point this becomes backend-specific.
#[test]
def test_uname_sysname : IO Bool := do {
    let r <- Host.uname;
    return (uname_is_linux r)
}

def uname_is_linux (r : Result SysError Uname) : Bool :=
    match r {
        Result.ok u => String.beq u.sysname "Linux",
        Result.err _ => false,
    }

/// A signal that delivers nothing, to ourselves: the cheapest end-to-end
/// check that signal-number encoding and `kill(2)` agree.
#[test]
def test_signal_zero_to_self_succeeds : IO Bool := do {
    let me <- Sys.pid;
    let r <- Sys.kill me (Signal.other 0);
    return (kill_ok r)
}

def kill_ok (r : Result SysError Unit) : Bool :=
    match r {
        Result.ok _ => true,
        Result.err _ => false,
    }

/// A pid that cannot exist is `no_such_process`, the kind a sampler skips
/// silently rather than surfacing.
#[test]
def test_signal_to_a_missing_pid_is_no_such_process : IO Bool := do {
    let r <- Sys.kill 2147483647 (Signal.other 0);
    return (kill_missing r)
}

def kill_missing (r : Result SysError Unit) : Bool :=
    match r {
        Result.ok _ => false,
        Result.err e => SysError.is_missing e,
    }
