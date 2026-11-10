/// The floor's user-facing surface: one thin `IO` wrapper per native, with
/// errno decoded into `SysError`. Everything above this file is pure Monad.
///
/// Syscall failures stay in the payload (`IO (Result SysError A)`), not in
/// `IO.Error`: a sampler looping over hundreds of pids must skip
/// `no_such_process` and continue, and signalling a list of processes needs
/// per-pid results.

use lib::errno {SysError, SysError.of_errno, SysErrorKind}
use lib::raw {Dir, sys_dir_close, sys_dir_next, sys_dir_open, sys_int, sys_stat, sys_str}
use lib::signal {Signal, Signal.number}
use lib::text {Text.parse_i64, Text.sort, Text.words}

/// `IO.map`, which `init` does not provide yet.
def io_map (f : A -> B) (m : IO A) : IO B :=
    match m {
        IO.mk raw => IO.mk (RawIO.bind raw (fn x => RawIO.pure (f x))),
    }

/// `rc < 0` is `-errno`; see `raw.mo`.
def sys_unit (op : String) (rc : I64) : Result SysError Unit :=
    if I64.lt rc 0 then Result.err (SysError.of_errno op (0 - rc)) else Result.ok Unit.unit

def sys_i64 (op : String) (rc : I64) : Result SysError I64 :=
    if I64.lt rc 0 then Result.err (SysError.of_errno op (0 - rc)) else Result.ok rc

def sys_string (op : String) (r : Result I64 String) : Result SysError String :=
    match r {
        Result.ok s => Result.ok s,
        Result.err e => Result.err (SysError.of_errno op e),
    }

pub def Sys.pid : IO I64 := IO.mk (sys_int 0 0 0)

pub def Sys.ppid : IO I64 := IO.mk (sys_int 1 0 0)

pub def Sys.uid : IO I64 := IO.mk (sys_int 2 0 0)

pub def Sys.kill (pid : I64) (s : Signal) : IO (Result SysError Unit) :=
    io_map (sys_unit "kill") (IO.mk (sys_int 4 pid (Signal.number s)))

pub def Sys.priority (pid : I64) : IO (Result SysError I64) :=
    io_map (sys_i64 "getpriority") (IO.mk (sys_int 5 pid 0))

pub def Sys.set_priority (pid : I64) (prio : I64) : IO (Result SysError Unit) :=
    io_map (sys_unit "setpriority") (IO.mk (sys_int 6 pid prio))

pub def Sys.clock_ticks : IO (Result SysError I64) :=
    io_map (sys_i64 "sysconf") (IO.mk (sys_int 7 0 0))

pub def Sys.page_size : IO (Result SysError I64) :=
    io_map (sys_i64 "sysconf") (IO.mk (sys_int 7 1 0))

pub def Sys.cpu_count : IO (Result SysError I64) :=
    io_map (sys_i64 "sysconf") (IO.mk (sys_int 7 2 0))

pub def Sys.readlink (path : String) : IO (Result SysError String) :=
    io_map (sys_string "readlink") (IO.mk (sys_str 0 path))

pub def Sys.getenv (name : String) : IO (Result SysError String) :=
    io_map (sys_string "getenv") (IO.mk (sys_str 2 name))

/// Bare entry names, one directory level, sorted. The loop runs HERE, over
/// `sys_dir_next`; the floor only opens, hands out one name at a time and
/// closes, so nothing above it sees a joined payload.
pub def Sys.list_dir (path : String) : IO (Result SysError (List String)) := do {
    let opened <- IO.mk (sys_dir_open path);
    match opened {
        Result.ok d => do {
            // The handle is used to iterate AND to close, so it travels as
            // a `Shared`: `Shared.get` is a read, and the close is a second
            // read of the same owned stream (the `IO.write_bytes_all`
            // idiom).
            let handle : Shared Dir := Shared.of d;
            let found <- dir_entries handle List.empty;
            let _ <- IO.mk (sys_dir_close (Shared.get handle));
            return found
        },
        Result.err e => IO.pure (Result.err (SysError.of_errno "list_dir" e)),
    }
}

/// One `sys_dir_next` per recursion. An empty name is the end of the
/// stream (POSIX never yields one); the sorted list is built on the way
/// back out, so an error discards the partial one.
#[terminating]
def dir_entries (handle : Shared Dir) (acc : List String) : IO (Result SysError (List String)) := do {
    let next <- IO.mk (sys_dir_next (Shared.get handle));
    match next {
        // Typed local: the pattern binder itself infers as `A` before the
        // affine check runs, and `A` is not `Copy`.
        Result.ok name =>
            let piece : String := name in
            if String.beq piece "" then IO.pure (Result.ok (Text.sort acc))
            else dir_entries handle (List.cons piece acc),
        Result.err e => IO.pure (Result.err (SysError.of_errno "list_dir" e)),
    }
}

/// A `/proc` or `/sys` file: these `stat()` as size 0, so a reader that
/// trusts the reported size reads nothing.
pub def Sys.read_small (path : String) : IO (Result SysError String) :=
    io_map (sys_string "read_small") (IO.mk (sys_str 3 path))

pub struct Stat {
    mode : I64,
    size : I64,
    mtime : I64
}

pub struct StatVfs {
    block_size : I64,
    fragment_size : I64,
    blocks : I64,
    blocks_free : I64,
    blocks_available : I64,
    files : I64,
    files_free : I64
}

pub def Sys.stat (path : String) : IO (Result SysError Stat) :=
    io_map (parse_stat "stat") (IO.mk (sys_stat 0 path))

pub def Sys.lstat (path : String) : IO (Result SysError Stat) :=
    io_map (parse_stat "lstat") (IO.mk (sys_stat 1 path))

pub def Sys.statvfs (path : String) : IO (Result SysError StatVfs) :=
    io_map parse_statvfs (IO.mk (sys_stat 2 path))

def parse_error (op : String) : SysError :=
    { kind := SysErrorKind.other, errno := 0, op := op }

def parse_stat (op : String) (r : Result I64 String) : Result SysError Stat :=
    match sys_string op r {
        Result.ok s =>
            match Text.words s {
                List.cons mode rest =>
                    match rest {
                        List.cons size rest2 =>
                            match rest2 {
                                List.cons mtime _ => build_stat mode size mtime,
                                _ => Result.err (parse_error op),
                            },
                        _ => Result.err (parse_error op),
                    },
                _ => Result.err (parse_error op),
            },
        Result.err e => Result.err e,
    }

def build_stat (mode : String) (size : String) (mtime : String) : Result SysError Stat :=
    match Text.parse_i64 mode {
        Result.ok m =>
            match Text.parse_i64 size {
                Result.ok z =>
                    match Text.parse_i64 mtime {
                        Result.ok t =>
                        // Bound with an annotation: a bare struct literal in argument
                        // position is the documented miscompile (AGENTS.md Gotchas).
                        let st : Stat := { mode := m, size := z, mtime := t } in
                        Result.ok st,
                        Result.err _ => Result.err (parse_error "stat"),
                    },
                    Result.err _ => Result.err (parse_error "stat"),
            },
        Result.err _ => Result.err (parse_error "stat"),
    }

def statvfs_short : Result SysError StatVfs :=
    Result.err (parse_error "statvfs")

/// Parse the packed statvfs line field by field; the C guarantees seven
/// space-separated decimal words, and a short line is a malformed payload.
def parse_statvfs (r : Result I64 String) : Result SysError StatVfs :=
    match sys_string "statvfs" r {
        Result.ok s => parse_statvfs_words (Text.words s),
        Result.err e => Result.err e,
    }

def parse_statvfs_words (ws : List String) : Result SysError StatVfs :=
    match ws {
        List.cons b rest =>
            match rest {
                List.cons fs rest2 =>
                    match rest2 {
                        List.cons blk rest3 =>
                            match rest3 {
                                List.cons bf rest4 =>
                                    match rest4 {
                                        List.cons ba rest5 =>
                                            match rest5 {
                                                List.cons fi rest6 =>
                                                    match rest6 {
                                                        List.cons ff _ => build_statvfs b fs blk bf ba fi ff,
                                                        List.empty => statvfs_short,
                                                    },
                                                List.empty => statvfs_short,
                                            },
                                        List.empty => statvfs_short,
                                    },
                                List.empty => statvfs_short,
                            },
                        List.empty => statvfs_short,
                    },
                List.empty => statvfs_short,
            },
        List.empty => statvfs_short,
    }

def build_statvfs (b : String) (fs : String) (blk : String) (bf : String) (ba : String) (fi : String) (ff : String) : Result SysError StatVfs :=
    match Text.parse_i64 b {
        Result.ok bv =>
            match Text.parse_i64 fs {
                Result.ok fsv =>
                    match Text.parse_i64 blk {
                        Result.ok blkv =>
                            match Text.parse_i64 bf {
                                Result.ok bfv =>
                                    match Text.parse_i64 ba {
                                        Result.ok bav =>
                                            match Text.parse_i64 fi {
                                                Result.ok fiv =>
                                                    match Text.parse_i64 ff {
                                                        Result.ok ffv => Result.ok {
                                                            block_size := bv,
                                                            fragment_size := fsv,
                                                            blocks := blkv,
                                                            blocks_free := bfv,
                                                            blocks_available := bav,
                                                            files := fiv,
                                                            files_free := ffv
                                                        },
                                                        Result.err _ => statvfs_short,
                                                    },
                                                Result.err _ => statvfs_short,
                                            },
                                        Result.err _ => statvfs_short,
                                    },
                                Result.err _ => statvfs_short,
                            },
                        Result.err _ => statvfs_short,
                    },
                Result.err _ => statvfs_short,
            },
        Result.err _ => statvfs_short,
    }
