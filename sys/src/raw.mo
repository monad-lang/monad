/// The native floor: three flag-multiplexed syscalls. Everything above them
/// is pure Monad (`lang/src/cfg.mo`-style modules here), so the C stays
/// syscall-shaped and the parsing is testable.
///
/// Payloads are `String`/`I64` only, by design: `ByteBuf` lives in `std`,
/// and `sys` may depend on `init` alone. A call that would naturally fill an
/// out-parameter therefore returns its fields packed as text and the Monad
/// side splits them.
///
/// Failure is `-errno` in the `I64` shape and `Result.err errno` in the
/// `String` shapes; `SysError.of_errno` (`errno.mo`) maps it.
///
/// Package-private rather than `priv` on purpose: `priv` is module-only, and
/// the user-facing wrappers are the next step, in `sys/src/sys.mo`.
///
/// NOT WIRED YET: these declarations are inert until the four wiring points
/// (core_native.rs, codegen/src/natives.mo, runtime/src/platform_posix.c,
/// and the `wasm_os_only_natives` gate) land, which waits on the
/// `runtime/memory` branch rewriting those same files.

/// Integer syscalls. `op` selects the call; unused arguments are 0.
///   0 getpid    1 getppid   2 getuid    3 geteuid
///   4 kill(pid, signal)    5 getpriority(who)
///   6 setpriority(who, prio)
///   7 sysconf(a: 0 CLK_TCK, 1 PAGESIZE, 2 NPROCESSORS_ONLN)
#[native "sys_int"]
def sys_int (op : I64) (a : I64) (b : I64) : RawIO I64

/// String-shaped syscalls. `arg` is a path or a uname field name.
///   0 readlink(path)           -- the target, not resolved
///   1 uname(field)             -- "sysname" | "release" | "machine" | "nodename"
///   2 getenv(name)
///   3 list_dir(path)           -- entries joined by NUL, unsorted
///   4 read_small(path)         -- open/read-to-EOF/close, for /proc and /sys
///                                 files, which stat() as size 0
/// `Result.err errno` on failure.
#[native "sys_str"]
def sys_str (op : I64) (arg : String) : RawIO (Result I64 String)

/// `stat` fields packed as space-separated decimal words:
///   0 stat(path)     -> "mode size mtime"
///   1 lstat(path)    -> the same, without following a symlink
///   2 statvfs(path)  -> "bsize frsize blocks bfree bavail files ffree"
/// `Result.err errno` on failure; `not_found` is a missing path, which is
/// exactly what `file_exists`/`is_dir` turn into `false`.
#[native "sys_stat"]
def sys_stat (op : I64) (path : String) : RawIO (Result I64 String)
