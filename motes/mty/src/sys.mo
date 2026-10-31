// mty / sys -- the PTY FFI bindings.
//
// These are the ONLY foreign calls in the harness, and they are
// package-private (unmarked) so `spawn.mo` can reach them while no other
// mote can. `forkpty`, `execl` and `_exit` are declared PURE on purpose:
// the child branch after `forkpty` returns 0 must run no Monad allocation,
// and a `RawIO` extern boxes its result with `monad_io_pure` INSIDE the
// generated wrapper (lang/src/codegen/emit.mo), which would allocate in the
// child. The other calls are `RawIO` per AGENTS.md's side-effect rule.
//
// Linux/glibc ABI (the CI target). Every C `int` is `I32`: only I32 returns
// are sign-extended, and `pid_t`/`int` are 32-bit. `forkpty` lives in libc
// on glibc >= 2.34; there is no `[link] libs = ["util"]` here.
//
// `execl` is variadic and may be declared only ONCE. Eight argv slots cover
// every wave-1 driver (argv[0] = the binary path, then up to seven args);
// absent slots are each their own `Ptr.null` at the call site.

#[extern "c"]
def forkpty (amaster : Ptr) (name : Ptr) (termp : Ptr) (winp : Ptr) : I32

#[extern "c" {link_name := "execl"}]
def execl8 (path : Ptr) (a0 : Ptr) (a1 : Ptr) (a2 : Ptr) (a3 : Ptr)
           (a4 : Ptr) (a5 : Ptr) (a6 : Ptr) (a7 : Ptr) : I32

#[extern "c" {link_name := "_exit"}]
def exit_now (code : I32) : I32

#[extern "c"]
def setenv (name : String) (value : String) (overwrite : I32) : RawIO I32

#[extern "c"]
def unsetenv (name : String) : RawIO I32

#[extern "c"]
def ioctl (fd : I32) (request : I64) (arg : Ptr) : RawIO I32

#[extern "c"]
def kill (pid : I32) (sig : I32) : RawIO I32

#[extern "c"]
def waitpid (pid : I32) (status : Ptr) (options : I32) : RawIO I32

#[extern "c"]
def access (path : String) (mode : I32) : I32

// ── Typed constants ──────────────────────────────────────────────────────
//
// The corpus does not spell I32 literals (see motes/ffi_example/src/libc.mo),
// so every narrow constant is built by conversion once, at top level.

def zero_i64 : I64 := 0
def zero_i32 : I32 := I64.to_i32 0
def one_i32 : I32 := I64.to_i32 1
def code_127 : I32 := I64.to_i32 127
def sig_kill : I32 := I64.to_i32 9
def sig_winch : I32 := I64.to_i32 28
def x_ok : I32 := I64.to_i32 1

/// Linux `TIOCSWINSZ` (`asm-generic/ioctls.h`). The request argument of
/// `ioctl` is an `unsigned long`, so it travels as I64.
def tiocswinsz : I64 := 0x5414
