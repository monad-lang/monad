# Windows (experimental)

Monad can **cross-compile to Windows x86_64** from a Linux or macOS host. The
output is a self-contained PE32+ `.exe` that runs on Windows with nothing
installed beside it.

**Compiling *on* Windows is not supported.** That is a deliberate scope line,
not an oversight: the difference between "emit Windows binaries" and "be the
compiler on Windows" is the difference between one runtime platform file and
a whole toolchain port, and only the first is what this target claims. A
Windows-hosted `monad` is future work.

```bash
monad build prog.mo --target x86_64-pc-windows-gnu -o prog
```

That writes `prog.exe`. The suffix is added when the name does not already end
in `.exe`, and never twice.

## What it is for

The target exists so a Monad program can be handed to someone on Windows, and
so the compiler's own target machinery is exercised against a platform that is
**not** ELF. It is a proof, not a product: see [Status](#status).

## What works

A core subset, chosen so that a real console program builds and runs:

| Area | What you get |
|---|---|
| Allocation | The same Boehm collector as native, linked statically |
| Console I/O | `IO.println`, `IO.print`, `IO.write_stdout`, `IO.read_line`, `IO.read_stdin_exact` |
| Time | `IO.current_time`, `IO.current_time_nano`, `IO.epoch_time_nano` |
| Sleeping | `sleepIO` / `sleep_io` |
| Files and environment | `IO.file_exists`, `IO.is_dir`, `IO.file_size`, `IO.list_dir`, `IO.get_env` (the `std` sys floor) |
| Process identity | `std.process::process_id` |

```monad
#![mote { name := "hello", deps := [init] }]

open IO {println}

def main (args : List String) : IO Unit :=
    println "hello from windows"
```

## What does not, and how you find out

Every refusable native is a **named compile error** naming the native, the
target and this page -- never a link failure, never a crash at run time:

```
error: native `proc_spawn` (needed by def `std.process::proc_spawn`) is not
available on target `x86_64-pc-windows-gnu` (windows): the Windows target is
core-only: no OS threads, processes, sockets or file streams
(see docs/src/windows.md)
```

| Refused | Why |
|---|---|
| Fibers: `fork_io`, `await_fiber`, `poll_fiber`, `cancel_fiber`, `fiber_wait_any` | Each is an OS thread on POSIX, and `await` has to block. There is no honest single-threaded substitute, and the collector here is built without thread support. |
| Scopes, channels: `scope_new`, `scope_fork`, `scope_drop`, `channel_*` | A channel `put` must park a thread. |
| Processes: `proc_spawn`, `proc_wait`, `proc_kill_group`, `proc_stream_fd`, `exec_child_output` | `CreateProcess` is not a drop-in for `fork`+`execvp`, and the child's inherited-stdio contract would have to be rebuilt out of handles. `exec_cmd` rides on these, so it is refused by implication. |
| TCP: `tcp_connect_timeout`, `tcp_listen`, `tcp_listen_on`, `tcp_accept`, `tcp_local_port` | Winsock is a separate DLL with its own startup, error space and handle type. |
| File streams: `stream_open`, `stream_poll`, `stream_seek`, `stream_set_timeout` | The CRT descriptor is an `int` with a per-process table this runtime cannot reason about. The three standard descriptors *do* work. |
| Terminal, watches: `term_ctl`, `inotify_*` | `inotify` is Linux; the console API is a different design. |

So `IO.read_file` and friends, `IO.read_line`'s file-stream form, and anything
under `std::concurrent` are out. `IO.list_dir` and `IO.file_size` work because
they go through the sys floor rather than a stream.

## Installing the toolchain

The compiler needs a **mingw-w64** C compiler, reachable as
`x86_64-w64-mingw32-gcc`, that can also find Boehm GC and mingw's own
mcfgthread library. Where the cross cc comes from is `MONAD_WINDOWS_CC`:

```bash
# Debian / Ubuntu
sudo apt install gcc-mingw-w64-x86-64
```

That gives you the compiler and mcfgthread, but **not** a mingw build of Boehm
GC, so the link needs a gc you built or unpacked for mingw:

```bash
MONAD_WINDOWS_CC='x86_64-w64-mingw32-gcc -isystem /opt/gc-mingw/include -L/opt/gc-mingw/lib' \
  monad build prog.mo --target x86_64-pc-windows-gnu -o prog
```

The value is split on whitespace and used as the program plus its leading
arguments, so flags belong in it. An empty value reads as unset.

### With nix

```bash
nix build .#monad-windows      # the compiler, with MONAD_WINDOWS_CC wired up
nix develop                    # a shell with the cross cc, gc and wine
```

`nix build .#monad-windows` produces the **same native compiler** as
`.#monad`, with one difference: its wrapper sets `MONAD_WINDOWS_CC` to a shim
(`monad-windows-gcc`) that execs `pkgsCross.mingwW64`'s gcc with the paths a
mingw link cannot find on its own -- Boehm's `include` and `lib`, and
mcfgthread's `lib`. The shim is deliberately *not* named `clang`: PATH is left
alone precisely so a native build from that binary still links with the host
`clang`, and only the Windows leg reaches mingw.

## How it is built

Target resolution lives in `llvm/src/target.mo`, the runtime in
`runtime/src/platform_win32.c`, the link in `llvm/src/link.mo`.

The flags are the ones measured to produce a binary that runs on a machine with
no Monad install:

- **`-static`** is mandatory, not tidiness. Without it the image imports
  `libgc-1.dll` and dies at load with
  `err:module:import_dll Library libgc-1.dll ... not found`. With it, the only
  imports are `KERNEL32.dll` and `msvcrt.dll`.
- **`-Wl,--stack=33554432`** replaces the POSIX runtime's `setrlimit`: Windows
  has no such call, and the image header's `SizeOfStackReserve` is the whole
  answer. 32 MiB matches the POSIX fiber stack.
- **`-DMONAD_TARGET_WINDOWS`** selects `platform_win32.c` in
  `runtime/src/runtime.c`.

The collector is built **without** `GC_THREADS`, which is correct precisely
because there are no fibers: every thread that could allocate is the one Boehm
already knows about.

## Verifying it

```bash
scripts/check-windows-target.sh path/to/monad
```

The gate builds four fixtures and checks:

1. **structure** -- each is a PE32+ x86-64 image importing neither a gc DLL
   nor nothing (it must import `KERNEL32`/`msvcrt`). This half needs no
   emulator, and it is where a wrong link line shows up.
2. **behaviour**, when `MONAD_WINE` (or `wine` on `PATH`) is available: each
   binary runs and its stdout and exit code are checked. `fixtures/windows/
   alloc.mo` in particular appends 3000 times, so a collector that is not
   collecting, or a stack the image did not size, cannot pass.
3. **gating** -- one fixture per refused family (a fiber, a process, a socket,
   a file stream) must fail to *compile*, with the native and the target named.
4. **isolation** -- a **native** build under the same `MONAD_WINDOWS_CC` must
   still produce an ELF, proving the mingw cc reaches only the Windows leg.

The Windows experiments are published as `windows-experiment-<date>-<rev>`
prereleases by `.github/workflows/windows-experiment.yml`. That tag deliberately
never begins with `nightly-`, so `monadup` cannot install one: `monadup` selects
releases by that prefix, and a core-only compiler must not arrive on someone's
machine by accident.

## Status

Experimental, and named so on purpose:

- **Core only.** The subset above is what works; everything in the refusal
  table is a compile error.
- **Output target, not host.** The published binary runs on x86_64-linux.
- **Paths are Windows paths.** A program reading `"."` and its own siblings
  works; a POSIX absolute path is not something `_stat64` resolves. Under wine
  the `Z:` drive maps the host filesystem, but the raw Unix spelling is not a
  Windows path.
- **`\r\n` line endings.** stdout is in text mode, so a line ends `\r\n`, which
  is correct for a Windows console and for a redirected file. It is a real
  difference from the POSIX targets' output and worth knowing before diffing
  two platforms' output.
- **One platform file, one architecture.** x86_64 only; there is no
  `i686-pc-windows-gnu` or `aarch64-pc-windows-gnullvm`.

## Adding Windows support for a refused native

The refusal list is `windows_os_only_natives` in `codegen/src/natives.mo`, and
removing a name from it is the *last* step, not the first:

1. Implement the C body in `runtime/src/platform_win32.c` (see
   [Adding Native Functions](./../AGENTS.md) in the developer guide for the
   full wiring list).
2. Prove it: add a fixture under `fixtures/windows/` and a case in
   `scripts/check-windows-target.sh`.
3. Then delete its name from `windows_os_only_natives`.

A native left in the list after its C body exists is harmless; one removed
before its C body exists is a link error, which is exactly the failure mode the
gate exists to keep out of a user's hands.
