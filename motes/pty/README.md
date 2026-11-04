# pty — a Monad-native pty/TUI test harness

`pty` spawns a compiled program under a pseudo-terminal, feeds it keys/SGR
mouse reports, reconstructs the rendered screen, and asserts on it. The
weaver-specific drivers live in `motes/weaver/src/pty/`, run by the one test
file `motes/weaver/test/pty_tests.mo`, not here; the suite is
entirely Monad (the last Python pty driver, including the sessions 18 MB RSS
scenario, was ported and deleted).

## Compilation and gating

- The pty layer is `#[extern "c"]` (`forkpty`, `execl`, `ioctl`, `kill`,
  `waitpid`, `setenv`/`unsetenv`), and `#[extern "c"]` is compiled-backend
  only. Run the tests with the self-hosted `monad test`, not `monad-rs test`.
- The pure tests (`src/tests/ansi_tests.mo`, `grid_tests.mo`) always run.
- The FFI smoke in `src/tests/spawn_spike_tests.mo` skips green unless
  `PTY_SELFTEST=1`.
- A consumer's drivers gate themselves (the weaver suite uses `WEAVER_PTY=1`);
  unset means SKIP, so ordinary `monad test` sweeps stay clean.

## Surface

| Module | Public shape |
|---|---|
| `src/spawn.mo` | `SpawnConfig` (including `cwd`), `Pty.spawn`, `Pty.send_text`, `Pty.send_chunked`, `Pty.pump`, `Pty.wait_until`, `Pty.wait_quiet`, `Pty.resize`, `Pty.child_pid`, `Pty.pid_alive`, `Pty.alive`, `Pty.reap`, `Pty.finish`, `Output` |
| `src/grid.mo` | `Grid.empty/of_string/feed_from/find/row_text/text`; cursor moves, clears, UTF-8 + wide glyphs |
| `src/ansi.mo` | `Ansi.strip` (CSI/OSC), `Ansi.tight` (also drops whitespace), `Ansi.has_color` (basic palette only) |
| `src/check.mo` | `Check.report`, `Check.skip`, `Check.enabled`, `Check.value_set`, `Check.bin_path` |

`Output` accumulates raw bytes, the `Grid`, the grid's consumed offset and an
EOF flag. `Pty.wait_until` replaces fixed sleeps: it pumps in 100 ms slices and
evaluates a predicate on the current `Output` until it fires or the deadline
expires. `Pty.wait_quiet` waits for a silence window. `Pty.resize` sets
`TIOCSWINSZ`, sends SIGWINCH, and restarts the grid at the new geometry.

`SpawnConfig.cwd` is applied by a `chdir` in the forked child (the argv/cwd
buffers are built before `forkpty`, and the child path allocates nothing), so
a test can isolate a program that reads cwd-relative config. A relative `bin`
must be made absolute by the caller: the exec happens after that `chdir`.
`Pty.send_chunked` writes in byte-sized pieces with a pump between them, for
bracketed pastes a dialog reads one byte at a time.

## Running

```bash
# the harness's own tests
monad check motes/pty
monad test motes/pty
PTY_SELFTEST=1 monad test motes/pty/src/tests/spawn_spike_tests.mo

# the weaver drivers (from the repo root; PTY_ROOT locates the fixtures)
monad build motes/weaver/src/main.mo --release -o target-monad/release/weaver
PTY_ROOT="$PWD" WEAVER_PTY=1 WEAVER_PTY_REQUIRED=1 \
  WV_BIN=target-monad/release/weaver \
  monad test motes/weaver/test/pty_tests.mo -v
```

`WV_BIN` names the binary under test; `WV_SESSION_KEEP=1` keeps a failed
test's temp root (which is also kept automatically on failure and named on
stdout).

## Affine warnings

The mote carries `[affine] mode = "warn"`: `Ptr`, `ByteBuf`, `FdStream` and
`List` are not `Copy`, and the FFI layer necessarily reuses a buffer across
`ptr`/fork/free and reads an out-parameter. Keep the warnings confined to
`sys.mo`/`spawn.mo`; `MONAD_AFFINE_REPORT=1` tracks them.
