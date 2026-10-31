# mty — a Monad-native pty/TUI test harness

`mty` spawns a compiled program under a pseudo-terminal, feeds it keys/SGR
mouse reports, reconstructs the rendered screen, and asserts on it. It is the
replacement for the Python drivers under `scripts/weaver-tui-repro/`; the
weaver-specific drivers live in `motes/weaver/test/`, not here.

## Compilation and gating

- The pty layer is `#[extern "c"]` (`forkpty`, `execl`, `ioctl`, `kill`,
  `waitpid`, `setenv`/`unsetenv`), and `#[extern "c"]` is compiled-backend
  only. Run the tests with the self-hosted `monad test`, not `monad-rs test`.
- The pure tests (`src/tests/ansi_tests.mo`, `grid_tests.mo`) always run.
- The FFI smoke in `src/tests/spawn_spike_tests.mo` skips green unless
  `MTY_SELFTEST=1`.
- A consumer's drivers gate themselves (the weaver suite uses `WEAVER_MTY=1`);
  unset means SKIP, so ordinary `monad test` sweeps stay clean.

## Surface

| Module | Public shape |
|---|---|
| `src/spawn.mo` | `SpawnConfig`, `Mty.spawn`, `Mty.send_text`, `Mty.pump`, `Mty.wait_until`, `Mty.wait_quiet`, `Mty.resize`, `Mty.alive`, `Mty.reap`, `Mty.finish`, `Output` |
| `src/grid.mo` | `Grid.empty/of_string/feed_from/find/row_text/text`; cursor moves, clears, UTF-8 + wide glyphs |
| `src/ansi.mo` | `Ansi.strip` (CSI/OSC), `Ansi.tight` (also drops whitespace) |
| `src/check.mo` | `Check.report`, `Check.skip`, `Check.enabled`, `Check.value_set`, `Check.bin_path` |

`Output` accumulates raw bytes, the `Grid`, the grid's consumed offset and an
EOF flag. `Mty.wait_until` replaces fixed sleeps: it pumps in 100 ms slices and
evaluates a predicate on the current `Output` until it fires or the deadline
expires. `Mty.wait_quiet` waits for a silence window. `Mty.resize` sets
`TIOCSWINSZ`, sends SIGWINCH, and restarts the grid at the new geometry.

## Running

```bash
# the harness's own tests
monad check motes/mty
monad test motes/mty
MTY_SELFTEST=1 monad test motes/mty/src/tests/spawn_spike_tests.mo

# the weaver drivers (from the repo root; MTY_ROOT locates the fixtures)
monad build motes/weaver/src/main.mo --release -o target-monad/release/weaver
MTY_ROOT="$PWD" WEAVER_MTY=1 WEAVER_MTY_REQUIRED=1 \
  WV_BIN=target-monad/release/weaver \
  monad test motes/weaver/test --jobs 1 -v
```

`WV_BIN` names the binary under test; `WV_SESSION_KEEP=1` keeps a failed
test's temp root (which is also kept automatically on failure and named on
stdout).

## Affine warnings

The mote carries `[affine] mode = "warn"`: `Ptr`, `ByteBuf`, `FdStream` and
`List` are not `Copy`, and the FFI layer necessarily reuses a buffer across
`ptr`/fork/free and reads an out-parameter. Keep the warnings confined to
`sys.mo`/`spawn.mo`; `MONAD_AFFINE_REPORT=1` tracks them.
