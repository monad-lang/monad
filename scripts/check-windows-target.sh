#!/usr/bin/env bash
# usage: check-windows-target.sh [path/to/monad]
#
# The Windows target gate. Monad is the experimental OUTPUT target here: this
# cross-compiles a Windows `.exe` from a Linux/macOS host. Compiling ON Windows
# is deliberately out of scope (docs/src/windows.md), so nothing below runs a
# Windows-hosted compiler.
#
#   * structural: four fixtures build to PE32+ x86-64 images with no `libgc`
#     DLL import -- the two properties a wrong link line breaks, both readable
#     without an emulator;
#   * behavioural: the same binaries run, and their stdout/exit codes are
#     asserted, through $MONAD_WINE when it is set;
#   * gating: every concurrency/process/socket/file-stream native is a clean
#     COMPILE error naming the native and the target, not a link error;
#   * the suffix rule: no `-o` gives `<name>.exe`, and `.exe` is applied once.
#
# Requires a mingw-w64 cross cc reachable as
# `x86_64-w64-mingw32-gcc` (or named by $MONAD_WINDOWS_CC), plus a mingw
# build of Boehm GC. `nix develop` provides both through
# `packages.monad-windows`; this script takes a compiler path so CI can point
# it at a freshly built one.

set -euo pipefail

MONAD="${1:-monad}"

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

# The cross cc has to be found by the same variable the compiler reads, so the
# gate fails for the same reason a user's build would.
windows_cc="${MONAD_WINDOWS_CC:-x86_64-w64-mingw32-gcc}"
if ! command -v "$windows_cc" >/dev/null 2>&1; then
    echo "error: no mingw-w64 cross compiler: \`$windows_cc\` is not executable." >&2
    echo "  Debian/Ubuntu: apt install gcc-mingw-w64-x86-64" >&2
    echo "  nix:           nix build .#monad-windows, or the dev shell's" >&2
    echo "                 pkgsCross.mingwW64.stdenv.cc (which also needs" >&2
    echo "                 MONAD_WINDOWS_CC to carry gc's -isystem/-L; see" >&2
    echo "                 nix/monad.nix's windowsShim)" >&2
    exit 1
fi

tmp=$(mktemp -d "${TMPDIR:-/tmp}/monad-windows-check.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

fail() {
    echo "FAIL: $*" >&2
    exit 1
}

# `objdump`/`file` read the structural claims. The cross-prefixed objdump is
# preferred because it is guaranteed to understand PE, but plain `objdump`
# does too on any binutils built with PE support -- which the host's is when a
# mingw cc is installed at all. Either way a missing tool is a hard error
# rather than a silently skipped check.
objdump_bin="$(command -v "${windows_target_prefix:-x86_64-w64-mingw32-}objdump" \
    || command -v objdump || true)"
file_bin="$(command -v file || true)"
[ -n "$objdump_bin" ] || fail "no objdump found (needed to read the PE import table)"

TARGET=x86_64-pc-windows-gnu

build() {
    # Fails loudly rather than returning, so every caller can assume success.
    "$MONAD" build "$1" --target "$TARGET" -o "$2" --no-cache \
        >"$tmp/build.log" 2>&1 || {
        cat "$tmp/build.log" >&2
        fail "build failed: $1"
    }
}

# The structural claim every fixture must satisfy: a PE32+ x86-64 image that
# does not import the collector. `-static` is what makes the second true, and
# the failure it prevents is a load-time abort on a machine with no
# libgc-1.dll -- invisible to an exit-status check, because the process never
# starts.
assert_pe() {
    local exe="$1"
    local kind imports
    [ -f "$exe" ] || fail "no such output: $exe"
    # Both readings are captured FIRST and grepped second, deliberately: this
    # script runs under `set -o pipefail`, and `tool | grep -q` makes grep exit
    # as soon as it matches, which kills `tool` with SIGPIPE and leaves the
    # PIPELINE's status non-zero even though grep succeeded. Measured on this
    # file: the msvcrt/KERNEL32 assertion below failed on an image that plainly
    # had both imports. Capturing removes the pipe, so there is nothing to
    # signal.
    if [ -n "$file_bin" ]; then
        kind=$("$file_bin" "$exe")
        case "$kind" in
            *"PE32+ executable"*) ;;
            *) fail "$exe is not a PE32+ image: $kind" ;;
        esac
    fi
    imports=$("$objdump_bin" -p "$exe") \
        || fail "$objdump_bin could not read $exe"
    case "$imports" in
        *"DLL Name: libgc"*)
            fail "$exe imports the gc DLL (a -static link of -lgc should prevent this)" ;;
    esac
    case "$imports" in
        *"DLL Name: msvcrt"*|*"DLL Name: KERNEL32"*) ;;
        *) fail "$exe imports neither msvcrt nor KERNEL32 -- not a Windows console image?" ;;
    esac
}

run() {
    # $1 = exe, rest = arguments. Echoes stdout, with the CRT's `\r\n` folded
    # to `\n`. That fold is not cosmetic: mingw's stdio is in TEXT mode, so
    # every line the program prints ends `\r\n`, and that is the CORRECT
    # behaviour on Windows (a console and a redirected file both want it). The
    # gate compares against POSIX-shaped expected text, so the translation
    # belongs here, on the reading side.
    local exe="$1"
    local status=0
    shift
    # Written as a capture-then-fold rather than `exe | tr -d '\r'` because
    # this file runs under `set -o pipefail`: the pipeline's status would be
    # tr's, and `$?` after it has already been consumed by the assignment.
    # Capturing first keeps the exit status of the PROGRAM the thing checked.
    captured=$("$MONAD_WINE" "$exe" "$@" 2>"$tmp/run.err") || status=$?
    if [ "$status" -ne 0 ]; then
        sed 's/^/  stderr: /' "$tmp/run.err" >&2
        return 1
    fi
    printf '%s\n' "$captured" | tr -d '\r'
}

wine_bin="${MONAD_WINE:-}"
if [ -z "$wine_bin" ]; then
    command -v wine >/dev/null 2>&1 && wine_bin=wine
fi

echo "== structural: four fixtures build to PE32+ with no gc DLL import =="
for name in hello alloc clock sysfloor; do
    build "fixtures/windows/$name.mo" "$tmp/$name"
    assert_pe "$tmp/$name.exe"
    echo "  ok: $name.exe"
done

echo "== output suffix (build without -o) =="
# The suffix rule must name the linked artifact once, whichever way the output
# is spelled.
"$MONAD" build fixtures/windows/hello.mo --target "$TARGET" "$tmp/noext" --no-cache \
    >"$tmp/noext.log" 2>&1 || fail "build without -o failed: $(cat "$tmp/noext.log")"
[ -f "$tmp/noext.exe" ] || fail "missing $tmp/noext.exe"
[ ! -e "$tmp/noext.exe.exe" ] || fail "the .exe suffix was applied twice"
assert_pe "$tmp/noext.exe"
# ...and an explicit `.exe` is not doubled either.
"$MONAD" build fixtures/windows/hello.mo --target "$TARGET" "$tmp/explicit.exe" --no-cache \
    >"$tmp/explicit.log" 2>&1 || fail "build with an explicit .exe failed"
assert_pe "$tmp/explicit.exe"

echo "== gating: OS-only natives are a compile error naming the target =="
# A fiber, a process, a socket and a file stream -- one from each refused
# family, so a single list entry silently deleted cannot pass this by
# accident.
gate_case() {
    local fixture="$1" native="$2" label="$3"
    if "$MONAD" build "$fixture" --target "$TARGET" -o "$tmp/gate" --no-cache \
        >"$tmp/gate.log" 2>&1; then
        fail "$label: the Windows target accepted $native"
    fi
    grep -q "$native" "$tmp/gate.log" \
        || fail "$label: the gate did not name $native: $(cat "$tmp/gate.log")"
    grep -q 'not available on target' "$tmp/gate.log" \
        || fail "$label: the gate did not explain the target: $(cat "$tmp/gate.log")"
    grep -q 'windows' "$tmp/gate.log" \
        || fail "$label: the gate did not name the target kind: $(cat "$tmp/gate.log")"
    echo "  ok: $native refused ($label)"
}

mkdir -p "$tmp/gate"
cat >"$tmp/gate/fiber.mo" <<'EOF'
#![mote { name := "fiber", deps := [init, std] }]

#[native fork_io]
priv def fork_io_raw (f : Unit -> Unit) : RawIO I64

def main (args : List String) : IO Unit :=
    IO.mk (fork_io_raw (fn (_ : Unit) => unit))
EOF
gate_case "$tmp/gate/fiber.mo" 'fork_io' 'threads'

cat >"$tmp/gate/proc.mo" <<'EOF'
#![mote { name := "proc", deps := [init, std] }]

use std::process {exec_cmd}
open IO {println}

def main (args : List String) : IO Unit := do {
    let rc <- exec_cmd "cmd" ["/c", "echo hi"];
    println (I64.to_string rc)
}
EOF
gate_case "$tmp/gate/proc.mo" 'proc_spawn' 'processes'

cat >"$tmp/gate/socket.mo" <<'EOF'
#![mote { name := "socket", deps := [init, std] }]

#[native tcp_listen_on]
priv def tcp_listen_on_raw (port : I64) : RawIO I64

def main (args : List String) : IO Unit :=
    IO.mk (tcp_listen_on_raw 8080)
EOF
gate_case "$tmp/gate/socket.mo" 'tcp_listen_on' 'sockets'

cat >"$tmp/gate/filestream.mo" <<'EOF'
#![mote { name := "filestream", deps := [init, std] }]

#[native stream_open]
priv def stream_open_raw (path : String) (mode : I64) : RawIO I64

def main (args : List String) : IO Unit :=
    IO.mk (stream_open_raw "x" 0)
EOF
gate_case "$tmp/gate/filestream.mo" 'stream_open' 'file streams'

echo "== native builds still work (the Windows leg must not disturb them) =="
# `MONAD_WINDOWS_CC` points at a mingw cc. If that ever leaked into the NATIVE
# path -- it must not; only `TargetPlan.windows_cc` reads it -- this build
# would fail or produce a PE.
"$MONAD" build fixtures/windows/hello.mo -o "$tmp/hello-native" --no-cache \
    >"$tmp/native.log" 2>&1 || fail "a native build broke under MONAD_WINDOWS_CC: $(cat "$tmp/native.log")"
[ -x "$tmp/hello-native" ] || fail "the native build produced no executable"
if [ -n "$file_bin" ]; then
    native_kind=$("$file_bin" "$tmp/hello-native")
    case "$native_kind" in
        *PE32+*) fail "a NATIVE build produced a PE image (MONAD_WINDOWS_CC leaked): $native_kind" ;;
    esac
fi
echo "  ok: native build unaffected"

if [ -z "$wine_bin" ]; then
    echo "== behavioural: SKIPPED (set MONAD_WINE, or put wine on PATH) =="
    echo "ok: windows target structural checks passed"
    exit 0
fi

echo "== behavioural: the binaries run (MONAD_WINE=$wine_bin) =="

# hello: `main` gets only its own extra arguments, nothing else.
out=$(run "$tmp/hello.exe" from-wine) || fail "hello.exe did not run"
[ "$out" = "from-wine" ] || fail "hello.exe stdout: [$out]"
out=$(run "$tmp/hello.exe") || fail "hello.exe did not run without an argument"
[ "$out" = "hello from windows" ] || fail "hello.exe default stdout: [$out]"

# alloc: the collector allocates AND the recursion finishes. 3000 appends of
# 20 bytes; a heap that is not collected, or a stack the image did not size,
# leaves the marker missing or the output short.
run "$tmp/alloc.exe" >"$tmp/alloc.out" || fail "alloc.exe did not run"
grep -q '^allocprobe-ok' "$tmp/alloc.out" || fail "alloc.exe marker missing"
[ "$(wc -c <"$tmp/alloc.out")" -gt 60000 ] \
    || fail "alloc.exe produced $(wc -c <"$tmp/alloc.out") bytes, expected > 60000"

# clock: a monotonic reading advances across a real sleep, and the wall clock
# is after 2020. Both are `QueryPerformanceCounter` and
# `GetSystemTimeAsFileTime`; mingw has neither clock_gettime nor timespec_get.
out=$(run "$tmp/clock.exe") || fail "clock.exe did not run"
[ "$out" = "true true" ] || fail "clock.exe stdout: [$out]"

# sysfloor: the Win32 sys floor agrees with the compiler's own picture of the
# filesystem. The gate passes the directory to inspect and sets the variable
# the fixture looks for.
# `sysfloor` runs with the prepared directory as its CWD, and reads only
# relative paths: under wine a Unix absolute path is not one the Windows API
# can open, so handing it `$tmp/probe-dir` would test wine's path translation
# rather than this runtime's `_stat64`/`FindFirstFile`. See the fixture's own
# comment.
mkdir -p "$tmp/probe-dir"
printf 'x' >"$tmp/probe-dir/present.txt"
# Exported rather than written as `MONAD_WINDOWS_GATE=1 run ...`: an assignment
# on a FUNCTION call is scoped to the call as a shell variable, not applied to
# the command's environment, so the value would never reach the child.
MONAD_WINDOWS_GATE=1
export MONAD_WINDOWS_GATE
out=$(cd "$tmp/probe-dir" && run "$tmp/sysfloor.exe") \
    || fail "sysfloor.exe did not run"
unset MONAD_WINDOWS_GATE
expected=$(printf 'env: true\ndir: true\nfound: true\nabsent: true\nsize: true\npid: true')
[ "$out" = "$expected" ] || fail "sysfloor.exe stdout:
[$out]
expected:
[$expected]"

echo "ok: windows target checks passed"
