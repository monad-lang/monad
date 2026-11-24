#!/usr/bin/env bash
# usage: windows-release.sh [out-dir]
#
# Assemble the EXPERIMENTAL Windows proof artifact set: the compiler that emits
# Windows PE images (built by `nix build .#monad-windows`), and a `.exe` built
# with it as evidence that it works. Writes to <out-dir> (default: dist).
#
# This is deliberately NOT `scripts/nightly-release.sh`. A nightly publishes a
# compiler that RUNS on the platform it names; this publishes a compiler that
# runs on x86_64-linux and EMITS Windows binaries. The two are different
# products with different trust stories, which is why the workflow that calls
# this tags its release `windows-experiment-<date>-<rev>` and never
# `nightly-`: `scripts/monadup` selects installable releases with
# `startswith("nightly-")`, so an experiment tag can never be picked up by
# `monadup default` on someone's machine.
#
# Outputs:
#   monad-windows-<date>.tar.gz   the compiler (x86_64-linux; emits .exe)
#   hello-windows-<date>.exe      a Monad program compiled to Windows
#   windows-<date>.sha256         checksums of the above
#   windows-commit.txt            the revision they were built from
#
# Requirements: nix with flakes, a wine binary in $MONAD_WINE (or on PATH) if
# the .exe is to be RUN here. Absent wine, the .exe is still built and its
# structure checked -- which is most of the claim -- and the script says so.

set -euo pipefail

out_dir="${1:-dist}"
mkdir -p "$out_dir"
out_dir=$(cd "$out_dir" && pwd)

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

date_tag=$(date -u +%Y-%m-%d)
rev=$(git rev-parse --short HEAD 2>/dev/null || echo unknown)

fail() {
    echo "FAIL: $*" >&2
    exit 1
}

echo "== building the Windows-capable compiler (.#monad-windows) =="
# The derivation is the same native compiler as `.#monad` plus one wrapper
# variable; its own `checkPhase` already proves it emits a PE32+ image with no
# gc DLL import, so a failure here is that failure, reported by nix.
monad_store=$(nix build --no-link --print-out-paths --accept-flake-config .#monad-windows) \
    || fail "nix build .#monad-windows failed"
monad_bin="$monad_store/bin/monad"
[ -x "$monad_bin" ] || fail "no compiler at $monad_bin"
echo "   $monad_bin"

echo "== verifying the compiler advertises the target =="
targets=$("$monad_bin" print-targets) || fail "print-targets failed"
case "$targets" in
    *x86_64-pc-windows-gnu*) ;;
    *) fail "the compiler does not list x86_64-pc-windows-gnu:
$targets" ;;
esac

echo "== building a Monad program for Windows =="
# `fixtures/windows/hello.mo` is the same program the gate builds. The
# compiler's wrapper sets MONAD_WINDOWS_CC, so no environment is needed here.
exe_src="$out_dir/hello-windows-$date_tag"
"$monad_bin" build fixtures/windows/hello.mo \
    --target x86_64-pc-windows-gnu -o "$exe_src" --no-cache \
    || fail "building fixtures/windows/hello.mo for Windows failed"
exe="$exe_src.exe"
[ -f "$exe" ] || fail "no .exe produced at $exe"

echo "== checking the image structure =="
objdump_bin=$(command -v x86_64-w64-mingw32-objdump || command -v objdump || true)
[ -n "$objdump_bin" ] || fail "no objdump (mingw binutils or binutils)"
imports=$("$objdump_bin" -p "$exe") || fail "objdump could not read $exe"
case "$imports" in
    *"DLL Name: libgc"*)
        fail "the .exe imports the gc DLL: it would not start on a bare Windows" ;;
esac
case "$imports" in
    *"DLL Name: KERNEL32"*) ;;
    *) fail "the .exe does not import KERNEL32 -- not a Windows console image?" ;;
esac
if command -v file >/dev/null 2>&1; then
    kind=$(file "$exe")
    case "$kind" in
        *"PE32+ executable"*) ;;
        *) fail "not a PE32+ image: $kind" ;;
    esac
fi
dlls=$(printf '%s\n' "$imports" | sed -n 's/.*DLL Name: //p' | tr '\n' ' ')
echo "   imports: $dlls"

wine_bin="${MONAD_WINE:-}"
if [ -z "$wine_bin" ]; then
    command -v wine >/dev/null 2>&1 && wine_bin=wine
fi

if [ -n "$wine_bin" ]; then
    echo "== running it (MONAD_WINE=$wine_bin) =="
    # The CRT is in text mode, so the program's output ends `\r\n`; the fold is
    # on the reading side, exactly as scripts/check-windows-target.sh does it.
    captured=$("$wine_bin" "$exe" windows-release 2>/dev/null) || fail "the .exe did not run"
    out=$(printf '%s\n' "$captured" | tr -d '\r')
    [ "$out" = "windows-release" ] || fail "the .exe printed [$out]"
    echo "   ran, and printed its argument"
else
    echo "== NOT running it: no wine (set MONAD_WINE) =="
    echo "   the artifact is structure-checked only"
fi

echo "== packaging the compiler =="
# `dist/` holds artifacts; `dist/stage/` holds what is inside the tarball. Two
# directories rather than one because `sha256sum` below reads files by name
# from `dist/`, and a staged copy that shared the name would be ambiguous.
compiler_tar="$out_dir/monad-windows-$date_tag.tar.gz"
stage="$out_dir/stage"
rm -rf "$stage"
mkdir -p "$stage/monad-windows-$date_tag"
# The packaged binary is the WRAPPER, which is what carries MONAD_WINDOWS_CC.
cp "$monad_store/bin/monad" "$stage/monad-windows-$date_tag/monad"
cat >"$stage/monad-windows-$date_tag/README" <<'README'
monad, built to emit Windows x86_64 PE images (experimental).

This binary RUNS on x86_64-linux. It is not a Windows-hosted compiler:
compiling ON Windows is out of scope. See docs/src/windows.md.

It carries MONAD_WINDOWS_CC, pointing at the mingw shim it was built with --
a /nix/store path that exists only where that store does. On another machine
set MONAD_WINDOWS_CC to a mingw-w64 gcc that can find Boehm GC and
mcfgthread, e.g.

  MONAD_WINDOWS_CC='x86_64-w64-mingw32-gcc -isystem /gc/include -L/gc/lib' \
    ./monad build prog.mo --target x86_64-pc-windows-gnu -o prog

Core only: allocator, stdio on fds 0/1/2, the clock, files and the sys floor.
Threads, processes, sockets and file streams are named compile errors on this
target.
README
tar -czf "$compiler_tar" -C "$stage" "monad-windows-$date_tag"
rm -rf "$stage"

echo "== writing checksums and the revision =="
printf '%s\n' "$rev" >"$out_dir/windows-commit.txt"
(
    cd "$out_dir"
    sha256sum "monad-windows-$date_tag.tar.gz" "hello-windows-$date_tag.exe" \
        >"windows-$date_tag.sha256"
)

echo "ok: windows experiment artifacts in $out_dir"
ls -l "$out_dir"/monad-windows-*.tar.gz "$out_dir"/hello-windows-*.exe \
    "$out_dir"/windows-*
