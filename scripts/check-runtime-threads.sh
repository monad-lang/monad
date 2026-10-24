#!/usr/bin/env bash
# usage: check-runtime-threads.sh [runs]
#
# Thread-safety gate for the C runtime (plans/implementations/
# async-runtime-thread-safety.md): builds runtime/tests/thread_stress.c
# against the real runtime twice and runs it --
#   * plain, `runs` times (default 5): every line read is checked, so a
#     race shows up as a failure count even without a sanitizer;
#   * under ThreadSanitizer once, which must report no warnings.
#
# Needs clang and Boehm GC via pkg-config (the dev shell provides both).
# Runs no Monad compiler.

set -euo pipefail

runs="${1:-5}"
repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
src="$repo_root/runtime/src"
harness="$repo_root/runtime/tests/thread_stress.c"

tmp=$(mktemp -d "${TMPDIR:-/tmp}/monad-runtime-threads.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

read -r -a gc_cflags <<<"$(pkg-config --cflags bdw-gc)"
read -r -a gc_libs <<<"$(pkg-config --libs bdw-gc)"

# build <out> [extra clang flags...]
build() {
    local out=$1
    shift
    clang -O1 -g -pthread -w "$@" "${gc_cflags[@]}" \
        -Dmain=monad_runtime_main -c "$src/runtime.c" -o "$out.runtime.o"
    clang -O1 -g -pthread -Wall -Werror "$@" "${gc_cflags[@]}" \
        -c "$harness" -o "$out.harness.o"
    clang -pthread "$@" "$out.runtime.o" "$out.harness.o" -o "$out" \
        "${gc_libs[@]}"
}

echo "== plain build, $runs run(s) =="
build "$tmp/plain"
for ((i = 1; i <= runs; i++)); do
    "$tmp/plain"
done

echo "== ThreadSanitizer =="
build "$tmp/tsan" -fsanitize=thread
if ! TSAN_OPTIONS="halt_on_error=0 exitcode=0" "$tmp/tsan" >"$tmp/tsan.log" 2>&1; then
    cat "$tmp/tsan.log" >&2
    echo "FAIL: thread_stress failed under ThreadSanitizer" >&2
    exit 1
fi
warnings=$(grep -c 'WARNING: ThreadSanitizer' "$tmp/tsan.log" || true)
if [ "$warnings" -ne 0 ]; then
    cat "$tmp/tsan.log" >&2
    echo "FAIL: ThreadSanitizer reported $warnings warning(s)" >&2
    exit 1
fi
grep 'thread_stress:' "$tmp/tsan.log"
echo "OK: runtime thread stress clean"
