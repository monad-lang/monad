#!/usr/bin/env bash
# usage: check-wasm-target.sh [path/to/monad]
#
# The Phase 0-2 wasm gate:
#   * wasi profile: fib.mo builds to .wasm, wasmtime runs it, and its stdout
#     and exit code match the native build;
#   * web profile: hello.mo builds to a freestanding .wasm, and the Node
#     loader test instantiates it with the four "monad" imports and checks
#     stdout/exit;
#   * native gating: a reachable OS-only native is a clean compile error on
#     both wasm profiles, and dead std code does not block a pure program.
#
# Requires WASI_SDK_PATH (the dev shell sets it), wasmtime and node.

set -euo pipefail

MONAD="${1:-monad}"
: "${WASI_SDK_PATH:?WASI_SDK_PATH must name a wasi-sdk installation}"

for tool in wasmtime node; do
    command -v "$tool" >/dev/null 2>&1 || {
        echo "error: $tool is required (the dev shell provides it)" >&2
        exit 1
    }
done

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

tmp=$(mktemp -d "${TMPDIR:-/tmp}/monad-wasm-check.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

fail() {
    echo "FAIL: $*" >&2
    exit 1
}

echo "== wasi: fib (build, run, differential) =="
"$MONAD" build --target wasm32-unknown-wasip1 fixtures/wasm/fib.mo \
    -o "$tmp/fib.wasm" --no-cache
wasmtime "$tmp/fib.wasm" >"$tmp/fib.wasm.out" 2>"$tmp/fib.wasm.err" \
    || fail "wasmtime failed: $(cat "$tmp/fib.wasm.err")"

"$MONAD" build fixtures/wasm/fib.mo -o "$tmp/fib.native" --no-cache
"$tmp/fib.native" >"$tmp/fib.native.out" 2>"$tmp/fib.native.err"

diff -u "$tmp/fib.native.out" "$tmp/fib.wasm.out" \
    || fail "wasm and native stdout differ"
grep -qx '832040' "$tmp/fib.wasm.out" \
    || fail "unexpected wasm stdout: $(cat "$tmp/fib.wasm.out")"

echo "== wasi/web: 8-byte constructor fields and closure env slots =="
# 5000000000 does not fit in 32 bits: `some n` reads a constructor field,
# and `add n` captures the same value in a closure env slot.
"$MONAD" build --target wasm32-unknown-wasip1 fixtures/wasm/wide_values.mo \
    -o "$tmp/wide.wasm" --no-cache
wasmtime "$tmp/wide.wasm" >"$tmp/wide.wasm.out" \
    || fail "wasmtime failed on wide_values"
grep -qx '5000000123' "$tmp/wide.wasm.out" \
    || fail "wasm truncated a wide value: $(cat "$tmp/wide.wasm.out")"

"$MONAD" build --target wasm32-unknown-unknown fixtures/wasm/wide_values.mo \
    -o "$tmp/wide-web.wasm" --no-cache
node wasm/web/smoke.mjs "$tmp/wide-web.wasm" 5000000123

echo "== web: hello (freestanding build + Node loader) =="
"$MONAD" build --target wasm32-unknown-unknown fixtures/wasm/hello.mo \
    -o "$tmp/hello.wasm" --no-cache
node wasm/web/smoke.mjs "$tmp/hello.wasm"

echo "== output suffix (build without -o) =="
# The same rule must name the cache destination and the linked artifact.
"$MONAD" build --target wasm32-unknown-unknown fixtures/wasm/hello.mo \
    "$tmp/noext" --no-cache
[ -f "$tmp/noext.wasm" ] || fail "missing $tmp/noext.wasm"
[ ! -e "$tmp/noext.wasm.wasm" ] || fail "the .wasm suffix was applied twice"
node wasm/web/smoke.mjs "$tmp/noext.wasm"

echo "== gating: OS-only natives fail with a target diagnostic =="
if "$MONAD" build --target wasm32-unknown-unknown fixtures/wasm/web_file_io.mo \
    -o "$tmp/gate-web.wasm" --no-cache >"$tmp/gate-web.log" 2>&1; then
    fail "web build accepted get_env"
fi
grep -q 'get_env' "$tmp/gate-web.log" \
    || fail "web gate did not name get_env: $(cat "$tmp/gate-web.log")"
grep -q 'not available on target' "$tmp/gate-web.log" \
    || fail "web gate did not explain the target: $(cat "$tmp/gate-web.log")"

if "$MONAD" build --target wasm32-unknown-wasip1 fixtures/wasm/wasi_fiber.mo \
    -o "$tmp/gate-wasi.wasm" --no-cache >"$tmp/gate-wasi.log" 2>&1; then
    fail "wasi build accepted fork_io"
fi
grep -q 'fork_io' "$tmp/gate-wasi.log" \
    || fail "wasi gate did not name fork_io: $(cat "$tmp/gate-wasi.log")"
grep -q 'not available on target' "$tmp/gate-wasi.log" \
    || fail "wasi gate did not explain the target: $(cat "$tmp/gate-wasi.log")"

echo "ok: wasm target checks passed"
