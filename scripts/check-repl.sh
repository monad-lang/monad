#!/usr/bin/env bash
# `monad repl`: pipe a scripted session into the self-hosted REPL and assert
# the printed results. Prompts go to stderr; results and diagnostics to
# stdout (the CLI's convention), so the assertions read stdout.
#
# Needs a SELF-HOSTED compiler built from this tree:
#   MONAD_BIN=target-monad/release/monad scripts/check-repl.sh
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
monad="${MONAD_BIN:-${1:-$root/target-monad/release/monad}}"
if [ ! -x "$monad" ]; then
  echo "error: no self-hosted compiler at $monad (set MONAD_BIN)" >&2
  exit 1
fi

work="$(mktemp -d "${TMPDIR:-/tmp}/monad_repl_$$.XXXXXX")"
trap 'rm -rf "$work"' EXIT

fail() { echo "FAIL: $*" >&2; exit 1; }

run_session() {
  local name="$1" script="$2"
  local out="$work/$name.out" err="$work/$name.err" status
  set +e
  printf '%s' "$script" | (cd "$root" && "$monad" repl) >"$out" 2>"$err"
  status=$?
  set -e
  [ "$status" -eq 0 ] || { cat "$err" >&2; fail "$name: repl exited $status"; }
  cat "$out"
}

# Expressions, a definition then a call, :type, and a rejected definition
# that leaves the earlier ones intact.
out="$(run_session basic '2 + 3
def twice (n : I64) : I64 := n + n
twice 21
:type twice
def bad : I64 := nope
twice 5
:quit
')"
printf '%s' "$out" | grep -Fq '5 : I64' || fail "basic: no 5 : I64"
printf '%s' "$out" | grep -Fq '42 : I64' || fail "basic: no 42 : I64"
printf '%s' "$out" | grep -Fq 'twice : (I64 -> I64)' || fail "basic: :type wrong"
printf '%s' "$out" | grep -Fq '10 : I64' || fail "basic: session lost after a rejected def"

# `use` is an ordinary declaration and resolves through the standard loader.
out="$(run_session use 'use init::foldable {}
1 + 2
:quit
')"
printf '%s' "$out" | grep -Fq '3 : I64' || fail "use: no 3 : I64"

# A def body on the next line continues on the ".. " prompt.
out="$(run_session multiline 'def inc (n : I64) : I64 :=
    n + 1
inc 41
:quit
')"
printf '%s' "$out" | grep -Fq '42 : I64' || fail "multiline: no 42 : I64"

# EOF (no :quit) is a clean exit, not an error.
out="$(run_session eof '2 + 3
')"
printf '%s' "$out" | grep -Fq '5 : I64' || fail "eof: no 5 : I64"

echo "ok: monad repl session checks passed"
