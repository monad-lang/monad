#!/usr/bin/env bash
# Fixture tests for scripts/bump-nightly-pin.sh. No network and no real
# release: a `file://` releases API and a `file://` checksum tree drive every
# branch, so the rewrite and its failure paths are tested rather than assumed.
#
#   scripts/check-nightly-pin.sh
#
# The pin copy under test is the repo's own nix/nightly.nix, so the parser and
# the four rewritten lines are exercised against the real file's shape. Every
# platform the file names gets a checksum fixture; a platform added there
# without one fails these tests loudly, not silently.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
bump="$root/scripts/bump-nightly-pin.sh"
pin_source="$root/nix/nightly.nix"
new_tag="nightly-2026-12-01-aaaaaaaa"

work="$(mktemp -d "${TMPDIR:-/tmp}/monad-nightly-pin.XXXXXX")"
trap 'rm -rf "$work"' EXIT

passed=0
failed=0
fail() { echo "FAIL: $*" >&2; failed=$((failed + 1)); }
pass() { passed=$((passed + 1)); }

old_tag="$(sed -n 's/^ *tag = "\([^"]*\)";$/\1/p' "$pin_source" | head -n 1)"
[ -n "$old_tag" ] || { echo "no pin tag in $pin_source" >&2; exit 1; }
if [ "$(sed -n 's/^ *tag = "\([^"]*\)";$/\1/p' "$pin_source" | sort -u | wc -l)" -ne 1 ]; then
  echo "the pin entries in $pin_source disagree on a tag" >&2
  exit 1
fi

platforms="$(awk '/^[[:space:]]+[A-Za-z0-9_.-]+ = \{$/ { p=$1 } /^[[:space:]]+tag = "/ { print p }' "$pin_source")"
[ -n "$platforms" ] || { echo "no pin entries in $pin_source" >&2; exit 1; }

hex_for() {
  python3 -I -c 'import hashlib, sys; print(hashlib.sha256(sys.argv[1].encode()).hexdigest())' "$1"
}

sri_for() {
  python3 -I -c 'import base64, sys; print("sha256-" + base64.b64encode(bytes.fromhex(sys.argv[1])).decode())' "$1"
}

# A fresh pin copy plus a releases API that names `tag` after a non-nightly
# release (the API is newest-first, and the script must skip the non-nightly
# entries rather than take the first release).
reset() {
  local tag="$1"
  cp "$pin_source" "$work/nightly.nix"
  cp "$pin_source" "$work/before.nix"
  printf '[{"tag_name": "v0.1.0"}, {"tag_name": "%s"}]\n' "$tag" > "$work/releases.json"
  mkdir -p "$work/download/$tag"
  for plat in $platforms; do
    printf '%s  monad-nightly-%s\n' "$(hex_for "$plat")" "$plat" \
      > "$work/download/$tag/monad-nightly-$plat.sha256"
  done
}

run_bump() {
  MONAD_NIGHTLY_PIN_FILE="$work/nightly.nix" \
    MONAD_NIGHTLY_API_URL="file://$work/releases.json" \
    MONAD_NIGHTLY_DOWNLOAD_BASE="file://$work/download" \
    "$bump" "$@"
}

unchanged() {
  cmp -s "$work/nightly.nix" "$work/before.nix" || { fail "$1: the pin file changed"; return 1; }
  pass
  return 0
}

# ─── already at the newest: a no-op, and --check agrees ─────────────────────

reset "$old_tag"
if out="$(run_bump 2>&1)"; then
  case "$out" in
    *"already at $old_tag"*) pass ;;
    *) fail "no-op run did not report 'already at $old_tag': $out" ;;
  esac
else
  fail "no-op run exited non-zero: $out"
fi
unchanged "no-op run" || true

reset "$old_tag"
if run_bump --check >/dev/null 2>&1; then
  pass
else
  fail "--check exited non-zero when the pin was current"
fi
unchanged "--check when current" || true

# ─── stale: --check exits 1 and writes nothing ──────────────────────────────

reset "$new_tag"
if out="$(run_bump --check 2>&1)"; then
  fail "--check exited zero on a stale pin: $out"
else
  case "$out" in
    *"behind $new_tag"*) pass ;;
    *) fail "--check did not name the stale tag: $out" ;;
  esac
fi
unchanged "--check on a stale pin" || true

# ─── --dry-run reports the bump and writes nothing ──────────────────────────

reset "$new_tag"
if out="$(run_bump --dry-run 2>&1)"; then
  case "$out" in
    *"$new_tag"*) pass ;;
    *) fail "--dry-run did not name the new tag: $out" ;;
  esac
else
  fail "--dry-run exited non-zero: $out"
fi
unchanged "--dry-run" || true

# ─── a real bump rewrites all four lines of every pin entry ─────────────────

reset "$new_tag"
if out="$(run_bump 2>&1)"; then
  pass
else
  fail "bump exited non-zero: $out"
fi
grep -qF '# THE PIN, and why' "$work/nightly.nix" || fail "the bump lost a header comment"
for plat in $platforms; do
  hex="$(hex_for "$plat")"
  sri="$(sri_for "$hex")"
  url="file://$work/download/$new_tag/monad-nightly-$plat"
  grep -qF "url = \"$url\";" "$work/nightly.nix" || fail "$plat: url not rewritten"
  grep -qF "sha256 = \"$sri\";" "$work/nightly.nix" || fail "$plat: sha256 not rewritten"
  grep -qF "# curl -fsSL \"<url>.sha256\" -> $hex" "$work/nightly.nix" || fail "$plat: checksum comment not rewritten"
done
[ "$(grep -cF "tag = \"$new_tag\";" "$work/nightly.nix")" -eq "$(printf '%s\n' "$platforms" | wc -l)" ] \
  || fail "not every tag line was rewritten"
[ "$(grep -cF "sha256 = " "$work/nightly.nix")" -eq "$(printf '%s\n' "$platforms" | wc -l)" ] \
  || fail "the bump changed the number of sha256 lines"

# A second run against the same tag is now a no-op.
cp "$work/nightly.nix" "$work/before.nix"
if out="$(run_bump 2>&1)"; then
  case "$out" in
    *"already at $new_tag"*) pass ;;
    *) fail "the bump is not idempotent: $out" ;;
  esac
else
  fail "the second bump exited non-zero: $out"
fi
unchanged "second bump" || true

# ─── a missing checksum fails before the pin is touched ─────────────────────

reset "$new_tag"
missing="$(printf '%s\n' "$platforms" | head -n 1)"
rm -f "$work/download/$new_tag/monad-nightly-$missing.sha256"
if out="$(run_bump 2>&1)"; then
  fail "a missing .sha256 was accepted: $out"
else
  case "$out" in
    *"no checksum at"*) pass ;;
    *) fail "a missing .sha256 produced the wrong error: $out" ;;
  esac
fi
unchanged "missing .sha256" || true

# ─── --tag adopts a named release regardless of what the API says ──────────

reset "$old_tag"
mkdir -p "$work/download/$new_tag"
for plat in $platforms; do
  printf '%s  monad-nightly-%s\n' "$(hex_for "$plat")" "$plat" \
    > "$work/download/$new_tag/monad-nightly-$plat.sha256"
done
if out="$(run_bump --tag "$new_tag" 2>&1)"; then
  grep -qF "tag = \"$new_tag\";" "$work/nightly.nix" || fail "--tag did not rewrite the tag"
  pass
else
  fail "--tag exited non-zero: $out"
fi

# ─── the loop brake: nightly.yml must ignore a pin-only push ────────────────
#
# The scheduled bump is only self-limiting because merging a pin-only commit
# publishes no nightly (which the next bump would adopt, forever). If this
# filter disappears, every bump begets a nightly -- so assert it is still there.
nightly_workflow="$root/.github/workflows/nightly.yml"
if grep -q 'paths-ignore:' "$nightly_workflow" && grep -q '"nix/nightly.nix"' "$nightly_workflow"; then
  pass
else
  fail "nightly.yml no longer ignores a pin-only push; the bump workflow would loop"
fi

echo "check-nightly-pin: $passed passed, $failed failed"
[ "$failed" -eq 0 ]
