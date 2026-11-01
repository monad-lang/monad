#!/usr/bin/env bash
# Run `monad fmt --check` over the opt-in ratchet list.
#
# Usage: scripts/check-fmt.sh [monad-binary]
#
# The formatter ships inside the self-hosted compiler, so CI passes the
# rung-1 binary it just built. A developer can pass
# target-monad/fmt-build/monad (scripts/build-self-hosted.sh), and the
# fallback tries the usual local build directories, then `monad` on PATH.
#
# The ratchet is scripts/fmt-ratchet.txt: paths the project has decided to
# keep formatted. Growing it is deliberate; the whole corpus is not formatted
# yet (see the file's own header).
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

bin="${1:-}"
if [ -z "$bin" ]; then
  for candidate in \
    "$root/target-monad/ci-self-compile/monad" \
    "$root/target-monad/fmt-build/monad"; do
    if [ -x "$candidate" ]; then
      bin="$candidate"
      break
    fi
  done
fi
if [ -z "$bin" ]; then
  bin="$(command -v monad || true)"
fi
if [ -z "$bin" ]; then
  echo "check-fmt.sh: no monad binary (pass one, or put one on PATH)" >&2
  exit 1
fi

list="$root/scripts/fmt-ratchet.txt"
if [ ! -f "$list" ]; then
  echo "check-fmt.sh: missing $list" >&2
  exit 1
fi

paths=()
while IFS= read -r line; do
  line="${line%%#*}"
  line="$(printf '%s' "$line" | sed 's/^[[:space:]]*//; s/[[:space:]]*$//')"
  if [ -n "$line" ]; then
    paths+=("$line")
  fi
done < "$list"

if [ "${#paths[@]}" -eq 0 ]; then
  echo "check-fmt.sh: $list names no paths" >&2
  exit 1
fi

echo "check-fmt.sh: checking ${#paths[@]} path(s) with $bin"
exec "$bin" fmt --check "${paths[@]}"
