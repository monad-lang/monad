#!/usr/bin/env bash
# Enforce commit message format: "scope: msg", "scope/sub: msg", or
# "scope/sub(type): msg" (matches existing convention, e.g. "codegen: ...",
# "lang/scope: ...", "core/term/module: ...").
#
# Wired in as a git commit-msg hook via devenv.nix's git-hooks.hooks, but
# runs standalone too:
#   ./scripts/check-commit-msg.sh <path-to-commit-msg-file>
set -euo pipefail

msg_file="$1"
first_line="$(head -n1 "$msg_file")"

case "$first_line" in
  "Merge "*|"Revert "*)
    exit 0
    ;;
esac

pattern='^[a-zA-Z][a-zA-Z0-9_-]*(/[a-zA-Z0-9_-]+)*(\([a-zA-Z0-9_-]+\))?: .+'

if ! printf '%s' "$first_line" | grep -qE "$pattern"; then
  echo "Commit message must start with 'scope: ', 'scope/sub: ', or 'scope/sub(type): ' (got: '$first_line')" >&2
  exit 1
fi
