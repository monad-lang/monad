#!/usr/bin/env bash
# Enforce the one-way compiler dependency: `codegen` may import `lang`, but
# `lang` must never import `codegen`.
#
# The backend is its own mote (`codegen/`) and `lang/` is its dependency. A
# `use ... codegen::` line in `lang/` would reintroduce the front-end ->
# backend cycle that the name-text split cut, so this gate is checked before
# the build and on every compiler CI run.
#
# It matches `use`/`pub use` lines, not comments: prose that names
# `codegen::emit` is fine.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

hits="$(grep -rnE '^[[:space:]]*(pub[[:space:]]+)?use[[:space:]].*codegen::' \
    --include='*.mo' lang/src || true)"
if [ -n "$hits" ]; then
    echo "lang must not depend on codegen (only codegen -> lang):" >&2
    printf '%s\n' "$hits" >&2
    exit 1
fi
