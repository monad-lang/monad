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

# TEMPORARY (codegen-mote-extraction Phase 1): the four pre-existing edges
# that `lang/src/name_text.mo` removes. Delete this allowlist in the Phase 1
# commit; after that every hit is a regression.
allow='^(lang/src/(lib|elaborate|scope)\.mo|lang/src/typecheck/meta_reflect\.mo):'

# `lang/src/codegen/` is the backend itself before the move; its internal
# `lib::codegen::` imports are not front-end -> backend edges. After the move
# the directory is gone, so the exclusion is harmless.
hits="$(grep -rnE '^[[:space:]]*(pub[[:space:]]+)?use[[:space:]].*codegen::' \
    --include='*.mo' --exclude-dir=codegen lang/src || true)"
if [ -n "$hits" ]; then
    hits="$(printf '%s\n' "$hits" | grep -vE "$allow" || true)"
fi
if [ -n "$hits" ]; then
    echo "lang must not depend on codegen (only codegen -> lang):" >&2
    printf '%s\n' "$hits" >&2
    exit 1
fi
