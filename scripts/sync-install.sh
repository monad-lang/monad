#!/usr/bin/env bash
#
# Copy the monadup bootstrap stub to the Zola site's static directory so it
# is served at https://monad-lang.org/install.
#
# `scripts/monadup` stays canonical; `docs/site/static/install` is generated
# build output (gitignored). The devenv docs tasks and the deploy workflow
# run this before `zola build`.
#
# Usage: scripts/sync-install.sh
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
src="$root/scripts/monadup"
dest="$root/docs/site/static/install"

mkdir -p "$(dirname "$dest")"
cp "$src" "$dest"
chmod +x "$dest"
echo "sync-install: wrote $dest"
