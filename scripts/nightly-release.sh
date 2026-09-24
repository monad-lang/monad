#!/usr/bin/env bash
# Build the nightly release artifact: one self-compile of the self-hosted
# compiler, staged into <root>/dist/ exactly where the release step in
# .github/workflows/nightly.yml uploads from.
#
# This used to be four inline `run:` lines in that workflow, and the first
# of them -- `file dist/monad-nightly-x86_64-linux` -- was the only command
# in the repo that ran outside `nix develop`. A bare `run:` gets the
# RUNNER HOST's PATH, not the dev shell's, so `file` was "command not
# found" on the runner while resolving fine for anyone sitting in the dev
# shell whose devenv.nix lists it. Keeping the whole pipeline here, entered
# through `nix develop` -- and locally as `devenv tasks run monad:nightly`,
# or this script directly -- is what makes every tool it uses a declared
# dependency instead of an assumption about the host.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
bin="$root/dist/monad-nightly-x86_64-linux"

# A self-hosted runner's workspace is dirty across runs and the release step
# uploads whatever is in dist/ -- clear it, so a failed build can never
# publish the previous night's binary.
rm -rf "$root/dist"
mkdir -p "$root/dist"

cd "$root"
cargo run --release -- run cli/src/main.mo compile cli/src/main.mo \
  "$bin" --verbose --release
test -x "$bin"
chmod +x "$bin"
file "$bin"

# What the binary says it was built from. `runtime/src/runtime.c`'s
# `build_commit` falls back to "unknown" when the link stage could not reach
# `git` (llvm/src/link.mo's `build_commit_hash` shells out to `git rev-parse
# --short HEAD`), and an unidentifiable published artifact is a real defect,
# not a cosmetic one -- so an empty or "unknown" line fails here.
"$bin" version > "$root/dist/commit.txt"
cat "$root/dist/commit.txt"
grep -qvE '^$|^unknown$' "$root/dist/commit.txt"

# The binary that ships has to do the job it was built for: the same ~12s
# front-end sweep `monad:bootstrap-compile` runs in ci.yml, on the exact
# artifact being published.
"$bin" check cli/src/main.mo

# The workflow's `tag`/`date` step outputs, for the release step. Written
# here rather than in a second `nix develop` step of their own: they are this
# script's own output, so a second entry would buy nothing and add a second
# way for the release job to fail over something that has nothing to do with
# the release. `date` here is the dev shell's coreutils, like every other
# command in this script.
#
# Nothing is saved by avoiding a shell entry either way, and that is the one
# thing about the cost worth writing down: entering the dev shell DOES run the
# pre-commit suite. The flake devShell's shellHook ends in `devenv-tasks run
# devenv:enterShell --mode all`, and `--mode all` resolves the task graph in
# both directions from that root rather than only its prerequisites -- which
# pulls in `devenv:files` (generating .pre-commit-config.yaml) and
# `devenv:git-hooks:run` (the full `prek run -a` -- 75s warm, 291s measured
# cold), on every `nix develop -c` in this repo. `DEVENV_SKIP_TASKS=1` is the
# only way to suppress it. So a second entry here would cost a second sweep,
# not a `prek install`.
# Unset outside Actions, which is the only place these outputs mean anything.
if [ -n "${GITHUB_OUTPUT:-}" ]; then
  date_utc="$(date -u +%Y-%m-%d)"
  printf 'tag=nightly-%s\n' "$date_utc" >> "$GITHUB_OUTPUT"
  printf 'date=%s\n' "$date_utc" >> "$GITHUB_OUTPUT"
fi
