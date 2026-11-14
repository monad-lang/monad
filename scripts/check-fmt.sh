#!/usr/bin/env bash
# Run `monad fmt --check` over the whole Monad source corpus, or over the
# named files that fall inside it.
#
# Usage: scripts/check-fmt.sh [monad-binary] [-- file...]
#
# With `-- file...` (the pre-commit hook, devenv.nix's `monad-fmt`) only the
# named `.mo` files under a gated path below are checked, so a commit is held
# to exactly the rule CI's Formatting gate applies to the whole corpus, and a
# file outside the corpus (an intentionally unparseable fixture) is skipped
# the same way the gate skips it.
#
# The formatter ships inside the self-hosted compiler, so CI passes the
# rung-1 binary it just built. A developer can pass
# target-monad/fmt-build/monad (scripts/build-self-hosted.sh), and the
# fallback tries the usual local build directories, then `monad` on PATH.
#
# `paths` below is every parseable `.mo` source in the checkout. Two groups
# are deliberately EXCLUDED because they are designed not to parse:
#
#   * fixtures/lsp/                      intentionally invalid, and
#                                        byte-offset-sensitive LSP fixtures
#                                        (scripts/replay-lsp-session.sh)
#   * scripts/weaver-tui-repro/probes/   intentional parse-failure repros
#
# Markdown fences (docs/src/*.md, AGENTS.md) are not `.mo` files and are
# outside `monad fmt`'s scope. A NEW top-level source root has to be added
# to `paths`, or it is not gated; `motes` covers every mote, including ones
# that are not workspace members.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

bin=""
if [ "$#" -gt 0 ] && [ "$1" != "--" ]; then
  bin="$1"
  shift
fi
files=()
file_mode=0
if [ "$#" -gt 0 ] && [ "$1" = "--" ]; then
  file_mode=1
  shift
  files=("$@")
fi
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
if [ -z "$bin" ] && [ "$file_mode" -eq 1 ]; then
  # The pre-commit hook in an environment with no compiler at all: CI's
  # pre-commit-checks job, whose dev shell carries none. That job is not
  # where formatting is gated -- compiler-checks' Formatting gate runs this
  # script over the whole corpus with the tree's own compiler -- so the hook
  # steps aside rather than fail a check it cannot run. A developer's
  # machine always has one (monadup installs it).
  echo "check-fmt.sh: no monad binary; skipping (CI's Formatting gate checks the corpus)" >&2
  exit 0
fi
if [ -z "$bin" ]; then
  echo "check-fmt.sh: no monad binary (pass one, or put one on PATH)" >&2
  exit 1
fi

paths=(
  init
  std
  sys
  lang
  codegen
  cli
  llvm
  mlir
  runtime
  build
  eval
  slow_tests
  bench
  proofs
  motes
  examples
  docs/site/monad_website
  fixtures/wasm
  fixtures/cfg
  fixtures/mlir
)

for path in "${paths[@]}"; do
  if [ ! -e "$path" ]; then
    echo "check-fmt.sh: missing corpus path $path" >&2
    exit 1
  fi
done

if [ "$file_mode" -eq 1 ]; then
  gated=()
  for f in "${files[@]}"; do
    case "$f" in *.mo) ;; *) continue ;; esac
    [ -e "$f" ] || continue
    for path in "${paths[@]}"; do
      case "$f" in
        "$path"/*)
          gated+=("$f")
          break
          ;;
      esac
    done
  done
  if [ "${#gated[@]}" -eq 0 ]; then
    exit 0
  fi
  exec "$bin" fmt --check "${gated[@]}"
fi

echo "check-fmt.sh: checking ${#paths[@]} path(s) with $bin"
exec "$bin" fmt --check "${paths[@]}"
