#!/usr/bin/env bash
# Run `monad fmt --check` over the whole Monad source corpus.
#
# Usage: scripts/check-fmt.sh [monad-binary]
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

echo "check-fmt.sh: checking ${#paths[@]} path(s) with $bin"
exec "$bin" fmt --check "${paths[@]}"
