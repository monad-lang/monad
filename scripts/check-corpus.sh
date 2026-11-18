#!/usr/bin/env bash
# The whole-corpus check through the RUST host -- the `Rust corpus check` step
# of CI's `compiler-checks`, extracted so the pre-push hook and the workflow
# run the same command.
#
# WHAT IT IS. `monad-rs check` over every parseable `.mo` source in the
# checkout. It is the pipeline's only whole-corpus check, and it exercises
# every rule the bootstrap host enforces -- `use` completeness among them,
# which the loader also applies by default on every check/run/test/build/LSP
# path. The name says "corpus" rather than "use completeness" because the step
# is broader than that rule: it is also where a host-only name-resolution
# difference (a bare `Event`/`Sub` colliding with a flattened corpus
# declaration) shows up.
#
# WHY THE RUST HOST AND NOT THE SELF-HOSTED COMPILER. The step's whole point
# is to grade the *bootstrap host* on the compiler-source surface, since that
# is the binary the two-step rollout depends on. The self-hosted compiler is
# graded by the sweep in scripts/ci-compiler-checks.sh; if this used the
# self-hosted binary the step and the sweep would be the same gate twice, and
# a host-only divergence -- exactly the kind this catches -- would be invisible
# in both.
#
# COST, and why it is a PRE-PUSH hook rather than a pre-commit one. Measured
# 2026-11-16 on this checkout, warm: ~3m40s for the whole corpus, against
# ~24s for a single file. AGENTS.md is explicit that this sweep is not paid
# per commit -- "run in CI, not hooks ... but run them before pushing anything
# that touches the compiler" -- so the hook is installed on `pre-push`, the
# point AGENTS.md actually names. A commit stays fast; a push that would go
# red in CI fails here instead, seconds after the push instead of a full
# pipeline later.
#
# THE HOST. `MONAD_HOST_BIN` names it, defaulting to `cargo run --release --`
# -- the same host CI's step uses, and the one that cannot lag the tree. A
# binary path works too (much faster when you already have one built):
#
#   scripts/check-corpus.sh
#   MONAD_HOST_BIN=rust/target/release/monad-rs scripts/check-corpus.sh
#   MONAD_HOST_BIN="cargo run --manifest-path rust/Cargo.toml --release --quiet --" scripts/check-corpus.sh
#
# `cargo run` recompiles nothing when the tree is warm, so the default costs a
# cargo invocation and no build; the hooks in CI and locally both go through
# it, which is what keeps this script and the workflow step identical.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

# The corpus, spelled once. `scripts/bootstrap_next.mo` is a script rather
# than a mote source, so it is named after the directories.
corpus=(
  init std sys examples lang codegen cli llvm runtime build eval motes
  scripts/bootstrap_next.mo
)

for path in "${corpus[@]}"; do
  if [ ! -e "$path" ]; then
    echo "check-corpus.sh: missing corpus path $path" >&2
    exit 1
  fi
done

monad_host="${MONAD_HOST_BIN:-cargo run --manifest-path $root/rust/Cargo.toml --release --}"

# A cap, the way AGENTS.md prescribes for a whole-corpus sweep: a name
# resolution regression has hard-restarted machines, and the cap turns that
# into exit 137 rather than an OOM. `systemd-run` is used only when it is
# available and we are not already inside a scope (a nested scope is harmless
# but noisy), so a macOS or container dev still gets the plain run.
if command -v systemd-run >/dev/null 2>&1 && [ -z "${MONAD_NO_MEMORY_CAP:-}" ]; then
  # shellcheck disable=SC2086  # MONAD_HOST_BIN is deliberately word-split
  exec systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0 --collect -- \
    $monad_host check "${corpus[@]}"
fi

# shellcheck disable=SC2086  # MONAD_HOST_BIN is deliberately word-split
exec $monad_host check "${corpus[@]}"
