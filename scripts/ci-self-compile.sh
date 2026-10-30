#!/usr/bin/env bash
# Self-compile the compiler for CI under the LATEST PUBLISHED NIGHTLY.
#
# The invariant this script enforces: the last nightly can compile the next
# compiler. A tree that uses a construct the nightly does not know yet fails
# here, at the gate, instead of on a user's machine after `monadup update`.
# The Rust host is the compiler used by the release ladder, but it is NOT a
# fallback for this check: falling back is how an incompatible tree passed CI
# before (see plans/bootstrapping/native-rollout.md).
#
# `bootstrap/nightly-floor.txt` is the one temporary exception. It names the
# commit the tree first required from a nightly. While the latest nightly
# predates that commit, this script says so loudly and uses the Rust host --
# the nightly that would prove the invariant has not been published yet.
# Once a nightly at or after the floor exists, the check is strict and stays
# strict; a future incompatible change cannot use the floor to opt out.
#
# Local use:
#   scripts/ci-self-compile.sh [out-dir]
#   MONAD_ALLOW_RUST_FALLBACK=1 scripts/ci-self-compile.sh   # explicit opt-out
#   MONADUP_BIN=/path/to/monadup scripts/ci-self-compile.sh  # pick the installer
#
# The nightly is installed with `monadup default` (install latest, set it
# active), so the host is `$MONAD_HOME/bin/monad` -- the active shim, no
# output parsing. `monad version` prints the commit the nightly was built
# from, and that is what the floor comparison reads.
#
# Both hosts build the SAME thing: `scripts/build-self-hosted.sh` compiles
# `cli/src/main.mo` from THIS checkout (MONAD_STDLIB pinned to the checkout's
# init/src by that script), one rung for a `monad` host (native speed, ~1 min),
# an interpreted two-rung build for a monad-rs host (~22 min).
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

out="${1:-$root/target-monad/ci-self-compile}"
floor_file="${MONAD_NIGHTLY_FLOOR:-$root/bootstrap/nightly-floor.txt}"
allow_fallback="${MONAD_ALLOW_RUST_FALLBACK:-0}"
fallback_host="${MONAD_HOST_BIN:-"cargo run --manifest-path $root/rust/Cargo.toml --release --"}"

say() { printf 'ci-self-compile: %s\n' "$*" >&2; }

# The Rust-host path. By default this is a FAILURE, not a fallback: the whole
# point of the gate is that the nightly can build the tree. The opt-out exists
# for a local checkout with no network, and CI never sets it.
rust_fallback() {
  local why="$1"
  if [ "$allow_fallback" != 1 ]; then
    say "FAILED: $why"
    say "The last nightly must be able to build this tree. See AGENTS.md's"
    say "'Bootstrap compatibility': land new language/native support first and"
    say "use it in compiler sources only after a nightly contains it. Do not"
    say "set MONAD_ALLOW_RUST_FALLBACK=1 to make CI green."
    exit 1
  fi
  say "$why -- falling back to the Rust host (MONAD_ALLOW_RUST_FALLBACK=1)"
  MONAD_HOST_BIN="$fallback_host" scripts/build-self-hosted.sh "$out"
  say "self-compile OK with the Rust host fallback ($fallback_host)"
}

# ─── Find the latest nightly ────────────────────────────────────────────────

nightly=""
monad_home="${MONAD_HOME:-"$HOME/.monad"}"
# `monadup` is not part of the dev shell: the real tool is a published release
# asset and the repo ships only the bootstrap stub (`scripts/monadup`). Prefer
# an explicit MONADUP_BIN, then PATH, then the stub, then an installed copy.
if [ -n "${MONADUP_BIN:-}" ]; then
  monadup_bin="$MONADUP_BIN"
  [ -x "$monadup_bin" ] || rust_fallback "MONADUP_BIN ($monadup_bin) is not executable"
elif command -v monadup >/dev/null 2>&1; then
  monadup_bin="$(command -v monadup)"
elif [ -x "$root/scripts/monadup" ]; then
  monadup_bin="$root/scripts/monadup"
elif [ -x "$monad_home/bin/monadup" ]; then
  monadup_bin="$monad_home/bin/monadup"
else
  rust_fallback "no monadup on PATH (and no scripts/monadup installer)"
fi
if ! "$monadup_bin" default; then
  rust_fallback "monadup could not install the latest nightly"
elif [ ! -x "$monad_home/bin/monad" ]; then
  rust_fallback "monadup reported success but $monad_home/bin/monad is not executable"
else
  nightly="$monad_home/bin/monad"
fi

nightly_commit="$("$nightly" version 2>/dev/null | tr -d '[:space:]' || true)"
if [ -z "$nightly_commit" ] || [ "$nightly_commit" = unknown ]; then
  rust_fallback "the installed nightly does not report a commit (\`monad version\` was '${nightly_commit}')"
fi

# ─── The one-time bootstrap window ──────────────────────────────────────────

floor=""
if [ -f "$floor_file" ]; then
  floor="$(tr -d '[:space:]' < "$floor_file")"
fi
if [ "$floor" = pending ]; then
  # The tree needs a loader feature the published nightlies predate (the
  # `workspace = true` reader). A commit SHA cannot express that window
  # across a rebase-merge, so the floor is the explicit sentinel; replace it
  # with the first nightly's commit once that nightly exists.
  say "the nightly floor is pending: this tree needs a loader the published nightlies predate"
  say "the required check resumes when bootstrap/nightly-floor.txt names a nightly's commit"
  MONAD_HOST_BIN="$fallback_host" scripts/build-self-hosted.sh "$out"
  say "self-compile OK with the Rust host (pending floor)"
  exit 0
fi
if [ -n "$floor" ]; then
  if ! git -C "$root" rev-parse --verify --quiet "$floor^{commit}" >/dev/null; then
    rust_fallback "bootstrap/nightly-floor.txt names '$floor', which is not in this clone"
  fi
  # True exactly when the nightly predates the floor: the release that would
  # prove the invariant has not been cut yet. This is the only non-strict path.
  if git -C "$root" merge-base --is-ancestor "$nightly_commit" "$floor" 2>/dev/null; then
    say "the latest nightly ($nightly_commit) predates this tree's floor ($floor)"
    say "the required check resumes when a nightly at or after $floor is published"
    MONAD_HOST_BIN="$fallback_host" scripts/build-self-hosted.sh "$out"
    say "self-compile OK with the Rust host (bootstrap window)"
    exit 0
  fi
fi

# ─── The required check ─────────────────────────────────────────────────────

# A binary left by an earlier run must not satisfy build-self-hosted.sh's
# staleness check: the host that built it is the thing under test.
rm -rf "$out"

nightly_rc=0
MONAD_HOST_BIN="$nightly" scripts/build-self-hosted.sh "$out" || nightly_rc=$?
if [ "$nightly_rc" -ne 0 ]; then
  rust_fallback "the latest nightly ($nightly_commit) cannot build this tree"
fi

# Building is not enough: the binary has to do the job it was built for. A
# nightly that compiles the sources but miscompiles them is the failure class
# the old fallback scheme accepted (see the await_fiber_raw incident).
if ! "$out/monad" check cli/src/main.mo; then
  rust_fallback "the nightly-built compiler ($nightly_commit) cannot check cli/src/main.mo"
fi
built="$("$out/monad" version 2>/dev/null | tr -d '[:space:]' || true)"
if [ -z "$built" ] || [ "$built" = unknown ]; then
  rust_fallback "the nightly-built compiler did not report a commit"
fi

say "self-compile OK with the latest nightly host ($nightly_commit); built compiler reports $built"
