#!/usr/bin/env bash
# monadup-checks' test leg: the latest NIGHTLY compiles THIS checkout's
# monadup and type-checks check-monadup.sh's scaffold; the flake's
# `.#monadup` plus the Rust host is the FALLBACK.
#
# The fallback is the job as it used to be, and it is slow on exactly the
# changes this job runs for: `.#monadup` emits its IR with `monadRung1`,
# the Rust host interpreting the whole compiler, so any PR that touches a
# compiler source misses the cache and pays ~15 minutes before a single
# check runs. A nightly builds the same mote natively in seconds. Like
# scripts/ci-self-compile.sh, the nightly leg can fail when a PR outgrows
# a nightly cut from main (a parser or prelude change), and then the
# fallback takes over. A CHECK failure is not a reason to fall back:
# check-monadup.sh runs once, on whichever binary was built.
#
# The nightly comes from `monadup default` when monadup is on PATH, else
# from the repository's own bootstrap stub (scripts/monadup), because the
# CI runners carry no monadup -- which is why ci-self-compile.sh, with no
# stub leg, always took its fallback there. The stub needs curl and jq,
# which the devshell provides (nix/packages.nix).
#
# What the nightly leg does NOT grade is `.#monadup`'s packaging (the
# static relink); ci.yml's portability step does, on main.
#
# Runnable by hand:
#
#   scripts/ci-monadup.sh
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

out="${1:-$root/target-monad/ci-monadup}"
mkdir -p "$out"
monad_home="${MONAD_HOME:-"$HOME/.monad"}"

nightly=""
if command -v monadup >/dev/null 2>&1; then
  installer=(monadup)
else
  installer=("$root/scripts/monadup")
fi
if ! MONAD_HOME="$monad_home" "${installer[@]}" default; then
  echo "ci-monadup: could not install the latest nightly (${installer[*]}) -- taking the fallback" >&2
elif [ ! -x "$monad_home/bin/monad" ]; then
  echo "ci-monadup: the install reported success but $monad_home/bin/monad is not executable -- taking the fallback" >&2
else
  nightly="$monad_home/bin/monad"
fi

if [ -n "$nightly" ]; then
  if "$nightly" build motes/monadup --bin monadup --release -o "$out/monadup"; then
    echo "ci-monadup: monadup built with the latest nightly ($nightly)"
    MONADUP_BIN="$out/monadup" MONAD_BIN="$nightly" exec scripts/check-monadup.sh
  fi
  echo "ci-monadup: the nightly could not build motes/monadup -- taking the fallback" >&2
fi

bin="$(nix build --no-link --print-out-paths --accept-flake-config .#monadup)"
echo "ci-monadup: monadup built from the flake ($bin)"
MONADUP_BIN="$bin/bin/monadup" MONAD_BIN="cargo run --release --quiet --" \
  exec scripts/check-monadup.sh
