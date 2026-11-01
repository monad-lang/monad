#!/usr/bin/env bash
# monadup-checks' test leg: the latest NIGHTLY compiles THIS checkout's
# monadup and type-checks check-monadup.sh's scaffold. The nightly is the only
# host: there is no flake `.#monadup` + Rust-host fallback, because that path
# emits the mote's IR with `monadRung1` (the Rust host interpreting the whole
# compiler) and paid ~15 minutes on every compiler-touching PR.
#
# The nightly leg can fail when a PR outgrows a nightly cut from main (a parser
# or prelude change); that is a failure here, not a reason to pay the monad-rs
# build. It can also SUCCEED and still be unusable: the compiler carries the
# native wiring (each native's wrap kind and payload type) in its own tables,
# so a nightly cut before a change to those tables builds this tree's monadup
# into a binary whose IO natives hand back the wrong value -- `MONAD_HOME` and
# `MONADUP_UNAME` stop being read -- and the distribution checks then fail as
# though the RELEASE were at fault. That is a host problem, so
# `monadup_honours_env` below settles it here.
# A CHECK failure is not a reason to fall back: check-monadup.sh runs once,
# on whichever binary was built.
#
# The nightly comes from `monadup default` when monadup is on PATH, else
# from the repository's own bootstrap stub (scripts/monadup), because the
# CI runners carry no monadup -- which is why ci-self-compile.sh, with no
# stub leg, always took its fallback there. The stub needs curl and jq,
# which the devshell provides (nix/packages.nix).
#
# The packaged artifact is built and published by nightly-release.sh.
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

# Does `bin` read `MONAD_HOME`? Its own `env` report is the probe: every
# environment read that the native wiring can break lands on that line
# (`home:  <path>  (MONAD_HOME)` when honoured, `.monad  (default)` when the
# read returned nothing). A binary built by a compiler that predates a change
# to `std/`'s natives answers the second way for every knob.
monadup_honours_env() {
  local bin="$1" home probe home_line
  home="$(mktemp -d)"
  probe="$(MONAD_HOME="$home" MONADUP_UNAME="Linux x86_64" "$bin" env 2>/dev/null || true)"
  rm -rf "$home"
  home_line="$(printf '%s\n' "$probe" | grep '^home:' || true)"
  case "$home_line" in
    *"$home"*) return 0 ;;
  esac
  return 1
}

nightly=""
if command -v monadup >/dev/null 2>&1; then
  installer=(monadup)
else
  installer=("$root/scripts/monadup")
fi
if ! MONAD_HOME="$monad_home" "${installer[@]}" default; then
  echo "ci-monadup: could not install the latest nightly (${installer[*]})" >&2
  exit 1
elif [ ! -x "$monad_home/bin/monad" ]; then
  echo "ci-monadup: the install reported success but $monad_home/bin/monad is not executable" >&2
  exit 1
else
  nightly="$monad_home/bin/monad"
fi

if ! "$nightly" build motes/monadup --bin monadup --release -o "$out/monadup"; then
  echo "ci-monadup: the latest nightly could not build motes/monadup" >&2
  exit 1
fi
if ! monadup_honours_env "$out/monadup"; then
  echo "ci-monadup: the nightly built a monadup that does not read its environment -- it predates this tree's native wiring and cannot compile it correctly" >&2
  exit 1
fi
echo "ci-monadup: monadup built with the latest nightly ($nightly)"
MONADUP_BIN="$out/monadup" MONAD_BIN="$nightly" exec scripts/check-monadup.sh
