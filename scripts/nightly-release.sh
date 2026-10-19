#!/usr/bin/env bash
# Build the nightly release artifact: the self-hosted compiler, staged into
# <root>/dist/ exactly where the release step in .github/workflows/nightly.yml
# uploads from.
#
# The binary itself comes from the flake -- `.#monad` for this machine's
# platform, `.#monad-<platform>` for one it only cross-builds -- and that is
# what a matrix of legs can afford. Both are rung 1, ONE ~26-minute
# interpretation of the compiler by the Rust host, relinked per target in
# seconds; a leg that ran its own interpretation would pay that cost again for
# every platform, and three legs would cost a night three self-compiles.
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
#
# Usage: scripts/nightly-release.sh [platform]
#
# `platform` names the artifacts (`monad-nightly-<platform>`) and, absent an
# argument, comes from an ambient MONAD_PLATFORM and then from this machine's
# own label; see scripts/lib/platform-label.sh. A cross leg must pass its
# TARGET's label, since the binary it stages is named after the platform it is
# for and not after the runner that produced it.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
# Argument, then environment, then the lib's table. `${1:-}` alone CLOBBERS an
# ambient MONAD_PLATFORM with the empty string, which the lib reads as "unset"
# -- so a cross leg driven from the environment silently published this
# machine's native label instead.
MONAD_PLATFORM="${1:-${MONAD_PLATFORM:-}}"
# shellcheck source=scripts/lib/platform-label.sh
# shellcheck disable=SC1091  # the hook runs bare `shellcheck`; the line above names the path for -x
. "$root/scripts/lib/platform-label.sh"
bin="$root/dist/monad-nightly-${MONAD_PLATFORM}"
# One name and not `commit-<platform>.txt`, even with several legs: an
# installed `monadup` resolves this asset from the releases API by exact name
# (`scripts/monadup`, `do_install`), so a per-leg name is a release no shipped
# installer can read. The legs' copies hold the same revision -- the release
# job asserts that before uploading -- so the one the release keeps is not a
# choice between different answers.
commit_file="$root/dist/commit.txt"

# Which flake output holds this platform's binary, and whether that binary can
# be run by the machine that built it. The two questions have the same answer,
# and it is the one `MONAD_PLATFORM` and `MONAD_NATIVE_PLATFORM` disagree on: a
# cross leg stages a binary for a platform it is not.
if [ "$MONAD_PLATFORM" = "$MONAD_NATIVE_PLATFORM" ]; then
  attr=monad
  runs_here=yes
else
  attr="monad-${MONAD_PLATFORM}"
  runs_here=no
fi

# A self-hosted runner's workspace is dirty across runs and the release step
# uploads whatever is in dist/ -- clear it, so a failed build can never
# publish the previous night's binary.
rm -rf "$root/dist"
mkdir -p "$root/dist"

cd "$root"

# `nix build` and not an in-workflow self-compile, because the flake's `monad`
# IS that self-compile: rung 1 is `scripts/build-self-hosted.sh` run inside a
# derivation (`nix/monad.nix`), and `.#monad` relinks its `.ll` with this
# commit's revision. Taking it from the store is what lets every leg of a
# night's matrix share one interpretation -- and it is the same command
# ci.yml's `flake-package` job and `checks.bootstrap` already build, so it is
# a path in daily use rather than a new one.
#
# The revision the artifact claims is then baked by the flake, not by this
# script: `MONAD_BUILD_COMMIT` from `self.shortRev` at LINK time, in whichever
# process does the linking -- which is why the check below is on the BINARY's
# answer rather than on an environment variable this script could set.
out="$(nix build --no-link --print-out-paths --accept-flake-config ".#${attr}")"
# `share/monad/monad` and NOT `bin/monad`: the latter is `makeWrapper`'s script,
# a store path's worth of environment around the real binary, and a consumer
# installing this artifact has no store to run it out of. What is published is
# the binary the wrapper wraps -- the same bare ELF `build-self-hosted.sh`
# leaves in `dist/` -- so a release's artifact does not change shape here.
install -m755 "$out/share/monad/monad" "$bin"
test -x "$bin"
file "$bin"

# A published binary must load no library out of the store it was copied
# from: the one that did died in dyld before `main` on every machine without
# that exact path, while every check below passed -- they run HERE, where the
# store is. `nix/monad.nix` links libgc statically on every target and adds
# `-static` on Linux for this reason.
case "$MONAD_PLATFORM" in
  *-darwin)
    # Captured, not piped into `grep -q`: under pipefail an early-exiting grep
    # can SIGPIPE the producer and turn a match into a failed condition.
    linked="$(otool -L "$bin")"
    printf '%s\n' "$linked"
    if printf '%s\n' "$linked" | tail -n +2 | grep '/nix/store/' >/dev/null; then
      echo "nightly-release: $bin links a library from /nix/store, so it cannot run" >&2
      echo "  on a machine without that store path" >&2
      exit 1
    fi
    ;;
  *-linux)
    # A static binary has no dynamic dependencies. `ldd` reports
    # "not a dynamic executable" for a fully static binary; any line
    # naming a /nix/store path means a library slipped through.
    ldd_output="$(ldd "$bin" 2>&1)" || true
    printf '%s\n' "$ldd_output"
    if printf '%s\n' "$ldd_output" | grep '/nix/store/' >/dev/null; then
      echo "nightly-release: $bin links a library from /nix/store, so it cannot run" >&2
      echo "  on a machine without that store path" >&2
      exit 1
    fi
    ;;
esac

if [ "$runs_here" = yes ]; then
  # What the binary says it was built from. An unidentifiable published
  # artifact is a real defect, not a cosmetic one -- so an empty or "unknown"
  # line fails here. It is also what the release job compares the other legs'
  # `commit.txt` against, which is the only thing tying a cross-built asset to
  # the revision this release says it is.
  "$bin" version > "$commit_file"
  cat "$commit_file"
  grep -qvE '^$|^unknown$' "$commit_file"

  # The binary that ships has to do the job it was built for: the same ~12s
  # front-end sweep `monad:bootstrap-compile` runs in ci.yml, on the exact
  # artifact being published.
  "$bin" check cli/src/main.mo
else
  # Neither of those can run here: a cross binary does not execute on the
  # machine that built it, which is what makes it cross. Its verification is
  # the derivation's own `checkPhase`, which ran as part of the `nix build`
  # above -- it compiles an allocating probe with this binary under qemu and
  # runs it (nix/monad.nix, `crossMonadFor`). Said out loud rather than
  # skipped, because a verification that quietly stops happening is worse
  # than one that never existed.
  echo "nightly-release: ${MONAD_PLATFORM} does not run here; verified by the ${attr} checkPhase (qemu)"

  # Not `git rev-parse --short HEAD`: nix's shortRev is seven characters and
  # this repository's git spells the same revision in eight, so a tree-derived
  # answer differs for a reason that is not a defect. The stamp is read out of
  # the derivation instead -- the `--set MONAD_BUILD_COMMIT` in the install
  # phase -- which is what the binary itself would say if it could be asked.
  stamped="$(nix eval --raw ".#${attr}.installPhase" \
    | sed -n 's/^.*--set MONAD_BUILD_COMMIT \([^ ]*\).*$/\1/p')"
  if [ -z "$stamped" ]; then
    echo "nightly-release: .#${attr}'s install phase carries no MONAD_BUILD_COMMIT, so" >&2
    echo "  this leg cannot say which revision it just published" >&2
    exit 1
  fi
  printf '%s\n' "$stamped" > "$commit_file"
  cat "$commit_file"
fi

# The monadup binary asset, beside the compiler. It is the same tool the
# bash stub installed before, now a Monad-compiled binary. The native leg
# gets `. #monadup`; a cross leg `. #monadup-<platform>`. Its checkPhase runs
# `monadup --version` natively (or under qemu), so a leg that only builds
# cannot publish a binary that does not start.
up_attr="monadup"
if [ "$runs_here" = no ]; then
  up_attr="monadup-${MONAD_PLATFORM}"
fi
up_out="$(nix build --no-link --print-out-paths --accept-flake-config ".#${up_attr}")"
up_bin="$root/dist/monadup-${MONAD_PLATFORM}"
install -m755 "$up_out/bin/monadup" "$up_bin"
test -x "$up_bin"
file "$up_bin"
case "$MONAD_PLATFORM" in
  *-darwin)
    linked="$(otool -L "$up_bin")"
    printf '%s\n' "$linked"
    if printf '%s\n' "$linked" | tail -n +2 | grep '/nix/store/' >/dev/null; then
      echo "nightly-release: $up_bin links a library from /nix/store, so it cannot run" >&2
      echo "  on a machine without that store path" >&2
      exit 1
    fi
    ;;
  *-linux)
    ldd_output="$(ldd "$up_bin" 2>&1)" || true
    printf '%s\n' "$ldd_output"
    if printf '%s\n' "$ldd_output" | grep '/nix/store/' >/dev/null; then
      echo "nightly-release: $up_bin links a library from /nix/store, so it cannot run" >&2
      echo "  on a machine without that store path" >&2
      exit 1
    fi
    ;;
esac
if [ "$runs_here" = yes ]; then
  up_version="$("$up_bin" --version)"
  printf '%s\n' "$up_version"
  case "$up_version" in
    monadup\ *) ;;
    *)
      echo "nightly-release: $up_bin did not report 'monadup <version>'" >&2
      exit 1
      ;;
  esac
else
  echo "nightly-release: ${MONAD_PLATFORM} monadup does not run here; verified by the ${up_attr} checkPhase (qemu)"
fi

# The second artifact: `init`/`std`/`runtime`, which is what lets the binary
# above compile anything OUTSIDE a compiler checkout. `monadup` unpacks it
# into the same version directory as the binary, and the compiler then finds
# it as a toolchain root (`Mote.toolchain_root`, `lang/src/mote.mo`). Staged
# by its own script because that script is also what the staging test drives
# against a temp directory -- see scripts/check-monadup.sh. It takes the same
# label, so the two artifacts of a leg are always for the same platform.
"$root/scripts/stage-mote-sources.sh" "$root/dist" "$MONAD_PLATFORM"

# Checksums for every downloadable artifact, published beside it and
# verified by `monadup`/the bootstrap stub when present. `commit.txt` and
# the tarball are not executables, but the sources become the toolchain a
# later build reads, so they are covered too.
for asset in \
  "$root/dist/monad-nightly-${MONAD_PLATFORM}" \
  "$root/dist/monadup-${MONAD_PLATFORM}" \
  "$root/dist/monad-src-${MONAD_PLATFORM}.tar.gz" \
  "$root/dist/monad-src.tar.gz"; do
  if [ -f "$asset" ]; then
    ( cd "$(dirname "$asset")" && sha256sum "$(basename "$asset")" > "$(basename "$asset").sha256" )
  fi
done

# The workflow's `tag`/`date` step outputs, for the release step. Written
# here rather than in a second `nix develop` step of their own: they are this
# script's own output, so a second entry would buy nothing and add a second
# way for the release job to fail over something that has nothing to do with
# the release. `date` here is the dev shell's coreutils, like every other
# command in this script.
#
# Nothing is saved by avoiding a shell entry either way, and that is the one
# thing about the cost worth writing down: nightly.yml sets
# DEVENV_SKIP_TASKS=1, so entering the dev shell no longer runs the
# pre-commit sweep (the shellHook's devenv-tasks invocation is gated on
# that variable). The outputs argument above still decides the shape --
# writing them here rather than in a second `nix develop -c` avoids a second
# way for the release job to fail over something unrelated to the release.
# Unset outside Actions, which is the only place these outputs mean anything.
if [ -n "${GITHUB_OUTPUT:-}" ]; then
  date_utc="$(date -u +%Y-%m-%d)"
  # The revision is IN the tag so two pushes in one UTC day cannot share a
  # release: `softprops/action-gh-release` overwrites same-named assets and
  # never deletes, and the "every leg the same revision" check reads only the
  # `commit.txt` files that ARE present, so it cannot see a stale binary left
  # by an earlier run. `scripts/monadup` filters on the `nightly-` prefix only.
  rev_short="${GITHUB_SHA:-}"
  rev_short="${rev_short:0:8}"
  tag="nightly-${date_utc}"
  if [ -n "$rev_short" ]; then tag="${tag}-${rev_short}"; fi
  {
    printf 'tag=%s\n' "$tag"
    printf 'date=%s\n' "$date_utc"
    printf 'rev=%s\n' "$rev_short"
  } >> "$GITHUB_OUTPUT"
fi
