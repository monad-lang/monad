#!/usr/bin/env bash
# Push to the project's Cachix cache (monad-lang.cachix.org).
#
# Called from CI inside `nix develop`, which is where `cachix` is (nix/packages.nix).
# The darwin leg is the exception and enters it through `nix shell nixpkgs#cachix`
# instead, because that runner cannot realise the dev shell at all.
# Nothing else pushes: the runners' user is not a trusted Nix user, so there is
# no post-build hook to catch paths as they are built, and cachix-action's
# fallback in that situation scans the whole store and would upload whatever
# else the machine built meanwhile.
#
#   push-to-cache.sh <store-path>...   those paths, with their closures
#   push-to-cache.sh --inputs          the flake's inputs, for a cold store
#
# Without CACHIX_AUTH_TOKEN there is nothing to push and nothing to report: a
# PR from a fork gets no secrets, and that is not a failure.
set -euo pipefail

cache=monad-lang

if [ -z "${CACHIX_AUTH_TOKEN:-}" ]; then
  echo "push-to-cache: no CACHIX_AUTH_TOKEN, nothing pushed"
  exit 0
fi

if [ "${1:-}" = "--inputs" ]; then
  # An input is FETCHED rather than built, so no build hook can see one; only a
  # store that starts empty wants them, which is the Tangled microVMs and not
  # the runners, which keep theirs.
  nix flake archive --json --accept-flake-config \
    | grep -o '/nix/store/[^"]*' | sort -u \
    | xargs --no-run-if-empty cachix push "$cache"
elif [ "$#" -gt 0 ]; then
  cachix push "$cache" "$@"
else
  echo "push-to-cache: no paths given, nothing pushed"
fi
