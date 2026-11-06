#!/usr/bin/env bash
# Commit the already-bumped nix/nightly.nix and open (or refresh) the pin PR.
#
#   scripts/open-nightly-pin-pr.sh <tag>
#
# Run by .github/workflows/bump-nightly-pin.yml after
# scripts/bump-nightly-pin.sh has rewritten the pin in the working tree. It
# lives here, not inline in the workflow, because it uses `gh` -- a dev-shell
# package; the self-hosted runner host carries none -- so the workflow enters
# through `nix develop -c` and every tool is a declared dependency.
#
# The branch is fixed (`automation/bump-nightly-pin`), so consecutive nightly
# bumps update one PR instead of opening a new one each day. A commit here is
# a normal commit: hooks stay enabled, and the bot identity is set per-command
# rather than persisted into the checkout's config.
set -euo pipefail

tag="${1:-}"
[ -n "$tag" ] || { echo "usage: $0 <tag>" >&2; exit 1; }
[ -n "${GH_TOKEN:-}" ] || { echo "open-nightly-pin-pr: GH_TOKEN is required" >&2; exit 1; }

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

branch="automation/bump-nightly-pin"
base="${MONAD_NIGHTLY_PR_BASE:-main}"
title="nix: bump the nightly pin to $tag"
body="$(cat <<EOF
The nightly release's rung 1 is compiled by the nightly pinned in
\`nix/nightly.nix\`. This PR adopts \`$tag\`, the newest published nightly, for
every platform the pin names -- tag, URL and the published SRI checksum.

Opened and refreshed by \`.github/workflows/bump-nightly-pin.yml\`, which runs
\`scripts/bump-nightly-pin.sh\` on a schedule. Checks: \`scripts/check-nightly-pin.sh\`
(hermetic fixtures; also run by CI's compiler job).

A pin older than the compiler-source surface fails every nightly at rung 1
with the host's own unknown-construct error, so this bump should not sit.
EOF
)"

if git diff --quiet -- nix/nightly.nix; then
  echo "open-nightly-pin-pr: nix/nightly.nix has no changes; nothing to do" >&2
  exit 0
fi

# The loop prevention depends on this PR being PIN-ONLY: nightly.yml ignores a
# push whose only changed file is nix/nightly.nix, so merging it publishes no
# new nightly for the next scheduled bump to adopt. Refuse to widen the diff.
unexpected="$(git status --porcelain | awk '{print $2}' | grep -v '^nix/nightly\.nix$' || true)"
if [ -n "$unexpected" ]; then
  echo "open-nightly-pin-pr: the bump PR must touch only nix/nightly.nix; also changed:" >&2
  printf '  %s\n' "$unexpected" >&2
  exit 1
fi

git config user.name "github-actions[bot]"
git config user.email "41898282+github-actions[bot]@users.noreply.github.com"

# Bring the existing automation branch (if any) into the local clone so
# --force-with-lease compares against the real remote tip rather than
# refusing on a stale or missing lease.
git fetch origin "+refs/heads/$branch:refs/remotes/origin/$branch" 2>/dev/null || true

git checkout -B "$branch"
git add nix/nightly.nix
git commit -m "$title"
git push --force-with-lease origin "$branch"

state="$(gh pr view "$branch" --json state --jq .state 2>/dev/null || true)"
if [ "$state" = OPEN ]; then
  gh pr comment "$branch" --body "Re-pushed for \`$tag\` at $(git rev-parse --short HEAD); the previous head is superseded."
  gh pr view "$branch" --json url --jq .url
else
  gh pr create --base "$base" --head "$branch" --title "$title" --body "$body"
fi
