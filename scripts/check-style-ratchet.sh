#!/usr/bin/env bash
# The style/name-path ratchet, in the commit path.
#
# CI enforces it as `compiler-checks`' "Style metrics ratchet" step: no
# counter in `scripts/style-baseline.txt` may rise. Nothing ran it locally,
# which is how a branch that added 15 wide positional patterns and 5
# unneeded `#[partial]` attributes reached CI green and went red there --
# a gate that only fires twenty minutes after the commit is a gate the
# author reads instead of a gate that stops them.
#
# WHOLE CORPUS, not the touched files. The counters are corpus-wide totals
# (one file's +1 is only visible against the total), so a per-file mode
# cannot answer the question the baseline asks. The cost is the reason a
# per-file mode is not missed: measured 2026-11-16, the whole sweep is
# ~15s warm, which is cheap enough to pay on every commit and is what
# makes the ratchet a real gate rather than a CI-only one.
#
#   scripts/check-style-ratchet.sh          # the ratchet against the baseline
#   scripts/style-metrics.sh                # the counters + summary, ungated
#   scripts/style-metrics.sh --detail       # + per-file / per-scrutinee breakdown
#
# A developer who raises a counter on purpose regenerates the baseline with
# `scripts/style-metrics.sh --write-baseline scripts/style-baseline.txt` and
# commits it -- the same thing CI's step comments say.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

baseline="$root/scripts/style-baseline.txt"
if [ ! -f "$baseline" ]; then
  echo "check-style-ratchet.sh: missing $baseline" >&2
  exit 1
fi

# The counters go to stdout and the human summary and the failure report to
# stderr. A hook wants the failure report and nothing else -- 37 lines of
# counters on every commit is noise -- so stdout is dropped and stderr is
# kept. `set -o pipefail` is irrelevant here (nothing is piped), and the
# process's own exit status survives the redirection: 1 is the ratchet's "a
# counter rose", which prek turns into a failed hook.
exec python3 "$root/scripts/style_metrics.py" --root "$root" \
    --baseline "$baseline" --quiet >/dev/null
