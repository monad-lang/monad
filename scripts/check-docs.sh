#!/usr/bin/env bash
# Type-check every Monad code block in the mdBook under docs/.
#
# `mdbook build` only renders markdown -- it never compiles the code inside
# the chapters, which is how the book drifted far enough from the compiler
# that most of its samples stopped parsing. This script closes that gap.
#
# A fenced block tagged ```monad is extracted to its own .mo file and run
# through `check`. A block tagged ```monad,ignore is skipped: that tag is
# for samples that are deliberately not valid today -- syntax the docs
# describe as unimplemented, or fragments shown for illustration -- and
# every one of them should have prose next to it saying so.
#
# Blocks are checked in isolation, so each ```monad block must stand on its
# own: its own `use`/`open` lines, its own type annotations. That is a
# feature, not a limitation -- a reader copying one block into a file gets
# exactly what the checker saw.
#
# Two modes. The default uses the Rust bootstrap host, which is fast and is
# what the pre-commit hook runs:
#
#   scripts/check-docs.sh
#
# The book documents the SELF-HOSTED compiler, though, so the stricter check is
# to point MONAD_BIN at a bootstrapped `monad` binary:
#
#   MONAD_BIN=/path/to/monad scripts/check-docs.sh
#
# Both binaries take the same `check <paths>...` shape and the same exit codes,
# so no other change is needed. The self-hosted run may still report a failure or
# two: blocks demonstrating the remaining host-only constructs -- `#[derive]`,
# a `\u{...}` escape, a dotted instance name, or a call relying on a brace
# parameter's default. Every one of those carries a "Bootstrap host only" note in
# the prose beside it, and the full list is in docs/src/bootstrap-host.md. A
# failure without such a note is a real problem.
#
# The reverse also exists, which is why a few blocks are tagged
# ```monad,ignore even though they are correct: a multiplicity prefix on a
# destructured parameter parses self-hosted and is a parse error on the host.
#
# Module resolution is relative to the working directory, so this must run
# from the repository root (it cd's there itself).

set -euo pipefail

cd "$(dirname "$0")/.."

# Overridable so local runs can use an already-installed `monad-rs` instead
# of paying for a cargo rebuild: MONAD_BIN=monad-rs scripts/check-docs.sh
MONAD_BIN=${MONAD_BIN:-"cargo run --release --quiet --"}

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

total=0
skipped=0
declare -a blocks=()
declare -a origins=()

for md in docs/src/*.md; do
  # Resolved BEFORE the loop, not inside it: a `$(basename "$md" ...)` in the
  # body of a `while ... done < "$md"` reads as writing the file it redirects
  # from (shellcheck SC2094), which it isn't.
  stem=$(basename "$md" .md)
  # State machine over the file: `fence` holds the info string of the block
  # we're inside ("" when outside one), `start` its opening line number.
  fence=""
  start=0
  buf=""
  lineno=0
  while IFS= read -r line || [ -n "$line" ]; do
    lineno=$((lineno + 1))
    if [ -z "$fence" ]; then
      case "$line" in
        '```'*)
          fence=${line#'```'}
          start=$lineno
          buf=""
          ;;
      esac
      continue
    fi
    if [ "$line" = '```' ]; then
      case "$fence" in
        monad)
          total=$((total + 1))
          f="$work/${stem}_$start.mo"
          printf '%s' "$buf" > "$f"
          blocks+=("$f")
          origins+=("$md:$start")
          ;;
        monad,ignore)
          skipped=$((skipped + 1))
          ;;
      esac
      fence=""
      continue
    fi
    buf+="$line"$'\n'
  done < "$md"
done

if [ "$total" -eq 0 ]; then
  echo "check-docs: no \`\`\`monad blocks found under docs/src -- is the tag right?" >&2
  exit 1
fi

echo "check-docs: checking $total block(s), skipping $skipped tagged \`monad,ignore\`"

# One `check` invocation over every block: it reports per-file diagnostics
# already, and paying the module-loading cost once instead of N times takes
# this from minutes to seconds.
if out=$($MONAD_BIN check "${blocks[@]}" 2>&1); then
  echo "$out" | tail -1
  echo "check-docs: OK"
  exit 0
fi

echo "$out"
echo
echo "check-docs: FAILED -- the block(s) above came from:" >&2
for i in "${!blocks[@]}"; do
  echo "  $(basename "${blocks[$i]}")  <-  ${origins[$i]}" >&2
done
exit 1
