#!/bin/sh
# Golden-IR oracle for changes to the self-hosted codegen front end.
#   scripts/golden-ir.sh snapshot <dir>   build the fixed corpus, keep each .ll in <dir>
#   scripts/golden-ir.sh diff <dir>       rebuild into a scratch dir, diff against <dir>
# Builds run with MONAD_ELAB_STATS=1, so each <name>.log also carries the
# `elab_stats:` lines (see lang/src/codegen/validate.mo, report_elab_stats).
# The IR embeds the checkout's absolute path: compare within one worktree.
set -u
mode=${1:?usage: golden-ir.sh snapshot|diff <dir>}
dir=${2:?usage: golden-ir.sh snapshot|diff <dir>}
bin=${MONAD_BIN:-rust/target/release/monad-rs}
files="examples/hello.mo examples/factorial.mo examples/do_block.mo examples/raw_strings.mo
examples/structs.mo examples/located_terms.mo examples/sha256.mo examples/json.mo examples/toml.mo"

case $mode in
  snapshot) out=$dir ;;
  diff) out=$(mktemp -d) ;;
  *) echo "unknown mode $mode" >&2; exit 2 ;;
esac
mkdir -p "$out"

for f in $files; do
  n=$(basename "$f" .mo)
  MONAD_ELAB_STATS=1 "$bin" run cli/src/main.mo build "$f" --no-cache -o "$out/$n" > "$out/$n.log" 2>&1 \
    || echo "build failed: $f (see $out/$n.log)"
  rm -f "$out/$n" "$out/$n.o" "$out/${n}_runtime.o"
done

[ "$mode" = snapshot ] && exit 0
status=0
for f in $files; do
  n=$(basename "$f" .mo)
  if cmp -s "$dir/$n.ll" "$out/$n.ll"; then echo "same  $n"; else echo "DIFF  $n"; status=1; fi
done
echo "scratch: $out"
exit $status
