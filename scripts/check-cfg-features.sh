#!/usr/bin/env bash
# The `not` off-switch, verified through the ENVIRONMENT channel.
#
# `lang/src/cfg_tests.mo` covers `CfgEnv.for_mote` directly (it takes the spec
# as an argument), and `lang/src/cfg_fixture_tests.mo` covers the manifest
# `default` half. Neither can cover the one thing that only a subprocess can:
# that `MONAD_FEATURES` from the process environment reaches the resolver at
# all, and that a `not` in it subtracts. An in-process test cannot change its
# own environment portably, and a test that could would poison every later
# test in the same binary.
#
# So: run one fixture twice, in two processes, and require different output.
#
#   scripts/check-cfg-features.sh            # uses the `monad` on PATH
#   MONAD_BIN=/path/to/monad scripts/check-cfg-features.sh
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
monad_bin="${MONAD_BIN:-monad}"
fixture="$root/fixtures/cfg/on/src/main.mo"

if [ ! -f "$fixture" ]; then
  echo "error: missing fixture $fixture" >&2
  exit 2
fi

if ! command -v "$monad_bin" >/dev/null 2>&1; then
  echo "error: no \`$monad_bin\` on PATH (set MONAD_BIN to a built compiler)" >&2
  exit 2
fi

fail=0

# The fixture's mote is `cfg_on` and its `[features] default = ["on"]`, so the
# `default` half prints `on` and the gated-out half prints `off`.
run_case() {
  local label="$1" spec="$2" want="$3"
  local got
  got="$(cd "$root" && MONAD_FEATURES="$spec" "$monad_bin" run fixtures/cfg/on/src/main.mo 2>/dev/null | tail -n1)"
  if [ "$got" = "$want" ]; then
    printf 'ok    %-34s -> %s\n' "$label" "$got"
  else
    printf 'FAIL  %-34s -> %s (wanted %s)\n' "$label" "$got" "$want"
    fail=1
  fi
}

run_case "default (manifest)"                  ""                    "on"
run_case "not cfg_on/default subtracts it"     "not cfg_on/default"  "off"
run_case "not cfg_on/on subtracts the feature" "not cfg_on/on"       "off"
run_case "an unrelated mote leaves it alone"   "not other/x"         "on"
run_case "a trailing \`not\` is ignored"        "not"                 "on"

if [ "$fail" -ne 0 ]; then
  echo
  echo "The \`not\` off-switch did not take effect. Either the compiler you ran" >&2
  echo "predates it, or \`MONAD_FEATURES\` is not being read -- check that" >&2
  echo "\`cfg_env_for_file\` (lang/src/module.mo) still calls \`IO.get_env\`." >&2
  exit 1
fi

echo
echo "cfg feature off-switch: ok"