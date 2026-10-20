#!/usr/bin/env bash
# `monad install`: build a release binary and install it atomically to
# $MONAD_HOME/bin (default $HOME/.monad/bin). Runs the CLI with a
# temporary home, so neither the developer's ~/.monad nor the checkout is
# touched.
#
# Needs a SELF-HOSTED compiler (the Rust host has no install verb):
#   MONAD_BIN=target-monad/release/monad scripts/check-install.sh
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
monad="${MONAD_BIN:-$root/target-monad/release/monad}"
if [ ! -x "$monad" ]; then
  echo "error: no self-hosted compiler at $monad (set MONAD_BIN)" >&2
  exit 1
fi

work="$(mktemp -d "${TMPDIR:-/tmp}/monad_install_$$.XXXXXX")"
trap 'rm -rf "$work"' EXIT

cat > "$work/probe.mo" <<'EOF'
open IO {println}

def main : IO Unit := do {
    println "install-probe"
}
EOF

fail() { echo "FAIL: $*" >&2; exit 1; }

# 1. A source file with -o lands as a regular, executable file.
(
  cd "$root"
  MONAD_HOME="$work/home" "$monad" install "$work/probe.mo" -o probe --no-cache >/dev/null
)
dest="$work/home/bin/probe"
[ -x "$dest" ] || fail "install did not create an executable at $dest"
[ -L "$dest" ] && fail "install left a symlink at $dest"
[ "$("$dest")" = "install-probe" ] || fail "the installed binary does not run"

# 2. A pre-existing symlink is replaced, not written through.
echo dummy > "$work/home/bin/dummy-target"
rm -f "$dest"
ln -s "$work/home/bin/dummy-target" "$dest"
(
  cd "$root"
  MONAD_HOME="$work/home" "$monad" install "$work/probe.mo" -o probe --no-cache >/dev/null
)
[ -L "$dest" ] && fail "install followed the symlink instead of replacing it"
[ "$(cat "$work/home/bin/dummy-target")" = "dummy" ] || fail "install wrote through the symlink"
[ "$("$dest")" = "install-probe" ] || fail "the replaced binary does not run"

# 3. HOME supplies the default home when MONAD_HOME is unset.
(
  cd "$root"
  env -u MONAD_HOME HOME="$work/plain-home" "$monad" install "$work/probe.mo" -o p2 --no-cache >/dev/null
)
[ -x "$work/plain-home/.monad/bin/p2" ] || fail "HOME/.monad fallback did not install"

# 4. A source file without a name is refused before compiling.
if (
  cd "$root"
  MONAD_HOME="$work/home" "$monad" install "$work/probe.mo" --no-cache >/dev/null 2>&1
); then
  fail "install accepted a nameless source file"
fi

# 5. No MONAD_HOME and no HOME is a usage error.
if (
  cd "$root"
  env -u MONAD_HOME -u HOME "$monad" install "$work/probe.mo" -o p3 --no-cache >/dev/null 2>&1
); then
  fail "install accepted an environment with no home"
fi

echo "check-install: ok"
