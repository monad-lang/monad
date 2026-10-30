#!/usr/bin/env bash
# Does a mote in its OWN repository build with the compiler alone?
#
# Every other check in this repo runs from the repository root, where the
# stdlib is `init/src` and `std/src` beside the working directory and the C
# runtime is at `runtime/src/runtime.c` -- all three resolved by CWD-relative
# literals. That is exactly the environment an external mote does not have,
# and it is why this whole class of bug survived: nothing in the repo ever
# ran the CLI from a directory that was not the checkout. The Forge game
# engine, built as a sibling repository, found five such gaps at once.
#
# So this script builds a mote in a temporary directory *outside* the
# checkout and runs the compiled self-hosted binary from inside it, in the
# seven configurations an external user can be in:
#
#   1. declared path dependencies, explicit path -- `monad check src/lib.mo`.
#      The filed repro: everything resolves except `runtime.c`, which had no
#      manifest fallback at all, so `test`/`compile` died at the link stage.
#   2. the same repository, invoked bare -- `cd repo && monad check`, which
#      sets the mote's own directory to `"."` and turns every absolute
#      `[dependencies.X] path` into `"./<abs>"` through a naive join.
#   3. NO path dependencies, an installed toolchain -- `MONAD_ROOT=<root>`,
#      where the root holds `init/`, `std/`, `llvm/` and `runtime/` copied from
#      this checkout. Nothing is declared and nothing is relative: this is the
#      acceptance test for "a mote in its own repo compiles with a
#      monadup-installed toolchain".
#   4. NO path dependencies, the REAL monadup layout -- `MONAD_HOME=<home>`
#      with `active` naming a tag and the toolchain in `downloads/<tag>/`.
#      Configuration 3 only ever exercised `$MONAD_ROOT`, which is the
#      variable a test sets and not the one an install writes: everything a
#      real `monadup install` produces, `active` and the downloads directory
#      included, was covered by unit rows alone until this configuration.
#   5. Nothing at all -- no `$MONAD_ROOT`, no `$MONAD_HOME`, no installed
#      toolchain. This is a first-time user's machine, and what it asserts is
#      that the two things they meet are LEGIBLE: the `monad check` that
#      covers nothing says why and exits non-zero (rather than printing help
#      and exiting 0), and a check that cannot find the ambient motes names
#      `monadup`, `MONAD_ROOT` and `MONAD_HOME` instead of only reporting the
#      modules it could not resolve.
#   6. A real dependency that the manifest forgot to declare -- in both
#      layouts it can sit in. The hint has to name a `path` relative to the
#      MANIFEST, so `foo` and `../foo` are different answers to the same
#      error, and only one of them was right under the hardcoded `../<head>`
#      this replaced. Each layout ends by writing the hint's own path into the
#      manifest and asserting the check goes green.
#   7. A mote naming no target that exists -- no `src/lib.mo`, no
#      `src/main.mo`, and no `[lib]`/`[[bin]]` saying otherwise. Configuration
#      6 asserts the DECLARED-dependency gate; this asserts its sibling target
#      gate. It is also the one configuration with no `[workspace]` anywhere
#      above it: an external mote is a workspace of one, so the member half of
#      that gate has nothing to say and the loaded-module half is the only
#      thing that can report it. Ends by creating the file the error named.
#   8. A dependency whose library root is declared somewhere other than the
#      conventional `src/lib.mo` -- the manifest's `[lib] path` has to be what
#      a consumer's `use <dep>` resolves, and the error for an absent root has
#      to name the DECLARED path rather than the conventional one.
#   9. A bare `test`/`check` on a mote with a vendor tree -- `devenv shell`
#      leaves a `.devenv/` whose gettext catalogs are also `*.mo`. The no-path
#      forms cover a mote's DECLARED target roots; only an explicit path is
#      literal, and the second half of this configuration pins that as a
#      deliberate non-goal rather than an oversight.
#
# Configuration 3 also compiles and RUNS a binary, which is the only
# assertion that covers the C runtime end to end: the program prints through
# `println`, so a build that never found `runtime.c` cannot produce it.
# Configuration 4 does the same through the `MONAD_HOME` route, because the
# two routes reach the same root by different paths and only one of them was
# ever compiled against.
#
# Takes the compiled binary as its first argument (or `MONAD_BIN`). It must
# be the self-hosted compiler, not the Rust host: `monad-rs` resolves its own
# modules relative to the checkout and cannot be pointed at a foreign CWD.
#
# Run it directly (`scripts/check-external-mote.sh <binary>`); it needs
# `llc`, `clang` and the Boehm GC headers, i.e. the dev shell.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
monad="${1:-${MONAD_BIN:-}}"
[ -n "$monad" ] || { echo "usage: scripts/check-external-mote.sh <path-to-compiled-monad>" >&2; exit 2; }
monad="$(cd -- "$(dirname -- "$monad")" && pwd)/$(basename -- "$monad")"
[ -x "$monad" ] || { echo "check-external-mote: '${monad}' is not executable" >&2; exit 2; }

# PID in the name (plus `mktemp -d`), so parallel runs on one machine never
# share a directory.
work="$(mktemp -d "${TMPDIR:-/tmp}/monad-external-mote.$$.XXXXXX")"
trap 'rm -rf "$work"' EXIT

ok() { echo "ok   - $*"; }
die() { echo "FAIL - $*" >&2; exit 1; }

# ---------------------------------------------------------------------------
# The fixture: a mote with a library, a binary and one test
# ---------------------------------------------------------------------------
#
# The library goes through `std::path` on purpose. `Path` is std's own code,
# so a build that silently resolved std from somewhere stale -- or failed to
# resolve it and carried on -- does not reproduce the answer below. `main`
# prints, which forces the C runtime into the link.

mkdir -p "$work/src"

cat > "$work/src/lib.mo" <<'MONAD'
// The library half of the external-mote fixture. `std::path` is reached by
// name (no path dependency in configuration 3), and the answer is a
// two-segment join, so a std that resolved from anywhere plausible still has
// to produce the right string.

use std::path {Path}

def join2 (a : String) (b : String) : String :=
    match Path.of a {
        err _ => a,
        ok p => match Path.of b {
            err _ => b,
            ok q => Path.to_string (Path.join p q),
        },
    }

def data_dir (root : String) : String := join2 root "data"

#[test]
def test_data_dir : Bool := String.beq (data_dir "/var/lib/game") "/var/lib/game/data"
MONAD

cat > "$work/src/main.mo" <<'MONAD'
// The binary half. It prints, so the C runtime is in the link, and it calls
// into the library, so the mote's own `lib::` self-resolution is exercised
// too.

use init::io {IO}
open IO {println}
use lib::lib {data_dir}

def main (args : List String) : IO Unit := println (data_dir "/var/lib/game")
MONAD

write_manifest() {
  local dir="$1" deps="$2"
  mkdir -p "$dir/src"
  cp "$work/src/lib.mo" "$work/src/main.mo" "$dir/src/"
  {
    cat <<'TOML'
# The external-mote fixture. Its own repository, its own manifest, no
# compiler checkout anywhere above it.

[mote]
name = "game"
version = "0.1.0"
edition = "2026"

[lib]
path = "src/lib.mo"

[[bin]]
name = "game"
path = "src/main.mo"
TOML
    # Configuration 3 declares nothing: the toolchain root is what supplies
    # init/std/runtime, and a dependency entry would hide the fact that it
    # did not have to.
    [ "$deps" = no ] || cat <<TOML

[dependencies.init]
path = "${root}/init"

[dependencies.std]
path = "${root}/std"

[dependencies.runtime]
path = "${root}/runtime"
TOML
  } > "$dir/mote.toml"
}

# `nested/` rather than the top of the temp dir: `find_workspace_root` walks
# UP from the working directory looking for a `[workspace]` manifest, so the
# fixture's own directory tree must not contain one by accident.
withdeps="$work/nested/withdeps"
nodeps="$work/nested/nodeps"
write_manifest "$withdeps" yes
write_manifest "$nodeps" no

# The installed toolchain, laid out exactly as `monadup` leaves it: the four
# motes the sources tarball ships plus the generated workspace manifest
# (`scripts/stage-mote-sources.sh`). `llvm` is not optional here for the same
# reason it is in that list -- `runtime`'s natives are LLVM IR, so a root
# without `llvm/` is a root where `compile` cannot resolve `llvm::ir`. Copying
# the four by hand rather than running the stager keeps this fixture
# independent of the tarball's own packaging, which `check-monadup.sh` covers.
toolchain="$work/nested/toolchain"
mkdir -p "$toolchain"
for m in init std llvm runtime; do
  cp -R "$root/$m" "$toolchain/$m"
done
cat > "$toolchain/mote.toml" <<'TOML'
[workspace]
members = ["init", "std", "llvm", "runtime"]
TOML

# ---------------------------------------------------------------------------
# 1. Declared path dependencies, explicit path
# ---------------------------------------------------------------------------

cd "$withdeps"

check_log="$work/check1.log"
"$monad" check src/lib.mo > "$check_log" 2>&1 \
  || { cat "$check_log" >&2; die "config 1: 'monad check src/lib.mo' failed outside a checkout"; }
if grep -qE '^FAIL' "$check_log"; then
  die "config 1: check reported a FAIL line"
fi
ok "config 1: check resolves declared path deps from a foreign directory"

test_log="$work/test1.log"
"$monad" test src/lib.mo > "$test_log" 2>&1 \
  || { cat "$test_log" >&2; die "config 1: 'monad test src/lib.mo' failed outside a checkout"; }
grep -q "1/1 total tests passed" "$test_log" \
  || { cat "$test_log" >&2; die "config 1: the test did not run and pass"; }
ok "config 1: test compiles, links against the declared runtime and runs the test"

# The same in the strongest form: a real binary, linked against the C
# runtime found through `[dependencies.runtime]`, executed.
"$monad" build src/main.mo -o "$work/out1" > "$work/compile1.log" 2>&1 \
  || { cat "$work/compile1.log" >&2; die "config 1: compile failed on the C runtime"; }
[ "$("$work/out1")" = "/var/lib/game/data" ] \
  || die "config 1: the compiled binary printed the wrong thing"
ok "config 1: compile produces a working binary"

# ---------------------------------------------------------------------------
# 2. The same repository, invoked bare
# ---------------------------------------------------------------------------

# Bare, the mote's own directory is `"."`, so every declared absolute path
# dep is joined onto it -- which is where a naive `raw_path_join` produced
# `".//home/.../init"` and every dependency silently vanished.
bare_check="$work/check2.log"
"$monad" check > "$bare_check" 2>&1 \
  || { cat "$bare_check" >&2; die "config 2: bare 'monad check' failed on absolute path deps"; }
if grep -qE '^FAIL' "$bare_check"; then
  die "config 2: bare check reported a FAIL line"
fi
ok "config 2: bare check resolves absolute path deps"

bare_test="$work/test2.log"
"$monad" test > "$bare_test" 2>&1 \
  || { cat "$bare_test" >&2; die "config 2: bare 'monad test' failed on absolute path deps"; }
grep -q "1/1 total tests passed" "$bare_test" \
  || { cat "$bare_test" >&2; die "config 2: the bare test run did not run and pass"; }
ok "config 2: bare test runs the mote's tests"

# ---------------------------------------------------------------------------
# 3. No path dependencies, an installed toolchain
# ---------------------------------------------------------------------------

cd "$nodeps"

# The manifest really is empty of deps -- otherwise this configuration would
# be passing for the wrong reason.
if grep -q 'dependencies' mote.toml; then
  die "config 3: the fixture declares dependencies after all"
fi

root_check="$work/check3.log"
MONAD_ROOT="$toolchain" "$monad" check > "$root_check" 2>&1 \
  || { cat "$root_check" >&2; die "config 3: 'monad check' did not resolve init/std from the toolchain root"; }
if grep -qE '^FAIL' "$root_check"; then
  die "config 3: check reported a FAIL line"
fi
ok "config 3: check resolves init/std from \$MONAD_ROOT with no declared deps"

root_test="$work/test3.log"
MONAD_ROOT="$toolchain" "$monad" test > "$root_test" 2>&1 \
  || { cat "$root_test" >&2; die "config 3: 'monad test' did not resolve the toolchain root"; }
grep -q "1/1 total tests passed" "$root_test" \
  || { cat "$root_test" >&2; die "config 3: the test did not run and pass"; }
ok "config 3: test resolves init/std/runtime from \$MONAD_ROOT"

# The acceptance test for the whole feature: nothing declared, nothing
# relative, and a program that runs.
MONAD_ROOT="$toolchain" "$monad" build src/main.mo -o "$work/out3" > "$work/compile3.log" 2>&1 \
  || { cat "$work/compile3.log" >&2; die "config 3: compile did not find runtime.c in the toolchain root"; }
[ "$("$work/out3")" = "/var/lib/game/data" ] \
  || die "config 3: the compiled binary printed the wrong thing"
ok "config 3: compile links the toolchain's runtime and the binary runs"

# ---------------------------------------------------------------------------
# 4. No path dependencies, the real monadup layout ($MONAD_HOME + active)
# ---------------------------------------------------------------------------

# What `monadup install` actually writes: `$MONAD_HOME/active` holding a tag,
# and that tag's directory under `$MONAD_HOME/downloads/` holding the binary
# and the unpacked mote sources. Configuration 3 sets `$MONAD_ROOT` directly,
# which is the one root a test can install with a shell variable -- so
# `active`, the tag lookup and the downloads directory were exercised by unit
# rows in lang/src/mote.mo and by nothing end to end.
home="$work/nested/home"
tag="nightly-FIXTURE"
mkdir -p "$home/downloads/$tag"
cp -R "$toolchain/." "$home/downloads/$tag/"
printf '%s\n' "$tag" > "$home/active"

# From inside the fixture's own repository, which is the state a user is in
# after `monadup install`: the install is elsewhere, on `$MONAD_HOME` alone.
#
# Both cached verbs below run with the cache OFF, and that is what they are
# for rather than a precaution. Configurations 3 and 4 build the SAME
# fixture, from the SAME directory, through two toolchain roots that are
# `cp -R` copies of each other -- differing only in which variable names the
# root. That is not an input to a key, and should not be: identical bytes
# are identical work. So the two configurations key identically and the
# second replays the first. Measured, one shared store: config 3's `check`
# writes two entries and config 4's `check` adds none, because it is reading
# those two. What config 4 exists to establish is that the `$MONAD_HOME` +
# `active` route RESOLVES, and a replay resolves nothing -- a gate leaning
# on the cache is a gate that goes quiet when the cache gets correct.
#
# `MONAD_NO_CACHE=1` is off in both directions (nothing read, nothing
# written), so what runs here is the resolution it claims to be. Config 3
# keeps the cache on deliberately: it is the configuration whose entries are
# being shared, and it is the one that has to miss for the sharing to be
# observable at all. The build below was masked by a separate defect until
# now -- a mote whose manifest sits in the working directory keyed on an
# empty root, which the shell could not `cd` into, so the builder silently
# disabled its own cache and config 4 compiled for real. Fixing that is what
# makes this line load-bearing.
#
# And "load-bearing" is measured rather than argued: with the root fix in,
# one shared store gives config 3 a missing build (one key) and config 4 a
# `cached:' hit with no key of its own, for byte-identical binaries -- which
# is precisely the replay this hatch exists to refuse, since config 4 is
# here to show that its OWN root resolves. The two REAL compiles are not
# byte-identical either, and the difference is the sharper reason: 12
# `!DIFile' lines, because a module resolved through an absolute toolchain
# root carries that root's path into the IR (`llvm_split_path',
# llvm/src/ir.mo:979, takes a module's path verbatim). Without the hatch,
# `out4' would be config 3's artifact down to the toolchain path in its
# debug info.
monad_home_check="$work/check4.log"
MONAD_NO_CACHE=1 MONAD_HOME="$home" "$monad" check > "$monad_home_check" 2>&1 \
  || { cat "$monad_home_check" >&2; die "config 4: 'monad check' did not resolve the \$MONAD_HOME toolchain"; }
if grep -qE '^FAIL' "$monad_home_check"; then
  die "config 4: check reported a FAIL line"
fi
ok "config 4: check resolves init/std from \$MONAD_HOME + active"

monad_home_test="$work/test4.log"
MONAD_HOME="$home" "$monad" test > "$monad_home_test" 2>&1 \
  || { cat "$monad_home_test" >&2; die "config 4: 'monad test' did not resolve the \$MONAD_HOME toolchain"; }
grep -q "1/1 total tests passed" "$monad_home_test" \
  || { cat "$monad_home_test" >&2; die "config 4: the test did not run and pass"; }
ok "config 4: test resolves init/std/runtime from \$MONAD_HOME + active"

MONAD_NO_CACHE=1 MONAD_HOME="$home" "$monad" build src/main.mo -o "$work/out4" > "$work/compile4.log" 2>&1 \
  || { cat "$work/compile4.log" >&2; die "config 4: compile did not find runtime.c through \$MONAD_HOME"; }
[ "$("$work/out4")" = "/var/lib/game/data" ] \
  || die "config 4: the compiled binary printed the wrong thing"
ok "config 4: compile links the toolchain's runtime and the binary runs"

# ---------------------------------------------------------------------------
# 5. Nothing installed: what a first-time user meets
# ---------------------------------------------------------------------------

# Deliberately no `$MONAD_ROOT` AND a `$MONAD_HOME` that does not exist, so
# a developer's own `~/.monad` cannot answer this: the state under test is
# "this machine has no monad toolchain", not "this shell happens to be
# missing a variable". `MONAD_ROOT=''` is spelled empty for the same reason --
# the compiler treats empty as unset, and saying so removes the doubt.
fresh() { MONAD_ROOT='' MONAD_HOME="$work/nested/no-such-home" "$@"; }

# (a) A bare `monad check` in a directory with no mote above it. It has
# nothing to check, and the two things it must NOT do are the two it used to:
# print a screen of usage, and exit 0. A check command that exits 0 on a
# directory with no mote reads as a pass on a mote that does not exist yet.
mkdir -p "$work/nested/plain"
cd "$work/nested/plain"
bare_rc=0
fresh "$monad" check > "$work/bare5.log" 2>&1 || bare_rc=$?
[ "$bare_rc" -ne 0 ] \
  || { cat "$work/bare5.log" >&2; die "config 5: a bare 'monad check' outside any mote exited 0"; }
grep -q "no mote.toml above this directory" "$work/bare5.log" \
  || { cat "$work/bare5.log" >&2; die "config 5: the bare check did not say there was no mote to check"; }
if grep -q "Usage: monad build" "$work/bare5.log"; then
  die "config 5: the bare check printed the usage screen instead of the reason"
fi
ok "config 5: a bare check outside any mote says why and exits $bare_rc"

# (b) A real file, and no toolchain to resolve its ambient modules from. The
# compiler cannot invent `init`/`std` here, so this run fails -- what is
# asserted is that it fails with a way out in it. Without this, the failure
# is `unresolved module: prelude` plus a wall of `unknown variable 'Path'`,
# which names neither the variable to set nor the tool that sets it.
cd "$nodeps"
hint_rc=0
fresh "$monad" check src/lib.mo > "$work/no-root5.log" 2>&1 || hint_rc=$?
[ "$hint_rc" -ne 0 ] \
  || { cat "$work/no-root5.log" >&2; die "config 5: a check that resolved no ambient module exited 0"; }
for want in monadup MONAD_ROOT MONAD_HOME; do
  grep -q "$want" "$work/no-root5.log" \
    || { cat "$work/no-root5.log" >&2; die "config 5: the no-toolchain failure does not mention $want"; }
done
ok "config 5: a check with no toolchain fails, and names the install and the two variables"

# ---------------------------------------------------------------------------
# 6. An undeclared dependency: the hint names a path that is actually right
# ---------------------------------------------------------------------------

# `use foo::lib` on a mote that no manifest declares is the one error an
# external user is most likely to hit and the one they cannot debug: the
# `unknown variable` it trails into names nothing about a manifest. The hint
# is the whole value of the error, and it has to give a `path` relative to
# the MANIFEST -- so the same layout question that decides where a mote is
# found decides whether the answer is `foo` or `../foo`.
#
# Both layouts are driven, because both are real and only one of them was
# right under the old hardcoded `../<head>`: a dependency beside the working
# directory (value `foo`) and one beside the manifest's own directory, the
# sibling convention this repo's own manifests use (value `../foo`). Each
# ends with the hint's path actually written into the manifest and the check
# going green -- a hint that names a path which does not fix the build is
# worse than no hint, so the fix is asserted rather than the wording alone.
#
# No `[dependencies.foo]` entry in either manifest: that absence IS this
# configuration. The toolchain root is present so the failure under test is
# the undeclared mote rather than a missing stdlib.

undeclared="$work/nested/undeclared"

write_undeclared() {
  local mote_dir="$1" dep_dir="$2"
  mkdir -p "$mote_dir/src" "$dep_dir/src"
  cat > "$mote_dir/mote.toml" <<'TOML'
[mote]
name = "game"
version = "0.1.0"
edition = "2026"

[lib]
path = "src/lib.mo"
TOML
  cat > "$dep_dir/mote.toml" <<'TOML'
[mote]
name = "foo"
version = "0.1.0"
edition = "2026"

[lib]
path = "src/lib.mo"
TOML
  cat > "$dep_dir/src/lib.mo" <<'MONAD'
pub def answer : I64 := 42
MONAD
  cat > "$mote_dir/src/lib.mo" <<'MONAD'
// The undeclared dependency. `foo` is a real mote sitting next to this one,
// so the head names a mote rather than a plain module -- which is what puts
// the declaration hint in the error instead of a bare `unresolved module`.
use foo::lib {answer}

def main : I64 := answer
MONAD
}

# (a) Flat: the dependency is beside the working directory, and the check is
# bare, so the manifest's `m.dir` is `.` and the value a manifest needs is
# the plain name.
write_undeclared "$undeclared/flat" "$undeclared/flat/foo"
cd "$undeclared/flat"
flat_rc=0
MONAD_ROOT="$toolchain" "$monad" check > "$work/undeclared-flat.log" 2>&1 || flat_rc=$?
[ "$flat_rc" -ne 0 ] \
  || { cat "$work/undeclared-flat.log" >&2; die "config 6: an undeclared mote was not reported"; }
grep -q 'path = "foo"' "$work/undeclared-flat.log" \
  || { cat "$work/undeclared-flat.log" >&2; die "config 6: the hint did not name path = \"foo\" for a dependency beside the working directory"; }
if grep -q 'path = "../foo"' "$work/undeclared-flat.log"; then
  cat "$work/undeclared-flat.log" >&2
  die "config 6: the hint named ../foo for a dependency that is beside the working directory"
fi
ok "config 6: an undeclared dependency beside the working directory is hinted as path = \"foo\""

# ...and the hint fixes it, which is the only claim worth making.
printf '\n[dependencies.foo]\npath = "foo"\n' >> "$undeclared/flat/mote.toml"
MONAD_ROOT="$toolchain" "$monad" check > "$work/undeclared-flat-fixed.log" 2>&1 \
  || { cat "$work/undeclared-flat-fixed.log" >&2; die "config 6: the flat hint's path did not fix the check"; }
ok "config 6: the flat hint's path, written into the manifest, makes the check pass"

# (b) Sibling: the dependency is one level up from the mote, so the manifest
# value is `../foo`. This is the layout whose hint needs the `../` probe --
# without it nothing is found, and the error falls back to the unnamed
# `unresolved module` with no hint at all.
write_undeclared "$undeclared/nest/greet" "$undeclared/nest/foo"
cd "$undeclared/nest/greet"
sib_rc=0
MONAD_ROOT="$toolchain" "$monad" check > "$work/undeclared-sibling.log" 2>&1 || sib_rc=$?
[ "$sib_rc" -ne 0 ] \
  || { cat "$work/undeclared-sibling.log" >&2; die "config 6: an undeclared sibling mote was not reported"; }
grep -q 'path = "../foo"' "$work/undeclared-sibling.log" \
  || { cat "$work/undeclared-sibling.log" >&2; die "config 6: the hint did not name path = \"../foo\" for a sibling mote"; }
ok "config 6: an undeclared sibling dependency is hinted as path = \"../foo\""

printf '\n[dependencies.foo]\npath = "../foo"\n' >> "$undeclared/nest/greet/mote.toml"
MONAD_ROOT="$toolchain" "$monad" check > "$work/undeclared-sibling-fixed.log" 2>&1 \
  || { cat "$work/undeclared-sibling-fixed.log" >&2; die "config 6: the sibling hint's path did not fix the check"; }
ok "config 6: the sibling hint's path, written into the manifest, makes the check pass"

# ---------------------------------------------------------------------------
# 7. A mote that names no target at all
# ---------------------------------------------------------------------------
#
# The gate that arrived with the `[lib]`/`[[bin]]` defaults. Both target tables
# default -- `src/lib.mo` for a library, `src/main.mo` for a binary -- so a mote
# never has to write either one, and the gate is what keeps the defaults from
# becoming an invention: the paths are recorded whether or not the files are
# there, and this mote has neither.

targetless="$work/nested/targetless"
mkdir -p "$targetless/src"
cat > "$targetless/src/probe.mo" <<'MONAD'
// Nothing but a file for the load to have something to do with. The mote
// around it has no target, which is the whole point.
def answer : I64 := 42
MONAD
cat > "$targetless/mote.toml" <<TOML
[mote]
name = "targetless"
version = "0.1.0"
edition = "2026"

[dependencies.init]
path = "${root}/init"

[dependencies.std]
path = "${root}/std"

[dependencies.runtime]
path = "${root}/runtime"
TOML

cd "$targetless"
tgt_rc=0
MONAD_ROOT="$toolchain" "$monad" check > "$work/targetless.log" 2>&1 || tgt_rc=$?
[ "$tgt_rc" -ne 0 ] \
  || { cat "$work/targetless.log" >&2; die "config 7: a mote with no target at all was not reported"; }
grep -q 'has no target that exists' "$work/targetless.log" \
  || { cat "$work/targetless.log" >&2; die "config 7: the failure was not the target gate's"; }
# Which paths were tried depends on the manifest, so the error names them --
# and both defaults have to be in that list, or the reader cannot tell what
# the gate looked for.
grep -q 'src/lib.mo' "$work/targetless.log" \
  || { cat "$work/targetless.log" >&2; die "config 7: the error did not name the default library root"; }
grep -q 'src/main.mo' "$work/targetless.log" \
  || { cat "$work/targetless.log" >&2; die "config 7: the error did not name the default binary target"; }
# A gate that cannot be satisfied is worse than none: the file the error
# named has to be the fix.
printf 'pub def answer : I64 := 42\n' > "$targetless/src/lib.mo"
MONAD_ROOT="$toolchain" "$monad" check > "$work/targetless-fixed.log" 2>&1 \
  || { cat "$work/targetless-fixed.log" >&2; die "config 7: creating the library root the error named did not make the check pass"; }
ok "config 7: a mote naming no target that exists is reported, naming both defaults, and creating one fixes it"

# ---------------------------------------------------------------------------
# 8. A library root somewhere other than `src/lib.mo`
# ---------------------------------------------------------------------------
#
# `[lib] path` is a DECLARATION, and this is the configuration that proves
# resolution follows it rather than assuming the convention. Nothing in the
# monad workspace can prove it: all nine `[lib]` declarations there restate
# the default, so a resolver that ignored the field entirely would pass every
# other check in this repository. The root here is `lib/main.mo` -- a
# different directory AND a different stem, so neither half of the convention
# can answer by accident.
#
# Two motes, because the declaration has two readers: the mote itself (a bare
# `use lib`, which rewrites to the mote's own name) and a CONSUMER naming it
# as a dependency, which has to read the DEPENDENCY's manifest rather than its
# own. The second is the half that needs the dependency's `mote.toml` opened;
# a resolver that only honoured its own manifest would pass the first and fail
# here.

declared="$work/nested/declared"
mkdir -p "$declared/lib" "$declared/src"
cat > "$declared/lib/main.mo" <<'MONAD'
// The library root, at the path the manifest declares and nowhere near
// `src/lib.mo`. `pub`, because a consumer imports it across a mote boundary.
pub def shelf_width (n : I64) : I64 := n * 3

#[test]
def test_shelf_width : Bool := I64.beq (shelf_width 4) 12
MONAD
cat > "$declared/src/main.mo" <<'MONAD'
// The binary half, reaching its own library through the `lib` alias. BARE
// `lib`, not `lib::main`: the alias rewrites to the mote's own name, so a
// one-segment `lib` means "this mote's library root" and lands on the
// DECLARED file, where `lib::main` would be two segments and resolve under
// `src/` like any other module.
use init::io {IO}
open IO {println}
use lib {shelf_width}

def main (args : List String) : IO Unit := println (I64.to_string (shelf_width 5))
MONAD
cat > "$declared/mote.toml" <<TOML
[mote]
name = "shelf"
version = "0.1.0"
edition = "2026"

[lib]
path = "lib/main.mo"

[[bin]]
name = "shelf"
path = "src/main.mo"

[dependencies.init]
path = "${root}/init"

[dependencies.std]
path = "${root}/std"

[dependencies.runtime]
path = "${root}/runtime"
TOML

cd "$declared"
MONAD_ROOT="$toolchain" "$monad" check > "$work/declared-check.log" 2>&1 \
  || { cat "$work/declared-check.log" >&2; die "config 8: a declared [lib] path was not resolved"; }
ok "config 8: check resolves a library root declared outside src/"

MONAD_ROOT="$toolchain" "$monad" test > "$work/declared-test.log" 2>&1 \
  || { cat "$work/declared-test.log" >&2; die "config 8: tests in a declared library root did not run"; }
grep -q 'test_shelf_width' "$work/declared-test.log" \
  || { cat "$work/declared-test.log" >&2; die "config 8: the declared root's own test was never discovered"; }
ok "config 8: test discovers the declared library root's tests"

MONAD_ROOT="$toolchain" "$monad" build src/main.mo -o "$work/out8" > "$work/declared-build.log" 2>&1 \
  || { cat "$work/declared-build.log" >&2; die "config 8: building through the lib alias failed"; }
# The binary's own output, not just a zero exit: `lib::main` had to resolve to
# the declared file for `shelf_width 5` to be 15 at all.
out8="$("$work/out8" || true)"
[ "$out8" = 15 ] \
  || { echo "got: $out8" >&2; die "config 8: the built binary did not print the declared root's answer"; }
ok "config 8: a bare \`use lib\` reaches the declared root and the binary runs"

# The CONSUMER half: a second mote naming `shelf` as a dependency. `use shelf`
# is one segment, so it means "that mote's library root" -- and only `shelf`'s
# own manifest says where that is.
consumer="$work/nested/consumer"
mkdir -p "$consumer/src"
cat > "$consumer/src/main.mo" <<'MONAD'
// Imports the dependency by its BARE name, which is the case that has to read
// the dependency's own `[lib] path`.
use init::io {IO}
open IO {println}
use shelf {shelf_width}

def main (args : List String) : IO Unit := println (I64.to_string (shelf_width 7))
MONAD
cat > "$consumer/mote.toml" <<TOML
[mote]
name = "consumer"
version = "0.1.0"
edition = "2026"

[[bin]]
name = "consumer"
path = "src/main.mo"

[dependencies.shelf]
path = "${declared}"

[dependencies.init]
path = "${root}/init"

[dependencies.std]
path = "${root}/std"

[dependencies.runtime]
path = "${root}/runtime"
TOML

cd "$consumer"
MONAD_ROOT="$toolchain" "$monad" check > "$work/consumer-check.log" 2>&1 \
  || { cat "$work/consumer-check.log" >&2; die "config 8: a dependency's declared [lib] path was not resolved"; }
ok "config 8: a consumer's \`use <dep>\` resolves the dependency's declared root"

# The negative, and the reason it belongs here: when the declared file is
# absent the gate must name the DECLARED path. An error naming `src/lib.mo`
# would send the reader to create a file resolution will never read.
missing="$work/nested/missing"
mkdir -p "$missing/src"
cat > "$missing/src/probe.mo" <<'MONAD'
def answer : I64 := 42
MONAD
cat > "$missing/mote.toml" <<TOML
[mote]
name = "missing"
version = "0.1.0"
edition = "2026"

[lib]
path = "lib/root.mo"

[dependencies.init]
path = "${root}/init"

[dependencies.std]
path = "${root}/std"

[dependencies.runtime]
path = "${root}/runtime"
TOML

cd "$missing"
miss_rc=0
MONAD_ROOT="$toolchain" "$monad" check > "$work/missing.log" 2>&1 || miss_rc=$?
[ "$miss_rc" -ne 0 ] \
  || { cat "$work/missing.log" >&2; die "config 8: a declared library root that is absent was not reported"; }
grep -q 'lib/root.mo' "$work/missing.log" \
  || { cat "$work/missing.log" >&2; die "config 8: the error did not name the DECLARED library root"; }
ok "config 8: an absent declared root is reported by its declared path"

# ---------------------------------------------------------------------------
# 9. Bare `test`/`check` covers a mote's DECLARED targets, not its subtree
# ---------------------------------------------------------------------------

# The filed symptom, reproduced as an external mote rather than as the
# todo-app: `devenv shell` materializes a `.devenv/` holding a nix-fetched
# `bash`, whose gettext locale catalogs carry the `.mo` extension too. A bare
# `monad test` used to walk the whole subtree, so 85 binary catalogs each
# reported a parse failure and buried the two real files.
#
# The rule is that the no-path forms resolve a mote's declared target roots
# (`[lib] path`, then each `[[bin]] path`); only an explicit path is literal.
# `plans/implementations/2026-10-04-monad-test-no-path-globs-unrelated-dot-mo-files.md`.
discovery="$work/nested/discovery"
mkdir -p "$discovery/src"
cat > "$discovery/src/lib.mo" <<'MONAD'
def answer : I64 := 42

#[test]
def test_answer : Bool := I64.beq answer 42
MONAD
cat > "$discovery/mote.toml" <<TOML
[mote]
name = "discovery"
version = "0.1.0"
edition = "2026"

[lib]
path = "src/lib.mo"

[dependencies.init]
path = "${root}/init"

[dependencies.std]
path = "${root}/std"

[dependencies.runtime]
path = "${root}/runtime"
TOML

# The vendor tree. Deliberately binary: a file that merely fails to contain
# tests would pass this configuration for the wrong reason.
catalog="$discovery/.devenv/bash-bash/share/locale/af/LC_MESSAGES"
mkdir -p "$catalog"
printf '\xde\x12\x04\x95\x00\x00\x00\x00\x02\x00\x00\x00\x1c\x00\x00\x00' > "$catalog/bash.mo"

cd "$discovery"
disc_log="$work/test9.log"
MONAD_ROOT="$toolchain" "$monad" test > "$disc_log" 2>&1 \
  || { cat "$disc_log" >&2; die "config 9: bare 'monad test' failed on a mote with a vendor tree"; }
grep -q "1/1 total tests passed" "$disc_log" \
  || { cat "$disc_log" >&2; die "config 9: the mote's own test did not run and pass"; }
if grep -q '\.devenv' "$disc_log"; then
  cat "$disc_log" >&2
  die "config 9: bare 'monad test' walked the vendor tree instead of the declared root"
fi
ok "config 9: bare test covers only the mote's declared target roots"

# The other half of the rule, pinned so it is not "fixed" by accident: an
# EXPLICIT path is literal. `monad test .` means that directory, so the
# vendor tree is walked and its catalog reported -- skipping dot-directories
# inside the walk is a deliberate non-goal, not an oversight.
literal_log="$work/test9-literal.log"
MONAD_ROOT="$toolchain" "$monad" test . > "$literal_log" 2>&1 || true
grep -q '\.devenv' "$literal_log" \
  || { cat "$literal_log" >&2; die "config 9: an explicit path stopped being literal"; }
ok "config 9: an explicit path is still literal (the vendor tree is walked)"

# ---------------------------------------------------------------------------
# 10. A two-member workspace: inherited path AND git dependencies
# ---------------------------------------------------------------------------
#
# `[workspace.dependencies]` at the root plus `workspace = true` in a member:
# the inherited path is ROOT-relative, and the inherited git source is located
# through ONE lock at the workspace root (not the member's own). `monad fetch`
# is handed the virtual root, which has no `[mote]`, so it must walk the
# members itself.
ws="$work/ws"
git_src="$work/git-src"
home10="$work/home10"
mkdir -p "$ws/libm/src" "$ws/app/src" "$git_src/gm/src" "$home10"

cat > "$git_src/gm/mote.toml" <<'TOML'
[mote]
name = "gm"
version = "0.1.0"
edition = "2026"

[lib]
path = "src/lib.mo"
TOML

cat > "$git_src/gm/src/lib.mo" <<'MONAD'
pub def gvalue : I64 := 7
MONAD

(
  cd "$git_src"
  git init -q
  git add -A
  git -c user.email=test@example.invalid -c user.name=test commit -qm "gm"
  git tag v1
) || die "config 10: could not create the git fixture"

cat > "$ws/mote.toml" <<TOML
[workspace]
members = ["app", "libm"]

[workspace.dependencies.libm]
path = "libm"

[workspace.dependencies.gm]
git = "file://$git_src"
tag = "v1"
subdir = "gm"
TOML

cat > "$ws/libm/mote.toml" <<'TOML'
[mote]
name = "libm"
version = "0.1.0"
edition = "2026"

[lib]
path = "src/lib.mo"
TOML

cat > "$ws/libm/src/lib.mo" <<'MONAD'
pub def value : I64 := 41
MONAD

cat > "$ws/app/mote.toml" <<'TOML'
[mote]
name = "app"
version = "0.1.0"
edition = "2026"

[lib]
path = "src/lib.mo"

[dependencies.libm]
workspace = true

[dependencies.gm]
workspace = true
TOML

cat > "$ws/app/src/lib.mo" <<'MONAD'
use libm::lib {value}
use gm::lib {gvalue}

#[test]
def test_inherited_edges : Bool := value + gvalue == 48
MONAD

fetch_log="$work/ws-fetch.log"
MONAD_ROOT="$toolchain" MONAD_HOME="$home10" "$monad" fetch "$ws" > "$fetch_log" 2>&1 \
  || { cat "$fetch_log" >&2; die "config 10: monad fetch at a virtual workspace root failed"; }
[ -f "$ws/mote.lock" ] || die "config 10: monad fetch did not write the workspace-root mote.lock"
[ ! -f "$ws/app/mote.lock" ] || die "config 10: monad fetch wrote a member-local mote.lock"
grep -q 'name = "gm"' "$ws/mote.lock" \
  || { cat "$ws/mote.lock" >&2; die "config 10: the root lock does not record the inherited git dependency"; }
ok "config 10: fetch at a virtual root writes one root lock naming the inherited git dep"

(
  cd "$ws/app"
  run_log="$work/test10.log"
  MONAD_ROOT="$toolchain" MONAD_HOME="$home10" "$monad" test > "$run_log" 2>&1 \
    || { cat "$run_log" >&2; die "config 10: a member inheriting path and git deps did not test"; }
  grep -q "1/1 total tests passed" "$run_log" \
    || { cat "$run_log" >&2; die "config 10: the inherited-edge test did not pass"; }
) || exit 1
ok "config 10: a member resolves root-relative path and locked git dependencies"

echo "check-external-mote: an external mote loads, checks, tests and compiles in all ten configurations"
