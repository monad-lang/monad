#!/usr/bin/env bash
# Test the DISTRIBUTION half of a nightly: the sources asset, the bootstrap
# stub, and (when MONADUP_BIN is set) the monadup binary itself.
#
# The fixture is the reason MONADUP_API_URL exists: `curl file://` stands in
# for the GitHub releases API, so the whole fetch-install-use path runs
# offline against a release this script builds on the spot.
#
# Usage:
#   scripts/check-monadup.sh                 # stub + sources-asset checks
#   MONADUP_BIN=/path/to/monadup scripts/check-monadup.sh
#                                            # additionally drive the binary
#
# In binary mode the fixture also carries the real binary as its
# `monadup-<platform>` asset, so the stub's fetch-and-exec path and the
# binary's `upgrade` path both exercise a real executable.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
work="$(mktemp -d "${TMPDIR:-/tmp}/monadup-check.$$.XXXXXX")"
trap 'rm -rf "$work"' EXIT

ok() { echo "ok   - $*"; }
die() { echo "FAIL - $*" >&2; exit 1; }

tag="nightly-FIXTURE"

# ---------------------------------------------------------------------------
# 1. The sources asset, asserted from the artifact it produced
# ---------------------------------------------------------------------------

dist="$work/dist"
"$root/scripts/stage-mote-sources.sh" "$dist" x86_64-linux >/dev/null
asset="$dist/monad-src-x86_64-linux.tar.gz"
[ -f "$asset" ] || die "stage-mote-sources.sh wrote no $asset"

listing="$(tar -tzf "$asset")"
for want in init/mote.toml std/mote.toml llvm/mote.toml runtime/mote.toml \
            init/src/lib.mo std/src/lib.mo llvm/src/ir.mo runtime/src/runtime.c \
            mote.toml; do
  grep -qxF "$want" <<<"$listing" || die "sources asset is missing '$want'"
done
ok "sources asset carries the four motes' manifests, sources and runtime.c"

tar -xzOf "$asset" mote.toml | grep -qF 'members = ["init", "std", "llvm", "runtime"]' \
  || die "sources asset's root mote.toml does not declare the four motes as members"
ok "sources asset's root mote.toml is a workspace naming all four motes"

if grep -qE '^(lang|cli)/' <<<"$listing"; then
  die "sources asset contains lang/ or cli/ -- the compiler itself is already in the binary"
fi
[ "$(tar -tzf "$dist/monad-src.tar.gz")" = "$listing" ] \
  || die "the platform-neutral monad-src.tar.gz is not the same archive as $asset"
ok "sources asset contains neither lang/ nor cli/, and the neutral name is the same archive"

# ---------------------------------------------------------------------------
# 2. Fixture releases
# ---------------------------------------------------------------------------

platform_uname() {
  case "$1" in
    x86_64-linux) echo "Linux x86_64" ;;
    aarch64-linux) echo "Linux aarch64" ;;
    riscv64-linux) echo "Linux riscv64" ;;
    aarch64-darwin) echo "Darwin arm64" ;;
    *) die "no uname pair for platform '$1'" ;;
  esac
}

make_release() {
  local dir="$1" platform="$2" with_sources="${3:-no}"
  mkdir -p "$dir"

  cat > "$dir/monad-nightly-${platform}" <<'SH'
#!/bin/sh
[ "${1:-}" = version ] && echo "monad fixture (not a real binary)"
exit 0
SH
  chmod +x "$dir/monad-nightly-${platform}"
  printf 'deadbeef\n' > "$dir/commit.txt"

  if [ "$with_sources" = yes ]; then
    "$root/scripts/stage-mote-sources.sh" "$dir" "$platform" >/dev/null
  fi

  if [ -n "${MONADUP_BIN:-}" ]; then
    # A previous make_release may have left a read-only copy of a store
    # binary here; remove it before copying the new one.
    rm -f "$dir/monadup-${platform}"
    cp "$MONADUP_BIN" "$dir/monadup-${platform}"
    chmod +x "$dir/monadup-${platform}"
  else
    cat > "$dir/monadup-${platform}" <<'SH'
#!/bin/sh
printf '%s\n' "$*" >> "${MONADUP_FIXTURE_LOG:-/dev/null}"
exit 0
SH
    chmod +x "$dir/monadup-${platform}"
  fi

  local assets
  assets="{\"name\":\"monad-nightly-${platform}\",\"browser_download_url\":\"file://${dir}/monad-nightly-${platform}\"}"
  assets="${assets},{\"name\":\"monadup-${platform}\",\"browser_download_url\":\"file://${dir}/monadup-${platform}\"}"
  if [ "$with_sources" = yes ]; then
    assets="${assets},{\"name\":\"monad-src-${platform}.tar.gz\",\"browser_download_url\":\"file://${dir}/monad-src-${platform}.tar.gz\"}"
  fi
  printf '[{"tag_name":"%s","assets":[%s]}]' "$tag" "$assets" > "$dir/releases"
}

# ---------------------------------------------------------------------------
# 3. Bootstrap stub: pipe-safe fetch/exec and no-arg install
# ---------------------------------------------------------------------------

bash -n "$root/scripts/monadup" || die "scripts/monadup has a syntax error"
ok "scripts/monadup parses"

fix_stub="$work/release-stub"
home_stub="$work/home-stub"
export MONADUP_FIXTURE_LOG="$work/stub.log"
: > "$MONADUP_FIXTURE_LOG"
make_release "$fix_stub" x86_64-linux yes

MONAD_HOME="$home_stub" MONADUP_API_URL="file://${fix_stub}/releases" \
MONADUP_UNAME="Linux x86_64" \
  "$root/scripts/monadup" list > "$work/stub-exec.log" 2>&1 \
  || { cat "$work/stub-exec.log" >&2; die "the stub failed to fetch/exec"; }
if [ -n "${MONADUP_BIN:-}" ]; then
  grep -q "no nightlies installed" "$work/stub-exec.log" \
    || { cat "$work/stub-exec.log" >&2; die "the stub did not exec the monadup binary"; }
else
  grep -qx "list" "$MONADUP_FIXTURE_LOG" \
    || die "the stub did not exec the monadup asset with its arguments"
fi
ok "the stub fetches and execs the monadup asset with the user's arguments"

# The stub's own platform table (scripts/lib/platform-label.sh drives the
# release side; the stub keeps a standalone copy because it is published
# without a checkout). Drive every pair through uname.
for platform in x86_64-linux aarch64-linux riscv64-linux aarch64-darwin; do
  fix_p="$work/release-stub-${platform}"
  log_p="$work/stub-platform-${platform}.log"
  : > "$log_p"
  make_release "$fix_p" "$platform" no
  MONAD_HOME="$work/home-stub-${platform}" \
  MONADUP_API_URL="file://${fix_p}/releases" \
  MONADUP_UNAME="$(platform_uname "$platform")" \
  MONADUP_FIXTURE_LOG="$log_p" \
    "$root/scripts/monadup" list > "$work/stub-platform-${platform}.out" 2>&1 \
    || { cat "$work/stub-platform-${platform}.out" >&2; die "the stub failed for ${platform}"; }
  if [ -n "${MONADUP_BIN:-}" ]; then
    grep -q "no nightlies installed" "$work/stub-platform-${platform}.out" \
      || die "the stub did not select the ${platform} asset"
  else
    grep -qx "list" "$log_p" || die "the stub did not select the ${platform} asset"
  fi
done
ok "the stub's platform table covers all four release labels"

home_stub2="$work/home-stub-install"
MONAD_HOME="$home_stub2" MONADUP_API_URL="file://${fix_stub}/releases" \
MONADUP_UNAME="Linux x86_64" \
  "$root/scripts/monadup" > "$work/stub-install.log" 2>&1 \
  || { cat "$work/stub-install.log" >&2; die "the no-arg stub install failed"; }
[ -x "$home_stub2/bin/monadup" ] || die "the no-arg stub did not install bin/monadup"
grep -q "export PATH" "$work/stub-install.log" || die "the no-arg stub printed no PATH hint"
ok "the no-arg stub installs bin/monadup and prints the PATH hint"

# Pipe-safety: the stub is read from stdin exactly as `curl | bash` does,
# and must not consume the rest of the stream.
(cat "$root/scripts/monadup" | MONAD_HOME="$work/home-pipe" \
  MONADUP_API_URL="file://${fix_stub}/releases" MONADUP_UNAME="Linux x86_64" bash) \
  > "$work/stub-pipe.log" 2>&1 \
  || { cat "$work/stub-pipe.log" >&2; die "the stub failed when read from stdin"; }
[ -x "$work/home-pipe/bin/monadup" ] || die "the pipe-installed stub produced no binary"
ok "the stub is pipe-safe (curl … | bash)"

# With arguments the stub execs the downloaded binary; that child must not
# consume stdin either. A sentinel read AFTER the stub runs proves it.
printf 'SENTINEL\n' | {
  MONAD_HOME="$work/home-pipe-args" \
  MONADUP_API_URL="file://${fix_stub}/releases" MONADUP_UNAME="Linux x86_64" \
    bash "$root/scripts/monadup" install > "$work/stub-pipe-args.log" 2>&1 \
    || { cat "$work/stub-pipe-args.log" >&2; die "the stub failed with args on a pipe"; }
  IFS= read -r leftover || true
  [ "$leftover" = "SENTINEL" ] || die "the stub (or its child) consumed stdin"
} || exit 1
ok "the stub's exec path leaves stdin untouched"

# The stub enforces a published checksum too.
fix_stub_sum="$work/release-stub-sum"
home_stub_sum="$work/home-stub-sum"
make_release "$fix_stub_sum" x86_64-linux no
sha256sum "$fix_stub_sum/monadup-x86_64-linux" > "$fix_stub_sum/monadup-x86_64-linux.sha256"
MONAD_HOME="$home_stub_sum" MONADUP_API_URL="file://${fix_stub_sum}/releases" \
MONADUP_UNAME="Linux x86_64" \
  "$root/scripts/monadup" install > "$work/stub-sum.log" 2>&1 \
  || { cat "$work/stub-sum.log" >&2; die "the stub rejected a matching checksum"; }
ok "the stub accepts a matching checksum"

printf '%064d  monadup-x86_64-linux\n' 0 > "$fix_stub_sum/monadup-x86_64-linux.sha256"
if MONAD_HOME="$work/home-stub-sum-bad" MONADUP_API_URL="file://${fix_stub_sum}/releases" \
     MONADUP_UNAME="Linux x86_64" \
     "$root/scripts/monadup" install > "$work/stub-sum-bad.log" 2>&1; then
  die "the stub accepted a mismatched checksum"
fi
grep -q "checksum mismatch" "$work/stub-sum-bad.log" \
  || { cat "$work/stub-sum-bad.log" >&2; die "the stub's checksum failure was not reported"; }
ok "the stub refuses a mismatched checksum"

# Both JSON parsers, when both exist, driven with the other hidden.
path_without() {
  local what="$1" p t
  local dir="$work/path-without-${what}"
  mkdir -p "$dir"
  for t in env bash uname curl tar gzip mkdir chmod rm ln cat basename jq python3 mktemp mv sha256sum shasum; do
    [ "$t" = "$what" ] && continue
    p="$(command -v "$t" 2>/dev/null || true)"
    [ -n "$p" ] && ln -sf "$p" "$dir/$t"
  done
  echo "$dir"
}

if command -v jq >/dev/null 2>&1 && command -v python3 >/dev/null 2>&1; then
  for parser in jq python3; do
    fix_p="$work/release-parser-${parser}"
    home_p="$work/home-parser-${parser}"
    make_release "$fix_p" x86_64-linux no
    MONAD_HOME="$home_p" MONADUP_API_URL="file://${fix_p}/releases" \
    MONADUP_UNAME="Linux x86_64" PATH="$(path_without "$parser")" \
      "$root/scripts/monadup" list > "$work/stub-parser-${parser}.log" 2>&1 \
      || { cat "$work/stub-parser-${parser}.log" >&2; die "the stub failed with ${parser} hidden"; }
  done
  ok "the stub works with jq hidden and with python3 hidden"
else
  ok "only one JSON parser is present; the other stub branch is untested on this machine"
fi

# ---------------------------------------------------------------------------
# 4. The binary (only when MONADUP_BIN is set)
# ---------------------------------------------------------------------------

if [ -z "${MONADUP_BIN:-}" ]; then
  echo "check-monadup: all checks passed (stub mode; set MONADUP_BIN to drive the binary)"
  exit 0
fi

[ -x "$MONADUP_BIN" ] || die "MONADUP_BIN is not executable: $MONADUP_BIN"

# 4a. Install the binary, sources and layout, for every platform.
for platform in x86_64-linux aarch64-linux riscv64-linux aarch64-darwin; do
  fix="$work/release-${platform}"
  home="$work/home-${platform}"
  make_release "$fix" "$platform" yes

  MONAD_HOME="$home" MONADUP_API_URL="file://${fix}/releases" \
  MONADUP_UNAME="$(platform_uname "$platform")" \
    "$MONADUP_BIN" install > "$work/install-${platform}.log" 2>&1 \
    || { cat "$work/install-${platform}.log" >&2; die "monadup install failed for ${platform}"; }

  vdir="$home/downloads/${tag}"
  [ -x "$vdir/monad-nightly-${platform}" ] || die "no executable ${platform} binary in ${vdir}"
  [ "$(cat "$vdir/commit.txt")" = deadbeef ] || die "commit.txt was not installed for ${platform}"
  for m in init std llvm runtime; do
    [ -d "$vdir/$m" ] || die "the sources asset was not unpacked for ${platform}: ${vdir}/${m} is missing"
  done
  [ -f "$vdir/mote.toml" ] || die "the generated root mote.toml is missing from ${vdir}"
  [ -f "$vdir/std/src/map.mo" ] || die "the unpacked std is not the real std (${platform})"
  [ -f "$vdir/llvm/src/ir.mo" ] || die "the unpacked llvm is not the real llvm (${platform})"
  [ "$(cat "$home/active")" = "$tag" ] || die "the ${platform} fixture was not made active"
  [ "$(readlink "$home/bin/monad")" = "../downloads/${tag}/monad-nightly-${platform}" ] \
    || die "bin/monad does not point at the ${platform} binary"
  if [ -e "$vdir/monad-src-${platform}.tar.gz" ] || [ -e "$vdir/monad-src.tar.gz" ]; then
    die "the sources tarball was left in the ${platform} version directory"
  fi
done
ok "the binary installs the compiler, commit.txt and the four motes, for all four platforms"

# 4b. `list`, `use`, `uninstall` (active refusal).
home="$work/home-x86_64-linux"
MONAD_HOME="$home" "$MONADUP_BIN" list > "$work/list.log" 2>&1 || die "list failed"
grep -q "\* ${tag}" "$work/list.log" || { cat "$work/list.log" >&2; die "list did not mark the active tag"; }
ok "list marks the active nightly"

if MONAD_HOME="$home" "$MONADUP_BIN" uninstall "$tag" > "$work/uninstall.log" 2>&1; then
  die "uninstall removed the active nightly"
fi
grep -qi "cannot uninstall active" "$work/uninstall.log" || die "uninstall did not explain the refusal"
ok "uninstall refuses the active nightly"

MONAD_HOME="$home" "$MONADUP_BIN" use "$tag" > "$work/use.log" 2>&1 || die "use failed"
[ "$(readlink "$home/bin/monad")" = "../downloads/${tag}/monad-nightly-x86_64-linux" ] \
  || die "use did not refresh bin/monad"
ok "use switches the active nightly"

# 4c. A binary-only release still installs and explains itself.
fix_old="$work/release-binary-only"
home_old="$work/home-binary-only"
make_release "$fix_old" x86_64-linux no
MONAD_HOME="$home_old" MONADUP_API_URL="file://${fix_old}/releases" \
  "$MONADUP_BIN" install > "$work/install-old.log" 2>&1 \
  || { cat "$work/install-old.log" >&2; die "a release with no sources asset must still install"; }
vdir_old="$home_old/downloads/${tag}"
[ -x "$vdir_old/monad-nightly-x86_64-linux" ] || die "no binary from a binary-only release"
[ -e "$vdir_old/init" ] && die "a binary-only release must not produce an init/ directory"
grep -q "ships no monad-src-x86_64-linux.tar.gz and no monad-src.tar.gz" "$work/install-old.log" \
  || { cat "$work/install-old.log" >&2; die "no note about the missing sources asset"; }
grep -q "declare \[dependencies.runtime\]" "$work/install-old.log" \
  || { cat "$work/install-old.log" >&2; die "the note does not say what the user loses"; }
ok "a binary-only release installs, exits 0 and says what is missing"

# 4d. The fallback chain.
fix_only="$work/release-x86_64-only"
home_fallback="$work/home-fallback"
make_release "$fix_only" x86_64-linux yes
MONAD_HOME="$home_fallback" MONADUP_API_URL="file://${fix_only}/releases" \
MONADUP_UNAME="Linux aarch64" \
  "$MONADUP_BIN" install > "$work/install-fallback.log" 2>&1 \
  || { cat "$work/install-fallback.log" >&2; die "an aarch64 machine must install an x86_64-only release"; }
[ -x "$home_fallback/downloads/${tag}/monad-nightly-x86_64-linux" ] || die "the fallback installed no x86_64 binary"
[ -d "$home_fallback/downloads/${tag}/init" ] || die "the fallback installed no sources"
grep -q "ships no monad-nightly-aarch64-linux binary" "$work/install-fallback.log" \
  || { cat "$work/install-fallback.log" >&2; die "the fallback does not name the platform it looked for"; }
ok "a release with only x86_64-linux installs on aarch64, and says so"

fix_odd="$work/release-odd"
home_odd="$work/home-odd"
make_release "$fix_odd" x86_64-linux yes
MONAD_HOME="$home_odd" MONADUP_API_URL="file://${fix_odd}/releases" \
MONADUP_UNAME="SunOS sun4u" \
  "$MONADUP_BIN" install > "$work/install-odd.log" 2>&1 \
  || { cat "$work/install-odd.log" >&2; die "an unrecognised machine must still install"; }
grep -q "no nightly is published for 'SunOS sun4u'" "$work/install-odd.log" \
  || { cat "$work/install-odd.log" >&2; die "no note naming the unrecognised machine"; }
ok "an unrecognised machine installs x86_64 and names itself"

fix_none="$work/release-no-assets"
home_none="$work/home-no-assets"
make_release "$fix_none" x86_64-linux yes
sed 's/monad-nightly-x86_64-linux/monad-nightly-sparc-solaris/g' "$fix_none/releases" > "$fix_none/releases.tmp"
mv "$fix_none/releases.tmp" "$fix_none/releases"
if MONAD_HOME="$home_none" MONADUP_API_URL="file://${fix_none}/releases" \
   MONADUP_UNAME="Linux riscv64" "$MONADUP_BIN" install > "$work/install-none.log" 2>&1; then
  die "a release shipping no asset for this machine must fail"
fi
grep -q "monad-nightly-riscv64-linux" "$work/install-none.log" || die "the error does not name the platform asked for"
grep -q "monad-nightly-x86_64-linux" "$work/install-none.log" || die "the error does not name the fallback"
ok "a release with neither asset fails, naming both and the platform asking"

# 4e. Repair: re-running install adds sources to a binary-only directory.
make_release "$fix_old" x86_64-linux yes
MONAD_HOME="$home_old" MONADUP_API_URL="file://${fix_old}/releases" \
  "$MONADUP_BIN" install > "$work/reinstall.log" 2>&1 \
  || { cat "$work/reinstall.log" >&2; die "re-running install failed"; }
grep -q "already installed" "$work/reinstall.log" || die "re-running install did not take the already-installed path"
for m in init std llvm runtime; do [ -d "$vdir_old/$m" ] || die "re-running install did not add ${m}/"; done
ok "re-running install repairs a binary-only version directory"

# 4e-bis. Checksum verification: a published `.sha256` is enforced.
fix_sum="$work/release-sum"
home_sum="$work/home-sum"
make_release "$fix_sum" x86_64-linux no
sha256sum "$fix_sum/monad-nightly-x86_64-linux" > "$fix_sum/monad-nightly-x86_64-linux.sha256"
MONAD_HOME="$home_sum" MONADUP_API_URL="file://${fix_sum}/releases" MONADUP_UNAME="Linux x86_64" \
  "$MONADUP_BIN" install > "$work/install-sum.log" 2>&1 \
  || { cat "$work/install-sum.log" >&2; die "a matching checksum was rejected"; }
[ -x "$home_sum/downloads/${tag}/monad-nightly-x86_64-linux" ] \
  || die "the checksum-verified install produced no binary"
ok "a matching checksum is accepted"

home_sum_bad="$work/home-sum-bad"
printf '%064d  monad-nightly-x86_64-linux\n' 0 > "$fix_sum/monad-nightly-x86_64-linux.sha256"
if MONAD_HOME="$home_sum_bad" MONADUP_API_URL="file://${fix_sum}/releases" MONADUP_UNAME="Linux x86_64" \
     "$MONADUP_BIN" install > "$work/install-sum-bad.log" 2>&1; then
  die "a mismatched checksum was accepted"
fi
grep -q "checksum mismatch" "$work/install-sum-bad.log" \
  || { cat "$work/install-sum-bad.log" >&2; die "the mismatch was not reported as a checksum error"; }
ok "a mismatched checksum is refused"

# 4e-ter. `update` and uninstalling a non-active tag.
fix_upd="$work/release-update"
home_upd="$work/home-update"
make_release "$fix_upd" x86_64-linux no
MONAD_HOME="$home_upd" MONADUP_API_URL="file://${fix_upd}/releases" MONADUP_UNAME="Linux x86_64" \
  "$MONADUP_BIN" default > "$work/default-upd.log" 2>&1 \
  || { cat "$work/default-upd.log" >&2; die "default failed"; }
mkdir -p "$home_upd/downloads/nightly-OLD"
MONAD_HOME="$home_upd" "$MONADUP_BIN" uninstall nightly-OLD > "$work/uninstall-old.log" 2>&1 \
  || { cat "$work/uninstall-old.log" >&2; die "uninstall of a non-active tag failed"; }
[ ! -d "$home_upd/downloads/nightly-OLD" ] || die "uninstall left the non-active directory"
ok "uninstall removes a non-active nightly"

MONAD_HOME="$home_upd" MONADUP_API_URL="file://${fix_upd}/releases" MONADUP_UNAME="Linux x86_64" \
  "$MONADUP_BIN" update > "$work/update.log" 2>&1 \
  || { cat "$work/update.log" >&2; die "update failed"; }
[ -x "$home_upd/bin/monad" ] || die "update left no bin/monad"
ok "update keeps the latest nightly active"

# 4f. doctor, doctor --json, env, new, self-install, upgrade.
fix_x86="$work/release-x86_64-linux"
home_x86="$work/home-x86_64-linux"
MONAD_HOME="$home_x86" MONADUP_API_URL="file://${fix_x86}/releases" MONADUP_UNAME="Linux x86_64" \
  "$MONADUP_BIN" doctor --no-network > "$work/doctor.log" 2>&1 || true
grep -q "summary:" "$work/doctor.log" || { cat "$work/doctor.log" >&2; die "doctor printed no summary"; }
grep -q "\[ok\] llc" "$work/doctor.log" || die "doctor did not check llc"
ok "doctor reports the toolchain checks"

MONAD_HOME="$home_x86" MONADUP_API_URL="file://${fix_x86}/releases" MONADUP_UNAME="Linux x86_64" \
  "$MONADUP_BIN" doctor --json --no-network > "$work/doctor.json" 2>&1 || true
jq -e '.tool == "monadup"
       and (.checks | type == "array")
       and (.summary | has("ok") and has("warn") and has("fail"))' \
  "$work/doctor.json" >/dev/null \
  || die "doctor --json is not valid JSON with the expected keys"
ok "doctor --json is machine-readable"

# On an unrecognised machine the fallback note must go to stderr; anything
# on stdout would prefix (and break) the JSON report.
MONAD_HOME="$home_x86" MONADUP_API_URL="file://${fix_x86}/releases" MONADUP_UNAME="SunOS sun4u" \
  "$MONADUP_BIN" doctor --json --no-network > "$work/doctor-fallback.json" 2> "$work/doctor-fallback.err" || true
jq -e '.platform == "x86_64-linux" and (.checks | type == "array")' \
  "$work/doctor-fallback.json" >/dev/null \
  || die "doctor --json is not valid JSON on a fallback platform"
grep -q "no nightly is published" "$work/doctor-fallback.err" \
  || die "the fallback note did not reach stderr"
ok "fallback-platform doctor --json keeps stdout machine-readable"

MONAD_HOME="$home_x86" "$MONADUP_BIN" env > "$work/env.log" 2>&1 || die "env failed"
grep -q "^platform:" "$work/env.log" || die "env printed no platform"
grep -q "^toolchain root:" "$work/env.log" || die "env printed no toolchain root"
ok "env reports the resolved environment"

rm -rf "$work/scaffold"
MONAD_HOME="$home_x86" "$MONADUP_BIN" new demo --dir "$work/scaffold" > "$work/new.log" 2>&1 \
  || { cat "$work/new.log" >&2; die "new failed"; }
for f in mote.toml src/main.mo README.md .gitignore; do
  [ -f "$work/scaffold/demo/$f" ] || die "new did not write $f"
done
grep -q 'name = "demo"' "$work/scaffold/demo/mote.toml" || die "new's manifest does not name the project"
if [ -n "${MONAD_BIN:-}" ]; then
  # MONAD_BIN is a command plus flags (`cargo run --release --quiet --`),
  # split deliberately, like scripts/check-docs.sh.
  # shellcheck disable=SC2086
  $MONAD_BIN check "$work/scaffold/demo" || die "the scaffold does not type-check"
  ok "new scaffolds a project that type-checks"
else
  ok "new scaffolds a buildable project (MONAD_BIN unset; compile skipped)"
fi

MONAD_HOME="$home_x86" "$MONADUP_BIN" self-install > "$work/self-install.log" 2>&1 \
  || { cat "$work/self-install.log" >&2; die "self-install failed"; }
[ -x "$home_x86/bin/monadup" ] || die "self-install did not install bin/monadup"
ok "self-install copies the running binary"

MONAD_HOME="$home_x86" MONADUP_API_URL="file://${fix_x86}/releases" MONADUP_UNAME="Linux x86_64" \
  "$MONADUP_BIN" upgrade > "$work/upgrade.log" 2>&1 \
  || { cat "$work/upgrade.log" >&2; die "upgrade failed"; }
[ -x "$home_x86/bin/monadup" ] || die "upgrade removed the installed binary"
ok "upgrade fetches the monadup asset"

echo "check-monadup: all checks passed"
