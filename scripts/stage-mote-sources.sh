#!/usr/bin/env bash
# Stage the SECOND nightly artifact: the mote sources a consumer needs.
#
# The binary alone cannot compile anything outside a compiler checkout. It
# resolves `init`/`std` from CWD-relative literals (`init/src/`, `std/src/`)
# and the C runtime from a workspace-root walk that falls back to
# `runtime/src/runtime.c` (`runtime/src/lib.mo`'s `Runtime.c_path`) -- so
# `use std::map` and every `compile`/`run`/`test` need a checked-out tree,
# which is exactly what an external mote workspace does not have. This
# tarball is the other half: unpacked into the version directory by
# `monadup`, it makes that directory a toolchain root the compiler can find
# (`Mote.toolchain_root`, `lang/src/mote.mo`).
#
# Only the motes a CONSUMER needs are in it. `lang`/`cli` are the compiler
# itself and are already in the binary; shipping them would double the
# artifact for nothing. `src/` goes in wholesale, including the
# `*_tests.mo` modules: that is one rule instead of a filter, and it makes
# the bundle self-testable, because `init`'s `[dev-dependencies.std]`
# resolves inside it.
#
# `llvm` is a consumer dependency even though it is named after the backend
# toolchain rather than after a language feature: it is the LLVM IR data
# model, and `runtime`'s natives are emitted as LLVM IR rather than written
# in C (`runtime/src/natives.mo` uses `llvm::ir`, and `runtime/mote.toml`
# declares the dependency). Leaving it out made the unpacked root a
# workspace whose own `monad check -w` reported `unresolved module: llvm::ir`
# -- a broken bundle, since `runtime` is the one mote every `compile` needs.
#
# Sizes that make this cheap (mote.toml + src, in bytes): init 81904, std
# 152336, runtime 112350, llvm 83933 -- 430 KB of source for the toolchain
# root, against a binary of a few MB.
#
# The generated root manifest is what makes the unpacked directory a
# WORKSPACE rather than four loose motes, so a human can `monad check -w`
# in it and `monadup`'s directory is directly usable as `MONAD_ROOT`.
#
# The archive is written under the platform's name AND under the
# platform-neutral one. The tree is the same on every platform -- only the name
# is not -- and both names have a reader: an installed `monadup` resolves
# `monad-src-<platform>.tar.gz` through the releases API, which is why the
# per-platform names exist at all, and `monadup` falls back to the neutral name,
# which is what lets a leg stop publishing the per-platform copies without
# making a release look source-less. See scripts/monadup's do_install_sources.
#
# Usage: scripts/stage-mote-sources.sh [out_dir] [platform]
#   (defaults: <root>/dist, and this machine's platform)
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
out_dir="${1:-$root/dist}"
MONAD_PLATFORM="${2:-}"
# shellcheck source=scripts/lib/platform-label.sh
# shellcheck disable=SC1091  # the hook runs bare `shellcheck`; the line above names the path for -x
. "$root/scripts/lib/platform-label.sh"
asset="$out_dir/monad-src-${MONAD_PLATFORM}.tar.gz"
neutral="$out_dir/monad-src.tar.gz"

# Dependency order, not alphabetical: `llvm` before `runtime`, which declares
# it, and both after `init`/`std`, which they declare. The order is cosmetic
# for the archive and for `--workspace`; it is written this way so the list
# can be read against the manifests.
member_manifests=(init/mote.toml std/mote.toml llvm/mote.toml runtime/mote.toml)
members=(init std llvm runtime)

for m in "${members[@]}"; do
  [ -f "$root/$m/mote.toml" ] || { echo "stage-mote-sources: $m/mote.toml is missing" >&2; exit 1; }
  [ -d "$root/$m/src" ] || { echo "stage-mote-sources: $m/src is missing" >&2; exit 1; }
done

mkdir -p "$out_dir"

# Staged in a private temp dir, then tarred with an explicit member list so
# the archive holds `init/...`, not `./init/...`. `mktemp -d` rather than a
# fixed path under /tmp: two runs on one machine must not share it.
staging="$(mktemp -d "${TMPDIR:-/tmp}/monad-src-stage.XXXXXX")"
trap 'rm -rf "$staging"' EXIT

for m in "${members[@]}"; do
  mkdir -p "$staging/$m"
  cp "$root/$m/mote.toml" "$staging/$m/mote.toml"
  cp -R "$root/$m/src" "$staging/$m/src"
done

cat > "$staging/mote.toml" <<'TOML'
# The unpacked toolchain root: what `monadup` leaves in the version
# directory beside the binary. See scripts/stage-mote-sources.sh.
#
# Written with a `[workspace]` header rather than an inline table because
# the self-hosted reader (motes/toml/src/toml.mo) supports headers only.

[workspace]
members = ["init", "std", "llvm", "runtime"]

# Members inherit these with `workspace = true`; an inherited path is
# root-relative, which is why the unpacked root (not the member) names them.
[workspace.dependencies.init]
path = "init"

[workspace.dependencies.std]
path = "std"

[workspace.dependencies.llvm]
path = "llvm"

[workspace.dependencies.runtime]
path = "runtime"
TOML

rm -f "$asset" "$neutral"
tar -czf "$asset" -C "$staging" "${members[@]}" mote.toml
# A hard link, not a copy: same directory, same bytes, one inode -- and the
# release uploads each name separately, so nothing downstream can tell.
ln -f "$asset" "$neutral"

# The archive is the artifact; assert its shape here rather than in the
# release step, so a wrong member list fails the build that produced it.
#
# `llvm/src/ir.mo` is named apart from its `mote.toml` because the manifest
# alone only proves the mote directory is there: the module `runtime`'s
# natives actually import is this file, and an `llvm/` staged without `src/`
# would satisfy the manifest check and still fail `monad check -w` in the
# unpacked root.
listing="$(tar -tzf "$asset")"
for want in "${member_manifests[@]}" llvm/src/ir.mo runtime/src/runtime.c mote.toml; do
  grep -qxF "$want" <<<"$listing" \
    || { echo "stage-mote-sources: '$want' is not in $asset" >&2; exit 1; }
done

echo "stage-mote-sources: wrote $asset and $neutral"
wc -c < "$asset" | sed 's/^/stage-mote-sources: /;s/$/ bytes/'
