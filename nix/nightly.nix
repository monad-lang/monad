# The pinned previous nightly: the binary that compiles the next compiler.
#
# plans/bootstrapping/nightly-compiles-next.md states the invariant ("the last
# nightly can compile the next compiler") and ci.yml's `compiler-checks` job
# enforces it on every push. This file is the other half: the RELEASE's rung 1
# (nix/monad.nix's `nightlyRung1`, whose `.ll` every `monad-nightly-<platform>`
# asset is relinked from) is compiled by THIS binary instead of by the Rust
# interpreter -- one ~2-minute native build (measured on this tree: 2:10 for
# the pinned binary compiling `cli/src/main.mo` with
# `MONAD_HOST_BIN=<this>/bin/monad scripts/build-self-hosted.sh`) against the
# ~26-minute interpretation the release used to pay on every cold leg, and
# the Mac leg no longer pays the Rust host's own cold build either.
#
# THE PIN, and why the "latest" nightly is a pinned one. A derivation input
# cannot be "whatever is newest right now": the fetched binary, the rung it
# compiles and the release relinked from that rung are all keyed on the sha256
# below, so a night's build is reproducible, cacheable and shared by every leg
# -- and nothing downstream moves when tomorrow's nightly is published. The
# hash is the one the release publishes beside the asset itself
# (`monad-nightly-<platform>.sha256`, written by scripts/nightly-release.sh),
# so bumping the pin needs no local build:
#
#   curl -fsSL "<url>.sha256"   # one line per pinned platform below
#
# WHEN TO BUMP: AGENTS.md's two-step rollout. Compiler sources may use a new
# construct only once a nightly containing it exists -- and the release's host
# is the PINNED nightly, so adopting one means bumping this pin to a nightly
# that has it, in the same change. A stale pin fails LOUDLY, with the host's
# own unknown-construct error at rung 1, before anything is staged; that is
# the same contract scripts/ci-self-compile.sh gives the gate, not a silent
# lag. (`bootstrap/nightly-floor.txt` still gates the CI side against the
# TRUE latest nightly, which stays the stricter of the two.)
#
# The asset is the bare release binary, fetched read-only into the store: the
# Linux one is fully static and the Darwin one needs only libSystem
# (nix/monad.nix links gc statically and `-static` on Linux for exactly this
# portability), so both run inside the build sandbox with no patching. It is
# installed as `bin/monad` and not left under its fetch name for two reasons:
# a store file carries no execute bit, and both consumers key on that basename
# -- `lib.getExe` below, and scripts/build-self-hosted.sh's host dispatch,
# which takes its one-rung native path exactly when the host's basename is
# `monad`. The tree it compiles is the build's own unpacked `compilerSrc`, with
# MONAD_STDLIB pointed at it by that script, so a pinned host no older than
# the tree reads the same sources the interpreted rung would.
#
# `unsafeDiscardReferences`, on both derivations, is not hygiene relaxation
# for its own sake: the LINUX asset embeds /nix/store paths as STRINGS --
# measured on nightly-2026-11-01-d6238985: five, all static glibc's compiled-in
# defaults (its gconv module dir, locale archive, ld.so.cache and getconf
# paths; `-static` links the `.a` that carries them) -- and a fixed-output
# download refuses content that scans as referencing store paths. The strings
# are inert -- `ldd` reports "not a dynamic executable" and
# scripts/nightly-release.sh's own check greps it clean of live dependencies --
# so discarding the scan states the truth: the binary's runtime closure is
# empty, and nothing in this flake should ever pull the asset's build-time
# glibc in as a dependency. The Darwin asset scans clean (0 hits, measured on
# the same nightly); the attribute is set for both anyway so the two platforms
# differ only in their pin entries.
#
# The two derivations below spell the discard differently because THIS nix
# (2.35, Determinate) reads the attribute from a different place depending on
# how the derivation passes its attributes, and fetchurl and runCommand
# differ (all verified empirically against a fixed-output probe that embedded
# a real /nix/store path from its own input closure):
#
#   - fetchurl FORCES structured attrs (`derivationArgs // {
#     __structuredAttrs = true; ... }` in its default.nix), and under
#     structured attrs the scan reads the UNPREFIXED `unsafeDiscardReferences`
#     as a per-output OBJECT. The `__`-prefixed boolean is carried into the
#     JSON verbatim and ignored there (the probe with it fails exactly like
#     no attribute at all), and an unprefixed boolean is rejected at
#     derivation-parse time ("Expected JSON value to be of type 'object'").
#     `derivationArgs` is fetchurl's pass-through to mkDerivation.
#   - runCommand is by default a flat (env-passed) derivation here, and the
#     flat `__`-prefixed boolean only ever lifts the FIXED-OUTPUT check -- it
#     does not stop a normal derivation from RECORDING the scanned paths (a
#     probe with a flat normal derivation that embedded a real store path
#     still recorded it). The structured object form empties the record too,
#     so `__structuredAttrs` is forced on below to reach the one spelling that
#     does the whole job: with it, `nix-store -q --references` on this output
#     is empty, which is what the paragraph above claims.
#
# The outer discard is load-bearing, not cosmetic: if a future nightly is built
# against a glibc whose store path differs from today's stdenv's, a scanned
# reference would name a path the store does not have, which fails the
# build outright -- the discard keeps the pin a pure byte-for-byte artifact.
#
# Which pin a build uses is decided by the BUILD machine's system, not the
# target's: the cross legs are outputs of x86_64-linux and consume the
# x86_64-linux pin (rung 1 is compiled once on the builder; only the relink is
# per-target), and the aarch64-darwin leg, the one native build that shares no
# rung with the others, uses its own platform's pin the same way.
{
  perSystem =
    { pkgs, lib, ... }:
    let
      # THE PIN. One entry per flake build system, each naming the latest
      # nightly at the time of the bump; the tag is in the URL and in the
      # package name, so `nix build .#monadNightlyHost && ./result/bin/monad
      # version` says which nightly a release was hosted by.
      pins = {
        x86_64-linux = {
          tag = "nightly-2026-11-01-d6238985";
          url = "https://github.com/monad-lang/monad/releases/download/nightly-2026-11-01-d6238985/monad-nightly-x86_64-linux";
          # curl -fsSL "<url>.sha256" -> 30d58afce10ca25929057dcff946290c10158bca07aa3974a90cd29073e13085
          sha256 = "sha256-MNWK/OEMolkpBX3P+UYpDBAVi8oHqjl0qQzSkHPhMIU=";
        };
        aarch64-darwin = {
          tag = "nightly-2026-11-01-d6238985";
          url = "https://github.com/monad-lang/monad/releases/download/nightly-2026-11-01-d6238985/monad-nightly-aarch64-darwin";
          # curl -fsSL "<url>.sha256" -> f5467116dc17bbc7f61222b1c34015d3e54da6030c8109aba7bee83500c53f72
          sha256 = "sha256-9UZxFtwXu8f2EiKxw0AV0+VNpgMMgQmrp77oNQDFP3I=";
        };
      };

      pin =
        pins."${pkgs.stdenv.hostPlatform.system}"
        or (throw "nix/nightly.nix pins no nightly for ${pkgs.stdenv.hostPlatform.system}: add one before building the release family from this system");
    in
    {
      # `nix build .#monadNightlyHost`. Consumed by nix/monad.nix's
      # `nightlyRung1` through `config.packages.monadNightlyHost`, the same
      # cross-module read `monadHost` gets there.
      packages.monadNightlyHost = pkgs.runCommand "monad-nightly-host-${pin.tag}"
        {
          # See the file header's `unsafeDiscardReferences` paragraph: the
          # installed copy carries the same inert strings the fetched asset
          # does, and this output's closure is genuinely empty. Both are the
          # structured-attrs spelling: the flat `__`-prefixed boolean does not
          # stop a normal derivation from recording the scanned paths.
          __structuredAttrs = true;
          unsafeDiscardReferences = { out = true; };

          # `lib.getExe` (nix/monad.nix's rung 1) resolves against
          # meta.mainProgram, and the dispatch in scripts/build-self-hosted.sh
          # resolves against the basename: both must read `monad`.
          meta = {
            mainProgram = "monad";
            description = "The pinned previous monad nightly, host of the release family's rung 1";
            homepage = "https://monad-lang.org";
            license = lib.licenses.asl20;
          };
        }
        ''
          install -Dm755 ${
            pkgs.fetchurl {
              inherit (pin) url sha256;
              # See the file header's `unsafeDiscardReferences` paragraph:
              # the Linux asset's embedded glibc default paths would otherwise
              # fail the fixed-output reference scan before this install ever
              # ran. fetchurl forces structured attrs, so the discard is the
              # unprefixed per-output object there; `derivationArgs` is its
              # pass-through to mkDerivation.
              derivationArgs = {
                unsafeDiscardReferences = { out = true; };
              };
            }
          } $out/bin/monad
        '';
    };
}
