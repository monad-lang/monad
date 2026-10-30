# The Rust bootstrap host: rung 1 of the ladder, and the only thing that can
# build `cli/src/main.mo` (rung 2 is the result). `nix build .#monadHost`.
#
# It is a package of its own rather than a step inside `monad`'s build, which
# is what makes `nix build .#monadHost` a ~3 minute answer to "does the Rust
# side still build" rather than a ~20 minute one: rung 1 sits DOWNSTREAM of the
# host, not upstream of it, so asking about the host never drags the self-hosted
# build in. Its `src` is filtered to the cargo inputs (see below), so a commit
# touching only `.mo` sources, docs or workflows is a STORE HIT here. It used to
# be `src = ../.`, which put the whole tree in the derivation's hash -- editing
# any file in the repository invalidated it too (measured at the time by
# touching flake.nix and rebuilding: "Compiling hashbrown"). That mattered
# because `.#monad` takes this package as a native input, so a cold host was
# paid inside rung 1's own build, and because a whole-tree hash is unshareable
# between the two CI runners by construction.
#
# See nix/monad.nix for what consumes it, and nix/bootstrap.nix for the check
# that asserts the ladder is at a fixpoint.
{ monadVersion }:
{
  perSystem =
    { pkgs, lib, ... }:
    {
      packages.monadHost = pkgs.rustPlatform.buildRustPackage {
        pname = "monad-rs";
        version = monadVersion;

        # Path literals are relative to THIS file, so `./.` would be `nix/`;
        # the flake root is one level up. `cargoLock.lockFile` derives every
        # crates.io input's hash from the committed lock file, so there is no
        # `cargoHash` to keep in sync by hand.
        #
        # Only the cargo inputs are in the source, which is what makes this
        # derivation shareable across commits that do not touch them. The
        # filter keeps what the build actually reads, no more:
        #
        #   * EVERY workspace member under `rust/` (the root `members` list
        #     names `core` and `rust-cli`; cargo parses it before it does
        #     anything else).
        #   * `rust/.cargo/config.toml`, which is a cargo input even though it
        #     reaches no source file: it sets `RUST_MIN_STACK = 16 MiB` for
        #     the processes cargo runs. Leaving it out would change the
        #     build's environment silently.
        #   * NOT the monad sources. The `include_str!` calls that reach
        #     `init/`, `std/` and `examples/` (rust/core/src/core_check_module.rs)
        #     are inside `#[cfg(test)] mod test`, and `doCheck = false` below
        #     means no test build ever expands them; the stdlib is a RUNTIME
        #     path, which is why the CI job exports MONAD_STDLIB.
        src = lib.fileset.toSource {
          root = ../rust;
          fileset = lib.fileset.unions [
            ../rust/.cargo
            ../rust/Cargo.lock
            ../rust/Cargo.toml
            ../rust/core
            ../rust/rust-cli
          ];
        };
        cargoLock.lockFile = ../rust/Cargo.lock;

        # `-p monad-cli` rather than the whole workspace, which keeps the
        # `monad-core` dependency as the only crate the host needs.
        cargoBuildFlags = [
          "-p"
          "monad-cli"
        ];

        # Cargo's default output is `rust/target`, but nixpkgs' cargo-install
        # hook looks in a literal `target/@targetSubdirectory@/$cargoBuildType`
        # relative to the build directory. Pinning the variable (to the same
        # place the default would use) keeps the install hook and cargo
        # agreeing without a config file override.
        CARGO_TARGET_DIR = "target";

        # CI runs the Rust suite from the dev shell; this derivation only
        # needs to produce the host binary.
        doCheck = false;

        # Deliberately no `git`. No input in Cargo.lock is a git dependency, so
        # the only thing it could have served here was the build-commit probe
        # `llvm/src/link.mo` used to run -- and there is no probe any more: a
        # linked binary is stamped with the LINKING compiler's own revision
        # (`build_commit_define`), which for the packaged `monad` means the
        # `MONAD_BUILD_COMMIT` the flake exports in nix/monad.nix. A host built
        # with `git` on PATH does not need it, and a store copy has no `.git`
        # for it to read anyway.
        meta.mainProgram = "monad-rs";
      };
    };
}
