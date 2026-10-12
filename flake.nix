{
  description = "Monad language compiler";

  inputs = {
    nixpkgs.url = "github:cachix/devenv-nixpkgs/rolling";
    devenv.url = "github:cachix/devenv";
    # The module system the three `nix/` files below are written against, and
    # what this file is reduced to assembling. Already locked transitively
    # (devenv uses it), and its nixpkgs input is pinned to this flake's so no
    # second nixpkgs enters the lock.
    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
    git-hooks = {
      url = "github:cachix/git-hooks.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  # CI pushes the built ladder to monad-lang; devenv.cachix.org was always here.
  # Both are read (under --accept-flake-config or a trusted user); only ours is
  # written, and only in CI.
  nixConfig = {
    extra-trusted-public-keys = [
      "devenv.cachix.org-1:w1cLUi8dv3hnoSPGAuibQv+f9TZLr6cv/Hm9XgU50cw="
      "monad-lang.cachix.org-1:iydtAH4RfGNfAimoaX7vfcACG/X8R5A3Iw9wL8dkFDU="
    ];
    extra-substituters = [
      "https://devenv.cachix.org"
      "https://monad-lang.cachix.org"
    ];
  };

  # A thin assembler over three independent modules. Each `nix/*.nix` file owns
  # one rung of the ladder and reads the rung below it as a PACKAGE
  # (`config.packages.monadHost`) rather than as a function applied to it, so
  # the modules can be read, built and cached one at a time:
  #
  #   nix/host.nix     packages.monadHost  the Rust interpreter (rung 0)
  #   nix/monad.nix    packages.monad      rung 1, built by scripts/
  #   nix/bootstrap.nix checks.bootstrap   the fixpoint rung 1 asserts
  #
  # (`nix/packages.nix` is not one of them: it is a DEVENV module, the dev
  # shell's package list, imported by devenv.nix.)
  #
  # The facts the three of them share are passed as explicit import arguments
  # rather than through `_module.args`: they are not module-system state, they
  # are what this flake knows about itself, and `import`-arguments cannot be
  # silently shadowed by a module that happens to declare the same option.
  outputs =
    inputs:
    let
      # What `monad version` reports, and what gets baked into every binary the
      # packaged compiler links (`build_commit_define`, llvm/src/link.mo). A nix
      # build's source tree is a store copy with no `.git`, so the revision has
      # to reach it from the flake rather than from the tree it is building --
      # which is why the derivation exports this as `MONAD_BUILD_COMMIT`.
      #
      # The DIRTY revision is preferred when there is one: `shortRev` on a tree
      # with uncommitted changes is still the last commit, which would label a
      # binary built from modified sources with a revision it does not
      # correspond to. `self.dirtyShortRev` is `"<shortRev>-dirty"`, so the
      # version carries the distinction instead of dropping it.
      commit =
        let
          dirty = inputs.self.dirtyShortRev or null;
          rev = inputs.self.shortRev or null;
        in
        if dirty != null then
          dirty
        else if rev != null then
          rev
        else
          "unknown";

      # One place for the version string, so the three derivations below cannot
      # disagree about it.
      monadVersion = "0.1.0";
    in
    inputs.flake-parts.lib.mkFlake { inherit inputs; } {
      # A system here means a machine that BUILDS, which is why `aarch64-linux`
      # is not one: nothing evaluates on a riscv64 or an arm64 Linux box, and
      # the nightly's binaries for those are cross outputs of x86_64-linux
      # (`monadAarch64Linux`, `monadRiscv64Linux`). The Mac leg is native
      # because cross-building for darwin needs an Apple SDK nixpkgs cannot
      # redistribute, and `macos-15` is arm64.
      systems = [
        "x86_64-linux"
        "aarch64-darwin"
      ];

      imports = [
        (import ./nix/host.nix { inherit monadVersion; })
        (import ./nix/monad.nix { inherit commit monadVersion; })
        (import ./nix/bootstrap.nix { inherit commit monadVersion; })
      ];

      perSystem =
        { pkgs, ... }:
        {
          devShells.default = inputs.devenv.lib.mkShell {
            inherit inputs pkgs;
            modules = [
              {
                packages = [ inputs.devenv.packages.${pkgs.system}.devenv ];
              }
              ./devenv.nix
            ];
          };
        };
    };
}
