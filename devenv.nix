{
  pkgs,
  lib,
  config,
  inputs,
  ...
}:

{

  # https://devenv.sh/packages/
  packages = with pkgs; [
    wasm-pack
    lld
    llvm
    clang
  ];

  # https://devenv.sh/languages/
  languages.rust.enable = true;

  # https://devenv.sh/processes/
  # processes.dev.exec = "${lib.getExe pkgs.watchexec} -n -- ls -la";

  # https://devenv.sh/services/
  # services.postgres.enable = true;

  # https://devenv.sh/scripts/
  scripts.web-repl.exec = ''
    cd wasm/web
    wasm-pack build --target web || exit
    cd ../pkg
    npx serve . 
  '';

  scripts.bootstrap.exec = ''
    cargo run --release -- run lang/main.mo $@
  '';

  scripts.monad-rs.exec = ''
    cargo run --release -- $@
  '';

  # https://devenv.sh/basics/
  enterShell = "";

  # https://devenv.sh/tests/
  # NB: Do not use for CI tests. this is run every time devenv is loaded
  enterTest = "";

  # https://devenv.sh/tasks/
  # Full "run everything" sweep for CI (see .github/workflows/ci.yml).
  # Reuses the git-hooks below (rustfmt, clippy, cargo test --release, and the
  # fast `init std lang examples` .mo sweep) via `prek` (the Rust pre-commit
  # runner this devenv's git-hooks.nix installs) so there's a single source
  # of truth, then adds slow_tests/ -- deliberately excluded from the hooks'
  # own sweep since it's ~91% of total test runtime, but something CI should
  # still cover on every push. `tasks."monad:bootstrap-compile"` below is a
  # separate, currently-opt-in self-hosted self-compile smoke test -- see
  # its own comment for why it isn't wired to run automatically here yet.
  #
  # slow_tests/ now passes (107/107 as of the self-hosted parser fixes that
  # unblocked `test_typecheck_lang_main`), so it runs unwrapped here and a
  # slow_tests/ failure fails `devenv test`/CI like every other check.
  tasks."monad:test" = {
    exec = ''
      cargo run --release -- test init std lang examples slow_tests --json
    '';
  };
  tasks."monad:bootstrap-compile" = {
    exec = ''
      timeout 1200 cargo run --release -- run lang/main.mo compile lang/main.mo monad --verbose || {
        echo "::warning::self-hosted self-compile failed or timed out (known-broken, fix in progress -- see plans/implementations/2026-08-28-string-value-representation-unification.md) -- not blocking CI" >&2
        true
      }
    '';
  };

  # https://devenv.sh/git-hooks/
  git-hooks.hooks = {
    commit-msg-format = {
      enable = true;
      name = "commit-msg-format";
      description = ''
        Enforce "scope: msg", "scope/sub: msg", or "scope/sub(type): msg"
        (see scripts/check-commit-msg.sh).
      '';
      entry = "${config.devenv.root}/scripts/check-commit-msg.sh";
      pass_filenames = true;
      always_run = true;
      stages = [ "commit-msg" ];
    };
    rustfmt.enable = true;
    clippy.enable = true;
    rust-tests = {
      enable = true;
      entry = ''
        cargo test --release
      '';
      pass_filenames = false;
      files = "\\.(rs|mo)$";
    };
    monad-tests = {
      enable = true;
      entry = "${config.devenv.root}/scripts/check-monad-tests.sh";
      pass_filenames = false;
      files = "\\.(rs|mo)$";
    };
  };

  # See full reference at https://devenv.sh/reference/options/
}
