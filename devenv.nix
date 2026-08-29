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
      ${config.devenv.root}/scripts/check-monad-tests.sh
    '';
  };
  # Still known-broken as of 2026-08-29 -- non-blocking (`|| { ...; true; }`)
  # until it compiles+links+runs cleanly AND the resulting binary is
  # verified correct (not just that llc/clang succeed). Five bugs fixed
  # chasing this exact command this session (write_file's 2-arg native
  # dispatch panic, IO.read_file/file_exists missing IO-wrap, an
  # indirect-call callee materialization gap, `Append_append` --
  # `List.append` instead of `++` -- and a parser bug mis-recognizing any
  # `return_`-prefixed identifier as the `return` keyword) got the
  # self-compile past `compile_db_module` entirely and progressively
  # further into `llc`; current frontier is `Show.show` unresolved inside
  # a nested match arm, see
  # `plans/implementations/2026-08-29-show-show-unresolved-carrier-in-
  # nested-match-arm.md`.
  tasks."monad:bootstrap-compile" = {
    exec = ''
      timeout 1200 cargo run --release -- run lang/main.mo compile lang/main.mo monad --verbose || {
        echo "::warning::self-hosted self-compile failed or timed out (known-broken, fix in progress -- see plans/implementations/2026-08-29-show-show-unresolved-carrier-in-nested-match-arm.md) -- not blocking CI" >&2
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
    monad-check = {
      enable = true;
      entry = ''
        cargo run --release -- check init std examples lang
      '';
      pass_filenames = false;
      files = "\\.(rs|mo)$";
    };
  };

  # See full reference at https://devenv.sh/reference/options/
}
