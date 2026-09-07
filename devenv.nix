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
    shellcheck
    wasm-pack
    lld
    llvm
    clang
    # Conservative GC for the GENERATED runtime (lang/codegen/runtime.c),
    # not for anything in this repo's Rust host. The nix cc-wrapper puts
    # its include/lib paths on clang's search path, which is why
    # `link_ir` can just say `-lgc` and `runtime.c` can just say
    # `#include <gc.h>` with no store paths hardcoded anywhere.
    #
    # DELIBERATELY TEMPORARY -- see
    # plans/bootstrapping/linear-types-memory.md.
    boehmgc
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

  scripts.monad-re.exec = ''
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
  # still cover on every push. `tasks."monad:bootstrap-compile"` below is
  # the self-hosted self-compile, run from `.github/workflows/ci.yml`
  # alongside this one.
  #
  # slow_tests/ now passes (107/107 as of the self-hosted parser fixes that
  # unblocked `test_typecheck_lang_main`), so it runs unwrapped here and a
  # slow_tests/ failure fails `devenv test`/CI like every other check.
  tasks."monad:test" = {
    exec = ''
      ${config.devenv.root}/scripts/check-monad-tests.sh
    '';
  };
  # The self-hosted compiler compiles ITSELF, and then the binary that
  # falls out has to do the job it was built for.
  #
  # The second step is the one with teeth. `compile` succeeding only says
  # llc and clang were happy with the emitted IR; it says nothing about
  # whether the binary works, and a compiler that builds but miscompiles
  # is worse than one that fails to build. Running `check lang/main.mo`
  # through it costs ~12s and exercises the whole front end -- parser,
  # scope, elaboration, typechecker -- on the largest input in the tree.
  #
  # What this deliberately does NOT check is the fixpoint: that the `.ll`
  # this binary produces from the same source is byte-identical to the one
  # the host produced (it is, and all three stages agree bit-for-bit), and
  # that the same holds one more turn out. That is the stronger property
  # and the one that would regress silently, but it costs another full
  # self-compile per turn, which is more than this job should carry today.
  # Verified by hand at 56e5e33; if this gets cheap enough, add it here.
  tasks."monad:bootstrap-compile" = {
    exec = ''
      set -euo pipefail
      out="''${TMPDIR:-/tmp}/monad-bootstrap-ci"
      rm -rf "$out"; mkdir -p "$out"
      # --release: debug info is on by default since stage 5, and this job
      # already runs at 1176s of a 1200s timeout with it off — the wrapper
      # cost would push a slower CI machine past the line.
      timeout 1200 cargo run --release -- run lang/main.mo compile lang/main.mo -o "$out/monad" --verbose --release
      test -x "$out/monad"
      "$out/monad" check lang/main.mo
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
    shellcheck = {
      enable = true;
      entry = "shellcheck";
      files = "^scripts/.*\\.sh$|^scripts/monadup$";
      pass_filenames = true;
    };
  };

  # See full reference at https://devenv.sh/reference/options/
}
