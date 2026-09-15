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

    # The docs/ book. `.github/workflows/mdbook.yml` installs its own copy
    # to publish monad-lang.org; this is so a docs change can be previewed
    # locally (`docs-serve`) before it ships, and so `mdbook build` is
    # available to check that SUMMARY.md still resolves.
    mdbook
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

  scripts.docs-serve.exec = ''
    mdbook serve ${config.devenv.root}/docs --open
  '';

  scripts.bootstrap.exec = ''
    cargo run --release -- run cli/src/main.mo $@
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
  # is worse than one that fails to build. Running `check cli/src/main.mo`
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
      # No timeout, by design: the interpreted self-compile measured ~320s
      # (2026-09-09) but stretches 2-4x when the runner's other jobs and
      # local sessions share this 8-core machine, and `cargo run`'s own
      # build phase is ~10 min cold (fat-LTO profile; CI's ephemeral job
      # containers never have a warm target/). A fixed `timeout` here was
      # killing healthy runs. Progress is visible instead: --verbose
      # streams a per-module and per-stage trace (lang/log.mo), so a
      # genuinely wedged run shows exactly which stage stalled.
      # --release: debug info is on by default; DWARF emission costs ~30s
      # on this workload and the binary this job tests does not need it.
      cargo run --release -- run cli/src/main.mo compile cli/src/main.mo -o "$out/monad" --verbose --release
      test -x "$out/monad"
      "$out/monad" check cli/src/main.mo
      # And again WITHOUT --release, which is the DEFAULT invocation and was
      # broken for an unknown length of time precisely because nothing ran
      # it: `monad compile cli/src/main.mo` died at `no instance found for
      # `Append.append``, and the only signal was a self-compile nobody
      # waited for (it took 7h48m before the located-parse fix).
      #
      # Both modes now share one term tree -- every term carries its source
      # position on every path (`parse_all_decls`, lang/module.mo) -- so this
      # run differs from the one above only in whether DWARF is EMITTED.
      # That is exactly why it is worth running: it is the only gate for the
      # carrier-inference shape probes in lang/scope.mo, which no
      # small-file test can reach (see examples/located_terms.mo's own
      # header for why, verified rather than assumed).
      dbg="''${TMPDIR:-/tmp}/monad-bootstrap-ci-debug"
      rm -rf "$dbg"; mkdir -p "$dbg"
      cargo run --release -- run cli/src/main.mo compile cli/src/main.mo -o "$dbg/monad" --verbose
      test -x "$dbg/monad"
      "$dbg/monad" check cli/src/main.mo
    '';
  };

  # The `Term.ctx` transparency oracle (tools/debug_transparency_oracle.sh).
  #
  # Source positions ride the AST as `Term.ctx` wrappers on every path, and
  # ~180 sites match on term SHAPE. A wrapper interposed where one of those
  # looks does not crash -- it silently stops matching, and a call quietly
  # fails to resolve. This asserts the property that makes wrappers safe:
  # `--debug` may add `!dbg` annotations and nothing else, so stripping them
  # must reproduce the `--release` build byte for byte.
  #
  # It existed, unwired, while the bug it describes was live. Cheap: two
  # compiles per example file, against the SELF-HOSTED BINARY rather than
  # the Rust host interpreting cli/src/main.mo -- the binary is what ships,
  # and it is ~40x faster per file besides.
  tasks."monad:debug-oracle" = {
    exec = ''
      set -euo pipefail
      out="''${TMPDIR:-/tmp}/monad-bootstrap-ci"
      # Reuse the binary `monad:bootstrap-compile` just built -- in CI that
      # is the step immediately before this one, in the same job. Rebuild
      # when it is missing or older than any lang/ source: a stale binary
      # reports failures that are really its own age (one here predated
      # two examples' syntax and could not parse them at all), which would
      # be indistinguishable from the transparency break this looks for.
      if [ ! -x "$out/monad" ] || [ -n "$(find ${config.devenv.root}/lang -name '*.mo' -newer "$out/monad" -print -quit)" ]; then
        mkdir -p "$out"
        cargo run --release -- run cli/src/main.mo compile cli/src/main.mo -o "$out/monad" --release
      fi
      MONAD_BIN="$out/monad" ${config.devenv.root}/tools/debug_transparency_oracle.sh ${config.devenv.root}/examples/*.mo
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
        cargo run --release -- check init std examples lang cli
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
    # `mdbook build` only RENDERS the book -- it never compiles the Monad
    # inside it, which is how docs/src drifted far enough from the compiler
    # that most of its samples had stopped parsing. This extracts every
    # ```monad block and type-checks it, so a language change that breaks
    # a documented example fails here instead of shipping to
    # monad-lang.org. Runs on .md too (a doc edit can break a block on its
    # own) and takes ~3s once the release binary is warm. Blocks tagged
    # ```monad,ignore are deliberately skipped -- see the script's header.
    docs-check = {
      enable = true;
      entry = ''
        ${config.devenv.root}/scripts/check-docs.sh
      '';
      pass_filenames = false;
      files = "\\.(md|mo|rs)$";
    };
  };

  # See full reference at https://devenv.sh/reference/options/
}
