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
    # Conservative GC for the GENERATED runtime (runtime/src/runtime.c),
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
    file
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
  # The "run everything" sweep for CI (see .github/workflows/ci.yml): the full
  # .mo corpus, the self-hosted self-compile, the source-transparency oracle
  # and the nightly, plus devenv's own task for the pre-commit suite.
  #
  # Every task here wraps a script under scripts/ because `showOutput` defaults
  # to false: devenv-tasks captures a task's stdout and shows it only when the
  # task FAILS, so a green CI job would show none of the evidence it collected.
  # The CI jobs therefore call those scripts directly inside `nix develop -c`
  # and these tasks stay as the local equivalent. The one exception --
  # `devenv:git-hooks`, which CI still enters through a task -- says why in
  # its own comment below.
  #
  # The script this calls now builds and uses the SELF-HOSTED binary
  # rather than `cargo run -- test` (the Rust evaluator). The self-hosted
  # runner is what the project ships and what a user gets from `monad
  # test`; running the Rust one here left it untested over the corpus,
  # which is how it went a long time unable to handle more than one
  # `#[test]` per file. See scripts/check-monad-tests.sh for the
  # staleness rules and the async-runtime gap it skips.
  #
  # slow_tests/ now passes (107/107 as of the self-hosted parser fixes that
  # unblocked `test_typecheck_lang_main`), so it runs unwrapped here and a
  # slow_tests/ failure fails `devenv test`/CI like every other check.
  tasks."monad:test" = {
    exec = ''
      ${config.devenv.root}/scripts/check-monad-tests.sh
    '';
  };
  # The nightly release artifact (.github/workflows/nightly.yml), built and
  # verified by scripts/nightly-release.sh (`devenv tasks run monad:nightly`).
  #
  # The workflow itself calls the script directly inside one `nix develop -c`
  # rather than through this task, for a reason specific to that job:
  # devenv-tasks captures a task's stdout and only shows it when the task
  # FAILS, and the nightly's log is the evidence of what got published (the
  # `file` line, the recorded commit, the compile's --verbose stage trace).
  # This task is the local equivalent -- same script, same dev shell, just
  # quieter on success.
  #
  # Either way the point is the same as every step in ci.yml: commands run
  # bare in a `run:` get the RUNNER HOST's PATH, not this shell's, so a tool
  # is only a declared dependency when it comes through `nix develop`. (The
  # `file` line that used to live in that workflow is exactly how that goes
  # wrong: present in this devenv, "command not found" on the runner.)
  tasks."monad:nightly" = {
    exec = ''
      ${config.devenv.root}/scripts/nightly-release.sh
    '';
  };
  # The self-hosted compiler compiles ITSELF, and then the binary that falls
  # out has to do the job it was built for -- twice, once `--release` and once
  # in the default DWARF-emitting mode, each with its own fixpoint `cmp`.
  #
  # The body lives in scripts/bootstrap-compile.sh, which CI calls directly
  # inside `nix develop -c` so that the --verbose per-module and per-stage
  # trace is streamed to the job log: devenv-tasks captures a task's stdout
  # and shows it only when the task FAILS, and a hang guard is only as useful
  # as the trace that says which stage stalled. The script's own header carries
  # the rest of the reasoning -- why the second step has teeth, why both turns
  # of the fixpoint are asserted, and why `ulimit -s` is load-bearing.
  #
  # This task is the local equivalent: same script, same dev shell, just
  # quieter on success (the pattern `monad:nightly` set above).
  tasks."monad:bootstrap-compile" = {
    exec = ''
      ${config.devenv.root}/scripts/bootstrap-compile.sh
    '';
  };

  # The `Term.ctx` transparency oracle (tools/debug_transparency_oracle.sh):
  # `--debug` may add `!dbg` annotations and nothing else, so stripping them
  # must reproduce the `--release` build byte for byte. It is the gate for the
  # ~180 AST-shape match sites a `Term.ctx` wrapper can silently disarm.
  #
  # The body lives in scripts/debug-oracle.sh, which CI calls directly inside
  # `nix develop -c` so the oracle's per-file verdicts reach the job log:
  # devenv-tasks captures a task's stdout and shows it only when the task
  # FAILS, and which file broke transparency is exactly what a failure report
  # needs. It also carries the staleness guard for the binary
  # `scripts/bootstrap-compile.sh` just built.
  #
  # This task is the local equivalent: same script, same dev shell, just
  # quieter on success (the pattern `monad:nightly` set above).
  tasks."monad:debug-oracle" = {
    exec = ''
      ${config.devenv.root}/scripts/debug-oracle.sh
    '';
  };

  # `devenv:git-hooks:run` is devenv's own task -- literally `prek run -a -c
  # .pre-commit-config.yaml` -- and the CI `pre-commit-checks` job is the one
  # step that stays a task rather than calling a script of its own.
  #
  # It is also the sweep every OTHER CI step already pays for. The devShell's
  # shellHook ends in `devenv-tasks run devenv:enterShell --mode all`, and
  # `--mode all` resolves the task graph in both directions from that root
  # rather than only over its prerequisites -- so entering the dev shell runs
  # `devenv:files` (which generates the gitignored .pre-commit-config.yaml),
  # `devenv:git-hooks:install` and this task, the whole `prek run -a`, before
  # any command in the step starts. A hook that fails there fails the shell
  # (`nix develop` exits 1), so it decides the step: the pre-commit job's own
  # command is never even reached when a hook has already failed at entry.
  #
  # What the setting below changes: devenv-tasks streams a task's output only
  # for tasks with `showOutput` (its ui.rs: `VerbosityLevel::Normal =>
  # state.show_output`), and a failing task is the one case that does not need
  # it -- the failure report prints the captured stdout and stderr either way.
  # So the case it buys is the GREEN run: which hooks ran and what they said,
  # in the step log, instead of nothing at all. It has to be set here rather
  # than on the CI command line because the entry-time run above is where the
  # sweep actually happens. `devenv:git-hooks:install` and `devenv:files` stay
  # quiet: their output is setup chatter rather than a result.
  tasks."devenv:git-hooks:run".showOutput = true;

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
        cargo run --release -- check init std examples lang cli llvm runtime motes
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
