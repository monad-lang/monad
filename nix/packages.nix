# The dev shell's packages: the toolchain the compiled ladder and the sweep
# shell out to, the C libraries the generated runtime and motes link, and the
# tools the CI scripts under scripts/ call. A devenv module of its own, imported
# by devenv.nix, so the list can be read (and diffed) apart from the shell's
# tasks, hooks and languages.
#
# https://devenv.sh/packages/
{ pkgs, ... }:

{
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
    # `enableStatic = true` ships `libgc.a` alongside `libgc.so`, so
    # `monad build` can link gc statically (`link_objects` in
    # `llvm/src/link.mo` passes `-Wl,-Bstatic -lgc -Wl,-Bdynamic` on
    # Linux, or the `.a` by path on Darwin). The parens are load-bearing:
    # a list element parses at select depth, so without them
    # `boehmgc.override { enableStatic = true; }` is TWO elements -- the
    # bare `override` lambda and the attrset -- and devenv's `packages`
    # type check dies on the function.
    #
    # DELIBERATELY TEMPORARY -- see
    # plans/bootstrapping/linear-types-memory.md.
    (boehmgc.override { enableStatic = true; })
    # OpenSSL for `motes/tls`'s `#[extern "c"]` binding. Same cc-wrapper
    # story as boehmgc: include/lib paths land on clang's search path, so
    # the mote's `[link] libs = ["ssl", "crypto"]` needs no store paths.
    openssl
    # Resolves a mote's `[link] pkg-config` (tls: `openssl`) to explicit `-L`
    # flags at link time (`llvm/src/link.mo`'s `pkg_config_link_flags`), so
    # the link does not hinge on `NIX_LDFLAGS` surviving to the linker.
    pkg-config

    # The docs/ book. `.github/workflows/mdbook.yml` installs its own copy
    # to publish monad-lang.org; this is so a docs change can be previewed
    # locally (`docs-serve`) before it ships, and so `mdbook build` is
    # available to check that SUMMARY.md still resolves.
    mdbook
    # Zola generates the landing page (monad-lang.org) with Tera templates;
    # mdBook output lands in Zola's static/docs/ so docs are served at /docs/.
    zola
    file

    # The tools the CI scripts under scripts/ call, declared here because a
    # bare `run:` step in CI gets the runner HOST path, not this shell's --
    # and that path has neither `awk` nor `lscpu`. Run 36313431973's `test`
    # job died 8 s in on `lscpu: command not found` / `awk: command not
    # found`, exit 127, measuring nothing. See scripts/ci-cpu-budget.sh.
    #
    # `type -p <tool>` INSIDE this shell is not evidence either, which is the
    # trap this list closes: `nix develop` leaves the ambient system PATH in
    # place rather than replacing it, so a tool from /run/current-system/sw/bin
    # (lscpu was exactly that, before util-linux below) looks present here and
    # is absent on the runner. Only what is declared here is really the
    # shell's, on both.
    gawk
    coreutils
    gnugrep
    # lscpu. The script guards the call with `command -v`, so losing this
    # would cost a diagnostic line rather than the step.
    util-linux
    # The push side of the binary cache (scripts/push-to-cache.sh): the
    # self-hosted runner host has no cachix of its own.
    cachix
    # The docs-check host's installer (scripts/monadup, run from ci.yml's
    # pre-commit-checks): it downloads a nightly with `curl` and reads the
    # release JSON with `jq` (its python3 fallback is no more present on the
    # runner than jq is). The runner service's own PATH carries bash, git,
    # tar and coreutils only, so both have to come from here.
    curl
    jq
  ];
}
