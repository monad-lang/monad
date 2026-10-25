# The dev shell's packages: the toolchain the compiled ladder and the sweep
# shell out to, the C libraries the generated runtime and motes link, and the
# tools the CI scripts under scripts/ call. A devenv module of its own, imported
# by devenv.nix, so the list can be read (and diffed) apart from the shell's
# tasks, hooks and languages.
#
# https://devenv.sh/packages/
{ pkgs, ... }:

let
  # wasi-sdk is not packaged in the pinned nixpkgs, so pin the official release
  # tarball. The prebuilt clang needs libtinfo (and the runtime C needs zlib),
  # so autoPatchelfHook rewrites its RPATH against the nix store libraries.
  #
  # The `bin/clang` here is the deliberate exception to this repo's "do not
  # pass --target to the C compiler" rule (`llvm/src/target.mo`): it is a
  # dedicated cross toolchain, not a nixpkgs cc-wrapper being shimmed.
  wasiSdk = pkgs.stdenv.mkDerivation rec {
    pname = "wasi-sdk";
    version = "34.0";

    src = pkgs.fetchurl {
      url = "https://github.com/WebAssembly/wasi-sdk/releases/download/wasi-sdk-34/wasi-sdk-${version}-x86_64-linux.tar.gz";
      sha256 = "sha256-t2HjoHIduunAmgBZ5f2yv5F9G0qKe0MPs7Wq+wmEssQ=";
    };

    nativeBuildInputs = [ pkgs.autoPatchelfHook ];
    buildInputs = [
      pkgs.ncurses
      pkgs.zlib
      pkgs.stdenv.cc.cc.lib
    ];

    sourceRoot = "wasi-sdk-${version}-x86_64-linux";
    dontStrip = true;

    installPhase = ''
      mkdir -p $out
      cp -r . $out/
    '';

    meta.platforms = [ "x86_64-linux" ];
  };
in
{
  # The wasm toolchain and its two hosts. `wasmtime` runs the wasi profile;
  # `nodejs` runs the web profile's direct loader in the smoke test.
  #
  # The pinned wasi-sdk tarball above is the x86_64-linux release. On any
  # other host (Darwin, aarch64-linux) the binding stays unset and the
  # derivation is never forced, so the dev shell still evaluates and
  # `--target wasm32-…` fails with the clear WASI_SDK_PATH diagnostic
  # instead of a store-path or "cannot execute" error.
  env.WASI_SDK_PATH =
    if pkgs.stdenv.hostPlatform.system == "x86_64-linux" then "${wasiSdk}" else "";

  # `wasiSdk` is deliberately NOT in this list: its bin/clang would shadow the
  # nixpkgs clang the native ladder uses (and defaults to wasm32), silently
  # breaking every native build. It is reachable only as $WASI_SDK_PATH.
  packages = with pkgs; [
    shellcheck
    wasmtime
    nodejs
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
    # SQLite for `motes/sqlite`'s `#[extern "c"]` binding. Same cc-wrapper
    # story as openssl: its include/lib paths land on clang's search path,
    # so `[link] libs = ["sqlite3"]` needs no store path here, and the dev
    # output supplies the `sqlite3.pc` that `[link] pkg-config` reads.
    sqlite
    # Resolves a mote's `[link] pkg-config` (tls: `openssl`, sqlite:
    # `sqlite3`) to explicit `-L` flags at link time (`llvm/src/link.mo`'s
    # `pkg_config_link_flags`), so the link does not hinge on `NIX_LDFLAGS`
    # surviving to the linker.
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
