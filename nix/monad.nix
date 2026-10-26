# Rung 1, in two derivations: the host interprets `cli/src/main.mo` into a real
# `monad` plus the `.ll` it emitted (`packages.monadRung1`), and a small link
# step stamps that `.ll` with this commit's revision (`packages.monad`).
#
# The split exists because of what made the old single derivation uncacheable.
# `.#monad` was cold on EVERY commit for two independent reasons -- its `src`
# was `../.`, the whole tree, and `MONAD_BUILD_COMMIT` was interpolated into
# its phases -- so the 20-minute interpretation was paid again by every commit,
# including one that changed only a workflow file. The revision has to be baked
# in (see installPhase), so the second reason cannot be removed from the
# arithmetic. What CAN be removed is the interpretation: the revision never
# enters the emitted IR, so the expensive half is a pure function of the
# compiler's sources, and the per-commit half is a three-command link.
#
# That the revision does not reach the IR is measured, not assumed. Two rung-1
# builds of the same source stamped with two DIFFERENT revisions (5441725 and
# 6770f64) emitted byte-identical `monad.ll` -- `cmp` clean on 5417399 bytes --
# which is what makes a commit-free `rung1` a legitimate input to a stamped
# `.#monad`. `monad_build_commit` reaches the binary as a `declare` the runtime
# object defines (`llvm/src/link.mo`'s `build_commit_define`, and
# runtime/src/runtime.c's `#ifdef MONAD_BUILD_COMMIT`), which is why the define
# has to be applied by a LINK and not by a wrapper.
#
# `.#monad` is what `packages.default` and `apps.monad` point to, so
# `nix build .#monad` and `nix run .#monad` are unchanged. It is a
# build-and-check artifact rather than a distributable one, and the reason is
# now only that this derivation installs the BINARY and not the sources: the
# compiler finds `init`/`std`/`llvm`/`runtime` in the target mote's declared
# `[dependencies.X] path` entries, in an installed toolchain root
# (`$MONAD_ROOT`, else `$MONAD_HOME` + `active`) or by walking up from the
# working directory to a workspace root (`resolve_runtime_src`,
# `lang/src/module.mo`). The nightly artifact is the distributable half
# precisely because `scripts/stage-mote-sources.sh` also ships the four motes
# beside the binary; a store copy of this derivation has no such directory to
# point at and cannot name one (see MONAD_BUILD_COMMIT below for the same
# "a store copy cannot name itself" constraint). Bare, then, a packaged
# `monad build` runs from a checkout, exactly as CI runs it.
#
# The step that builds rung 1 is `scripts/build-self-hosted.sh`, not a shell
# command spelled out here: CI builds rung 1 through that same script in
# check-monad-tests.sh, bootstrap-compile.sh and debug-oracle.sh, and the two
# drifted apart once already (the absolute `-o`, commit b8af914). The host
# arrives as a built input rather than as the script's default `cargo run`,
# which is what MONAD_HOST_BIN is for. The stack raise, and the note that says
# what the limit actually came out as, are the script's too -- a nix sandbox
# cannot raise RLIMIT_STACK (soft == hard), so rung 1 runs here with less
# stack than CI gives it, and it completes anyway.
{ commit, monadVersion }:
{
  perSystem =
    {
      pkgs,
      config,
      lib,
      ...
    }:
    let
      monadHost = config.packages.monadHost;

      # The collector, with its static archive. Every link in this file goes
      # through either `gcLink`'s archive-by-path or `llvm/src/link.mo`'s
      # `-Wl,-Bstatic -lgc -Wl,-Bdynamic` (the self-compiles: rung1's own
      # build runs the compiler that link_objects serves), and both need
      # `libgc.a` on the linker path -- the default boehmgc ships only the
      # shared object, which is how CI's rung-1 link died on `cannot find
      # -lgc` / "have you installed the static version of the gc library".
      gcStatic = pkgs.boehmgc.override { enableStatic = true; };

      # What the packaged compiler needs at RUNTIME, as opposed to at build
      # time: every `monad build` shells out to `llc` and `clang` by bare
      # name (llvm/src/link.mo), plus `mkdir`/`rm` for the link stage's own
      # output directory and the codegen harnesses' artifacts. `bash` is what
      # the build-commit probe's `sh -c` used to need; the probe is gone (the
      # compiler names its own revision now, `build_commit_define`), and bash
      # is left in only because dropping it would change the packaged closure
      # for a reason nothing here measures.
      runtimePath = lib.makeBinPath [
        pkgs.llvm
        pkgs.clang
        pkgs.bash
        pkgs.coreutils
        # `llvm/src/link.mo`'s `pkg_config_link_flags`: a mote's
        # `[link] pkg-config` is resolved to `-L` flags at link time.
        pkgs.pkg-config
      ];

      # The install step both derivations share. `$PWD/monad` is where each
      # buildPhase leaves the binary, and the wrapper supplies the runtime PATH
      # and the gc paths exactly as the single derivation always did.
      #
      # `gc` is the collector the binary was linked against -- the static
      # override natively (`gcStatic` above), and that target's own on a
      # cross leg. The generated runtime
      # includes `<gc.h>` and links `-lgc`, so both the header and the library
      # have to be reachable from a bare `clang`, and they are passed TWO ways
      # on purpose: the `NIX_*` variables are what nixpkgs' wrapped clang
      # reads, and `LIBRARY_PATH`/`CPATH` are what any clang reads. Which of
      # the two carries the flag depends on whether the `clang` found first is
      # the wrapped one, and there is no reason to depend on that. A CROSS cc
      # reads neither -- nixpkgs' wrapper overwrites `LIBRARY_PATH` and drops a
      # hand-set `NIX_LDFLAGS`, measured -- which is why a cross leg's shim
      # carries the same two flags as argv (`crossMonadFor`).
      #
      # `--prefix`, never `--set`: the gc paths are ADDED to whatever the
      # caller's environment carries. `--set` replaced it, so inside a dev
      # shell the store-built rung-1 erased openssl's `-L` from `NIX_LDFLAGS`
      # and every `motes/tls` link in CI's sweep died on `cannot find -lssl`.
      # (A mote's own libs now reach the link through `[link] pkg-config`
      # regardless; this keeps the wrapper from fighting anything else.)
      #
      # And every `--prefix` value must be ONE word, which is why the include
      # is `-I<dir>` GLUED and never `-isystem <dir>`. `makeWrapper`'s
      # `--prefix ENV SEP VAL` splits VAL on the separator and, for EACH word,
      # removes the first ` SEP <word> SEP ` already in the variable before
      # prepending -- a `PATH`-style de-dup. `-isystem <dir>` is TWO words, so
      # it de-dups twice against whatever the caller carries: the `<dir>` word
      # eats a live ` <dir> ` out of the inherited list (gluing its
      # neighbours), and the `-isystem` word eats the first ` -isystem `,
      # orphaning whatever dir it introduced. Inside this repo's own dev shell
      # the result was a `NIX_CFLAGS_COMPILE` with two BARE include dirs in it
      # (lld's and gc's own): clang drops those with a warning at `-c`, but at
      # LINK time it passes them to ld as input files, and ld.bfd's script
      # lexer cannot read a directory -- `read in flex scanner failed`, every
      # link dead. That was CI run 38432093049, whose `compiler-checks` job
      # took its release rung-1 from the store (`rung 1: re-using the store
      # build`) and so ran the WRAPPED binary inside the dev shell for the
      # first time; a rung-1 built from source is the raw binary and links
      # fine, which is why the debug ladder passed in the same run. `-I` glued
      # is one word, de-dups only against itself, and `clang` reads it
      # identically.
      #
      # `extraFlag` is spliced in as the LAST continuation of the `makeWrapper`
      # call, and it is either another `makeWrapper` argument or the empty
      # string: `.#monad` passes `--set MONAD_BUILD_COMMIT <rev>`, and `rung1`
      # passes nothing, because a `--set` of a fixed revision is precisely the
      # per-commit input this split removes. The empty case is not a stylistic
      # choice -- the flags above are a multi-line string that ends in a
      # newline, so a caller spelling its extra flag as
      #
      #     makeWrapper ... ${wrapperFlags} \
      #       --set MONAD_BUILD_COMMIT ${commit}
      #
      # would have that newline TERMINATE the `makeWrapper` command, leaving
      # the next line to run as a command of its own: `--set: command not
      # found`. Splicing keeps one command one command whatever is passed, and
      # the empty string leaves the continuation pointing at a blank line,
      # which ends the command exactly where the flags do.
      #
      # `extraPath` is prefixed to the wrapper's PATH and is empty for the
      # native target. It has to reach the INSTALLED compiler and not only the
      # phase that linked it: `llvm/src/link.mo` compiles `runtime.c` and links
      # through the bare name `clang`, so a user's build with the packaged
      # compiler links with whatever that name finds.
      installPhaseWith = gc: extraFlag: extraPath: ''
        runHook preInstall
        install -Dm755 "$PWD/monad" $out/share/monad/monad
        makeWrapper $out/share/monad/monad $out/bin/monad \
          --prefix PATH : ${extraPath}${runtimePath} \
          --prefix NIX_LDFLAGS " " "-L${lib.getLib gc}/lib" \
          --prefix NIX_CFLAGS_COMPILE " " "-I${lib.getDev gc}/include" \
          --prefix LIBRARY_PATH : "${lib.getLib gc}/lib" \
          --prefix CPATH : "${lib.getDev gc}/include" \
          --prefix PKG_CONFIG_PATH : "${lib.getDev gc}/lib/pkgconfig" \
          ${extraFlag}
        runHook postInstall
      '';

      # A1 -- WHAT THE BUILD READS, which is what a derivation's hash should
      # cover and what `src = ../.` did not.
      #
      # `scripts/build-self-hosted.sh`'s staleness scan is the authoritative
      # input list and is the guide here: the trees the compiler is built from,
      # their `.mo`/`.c`/`.h` sources and each one's `mote.toml`. That is the
      # complete set for those trees -- enumerated rather than assumed: they
      # hold 188 `.mo`, 13 `mote.toml` and exactly one `.c`
      # (runtime/src/runtime.c), and no file of any other name. `.h` is in the
      # filter and matches nothing today; it is there because the script scans
      # for it, and a header added later must not silently fall outside the
      # hash that is supposed to cover it.
      #
      # THE RULE, because this list has been wrong twice: every mote the
      # compiler's own sources IMPORT is a compiler input. `cli/mote.toml`
      # declares `[dependencies.lsp]` and `cli/src/main.mo` has
      # `use lsp::server`, so rung 1 -- which compiles `cli/src/main.mo` --
      # needs `motes/lsp`, and `motes/lsp` needs `motes/toolkit` (its own
      # `[dependencies]`) and `motes/json` (`use json::json`). Adding a mote to
      # `cli/mote.toml` without adding it here fails the buildPhase with
      # `module not found: <mote>.<module>`: the import that could not resolve,
      # never the missing input that caused it. (Measured both ways on a tree
      # assembled by exactly this filter: without a mote it is exactly that
      # error -- most recently `json`, which `6424aacb` moved out of `lang` and
      # added only as `toml` -- and with them `1 file(s) checked, 0 error(s)`.)
      #
      # Three things outside the scan are kept because the build needs them:
      #
      #   * the root `mote.toml`. Its `[workspace] members` names trees this
      #     filter drops (`bench`, `proofs`, `slow_tests`, and the motes that
      #     are not compiler inputs), and the fear was that the memberlist is
      #     walked eagerly and their absence would break the load. It is not:
      #     the compiler's own source checks clean in a tree assembled by
      #     exactly this filter with those trees absent. The file stays because
      #     it is the workspace-root marker `resolve_runtime_src` walks up to
      #     find, and losing that is a different failure from losing a member.
      #   * `scripts/build-self-hosted.sh`, the one script buildPhase enters,
      #     and `scripts/lib` beside it, which is where that script's helpers
      #     live (`lib/raise-stack.sh`, sourced at its line 55). A `source`d
      #     file is invisible to the extension filter above, and omitting it is
      #     how commit 22b4e287 came to break this derivation: rung 1 died at
      #     that line with `No such file or directory`. The rest of `scripts/`
      #     stays out, so a CI script's edit still does not invalidate a
      #     20-minute build.
      #   * `nix/` is NOT kept, and neither are the flake files: nothing in the
      #     build reads them. The revision and the version reach this
      #     derivation as `commit` and `monadVersion` arguments, and the
      #     toolchain reaches it through `pkgs`.
      #
      # 205 files and 4.7 MiB, against the whole tracked tree's 476 files and
      # 8.1 MiB (both measured -- re-measure rather than adjust these, they
      # have gone stale three times). What that buys is not a smaller build --
      # it is a SHAREABLE one: `rung1` below carries no commit, so this hash is
      # the same across two commits that differ only outside these paths, and
      # that is the prerequisite for two CI runs ever sharing the result.
      compilerSrc = lib.fileset.toSource {
        root = ../.;
        fileset = lib.fileset.unions (
          [
            ../mote.toml
            ../scripts/build-self-hosted.sh
            (lib.fileset.fileFilter (f: f.hasExt "sh") ../scripts/lib)
          ]
          ++
            map
              (
                tree:
                lib.fileset.fileFilter (f: f.hasExt "mo" || f.hasExt "c" || f.hasExt "h" || f.name == "mote.toml") (
                  ../. + "/${tree}"
                )
              )
              [
                "init"
                "std"
                "lang"
                "cli"
                "llvm"
                "runtime"
                "build"
                # The shared evaluator: `cli` links it for `monad eval` and
                # `monad repl`, so it is a compiler input like `lang`/`build`.
                "eval"
                # Compiler inputs -- see THE RULE above. `clap` arrives through
                # `cli`, whose `main.mo` parses its own argv with it;
                # `lsp`/`toolkit` arrive through `cli` too (its `lsp` subcommand),
                # and `json` through `lsp`, which speaks JSON-RPC; `parsec` and
                # `toml` arrive through `lang` itself, which parses with one and
                # reads every manifest with the other. Not the rest of `motes/`:
                # those are consumers of the compiler, not part of it, and keeping
                # them out is what stops an unrelated mote's edit from
                # invalidating a 20-minute interpretation.
                "motes/clap"
                "motes/json"
                "motes/lsp"
                "motes/parsec"
                "motes/toml"
                "motes/toolkit"
              ]
        );
      };

      # monadup's inputs. The compiler itself is a packaged binary, so this
      # tree only needs the motes monadup imports (its closure includes
      # `runtime`, hence `llvm`) and `runtime/src/runtime.c`, which the final
      # relink compiles. `motes/serde` is present because `motes/json`'s
      # manifest declares it. Kept OUT of `compilerSrc`: monadup is a
      # consumer of the compiler, not part of it.
      monadupSrc = lib.fileset.toSource {
        root = ../.;
        fileset = lib.fileset.unions (
          [ ../mote.toml ]
          ++
            map
              (
                tree:
                lib.fileset.fileFilter (f: f.hasExt "mo" || f.hasExt "c" || f.hasExt "h" || f.name == "mote.toml") (
                  ../. + "/${tree}"
                )
              )
              [
                "init"
                "std"
                "llvm"
                "runtime"
                "motes/clap"
                "motes/json"
                "motes/parsec"
                "motes/serde"
                "motes/monadup"
              ]
        );
      };

      # The interpretation. Commit-free by construction: no phase below
      # mentions `commit`, and neither does `nix/host.nix`, which takes only
      # `monadVersion` -- so nothing in this derivation's inputs can move with
      # the revision, which is the whole point of it. What `monad version`
      # prints from this output is therefore a constant and not this commit;
      # the revision belongs to `.#monad` below, and it gets one.
      #
      # It installs `monad.ll` BESIDE the binary, which is the enabling change
      # for CI's bootstrap job: the ladder there asserts the
      # interpreted-vs-compiled comparison and needs the IR the interpreter
      # wrote, and `nix/monad.nix` has deliberately never installed one. The
      # reasoning that kept it out -- "exactly one consumer, the
      # interpreted-vs-compiled `cmp`... a store copy would grow every
      # consumer's closure by 5.4 MB of IR" -- is an argument about the
      # PACKAGED `.#monad`, whose consumers compile programs and have no use
      # for the IR of the compiler itself. A dedicated rung-1 output whose only
      # consumer is that ladder is the different thing that argument allows
      # for, and `.#monad` still installs the binary alone.
      rung1 = pkgs.stdenv.mkDerivation {
        pname = "monad-rung1";
        version = monadVersion;

        src = compilerSrc;

        # No `git` here either (see nix/host.nix): a store copy has no `.git`,
        # so nothing in this build could name the revision from the tree it is
        # building -- and this derivation must not name one at all.
        nativeBuildInputs = [
          monadHost
          pkgs.llvm
          pkgs.clang
          pkgs.lld
          pkgs.makeWrapper
          pkgs.bash
          pkgs.coreutils
        ];
        buildInputs = [ gcStatic ];

        # The script below is entered by its shebang, exactly as CI enters it,
        # and a nix build has no `/usr/bin/env` to resolve that shebang with.
        # nixpkgs patches shebangs from `fixupOutputHooks` -- on the OUTPUT, at
        # the end -- so the unpacked source arrives at buildPhase still saying
        # `#!/usr/bin/env bash` and the build dies with "bad interpreter". This
        # one line patches the tree instead; `pkgs.bash` above is the
        # interpreter it rewrites to.
        postPatch = "patchShebangs scripts";

        buildPhase = ''
          runHook preBuild

          # `$PWD` is the unpacked source root, which is what the script is
          # given as its output directory -- the script writes `$PWD/monad`
          # beside the `.ll` it emits for the same reason this is spelled
          # absolutely.
          MONAD_HOST_BIN=${lib.getExe monadHost} scripts/build-self-hosted.sh "$PWD" --release

          runHook postBuild
        '';

        # `""` for the flag and the path, so this wrapper sets no revision and
        # puts nothing ahead of the runtime PATH: rung 1 has no revision to
        # set, and it is this machine's code whatever the target below is for.
        # The collector is the native one, because so is the code. The `.ll` is
        # installed ahead of the shared step because that step is a complete
        # phase, hooks and all, and `install` needs none of them.
        installPhase = ''
          install -Dm644 "$PWD/monad.ll" $out/share/monad/monad.ll
          ${installPhaseWith gcStatic "" ""}
        '';

        meta = {
          description = "Rung 1 of the Monad bootstrap ladder, with the IR it emitted";
          homepage = "https://monad-lang.org";
          license = lib.licenses.asl20;
          mainProgram = "monad";
        };
      };
    in
    let
      # A2 -- the per-commit half, and it is a link.
      #
      # Three commands, and they are `llvm/src/link.mo`'s four stages one to
      # one: `llc` on the IR, `clang -c` on the runtime with the revision
      # defined, `clang` over the two objects with `-lgc`. It is written out
      # here rather than reached through the compiler because the compiler has
      # no way in: `link_ir` is only ever entered with IR it just generated
      # from `.mo` modules, so re-stamping a `.ll` on disk means performing
      # the same three steps.
      #
      # That this reproduces what the interpretation would have produced is
      # measured rather than argued. Re-running these stages against a rung-1
      # build (rung1's own `monad.ll`, `runtime/src/runtime.c` at the stamped
      # revision, the same llc and clang) reproduced its binary byte for byte
      # -- 2603672 bytes, `cmp` clean -- once the linker's environment-derived
      # RUNPATH was accounted for: the same experiment against a binary linked
      # in a different devenv shell differed only in that RPATH, 205828 bytes,
      # and differs in nothing else.
      #
      # `-DMONAD_BUILD_COMMIT="<rev>"` is spelled the way `link_ir` builds it
      # (`"-DMONAD_BUILD_COMMIT=\"" ++ build_hash ++ "\""`), single-quoted
      # shell-side so the quotes reach clang. The path
      # `runtime/src/runtime.c` is `Runtime.c_path`, a literal, and it is used
      # RELATIVE because that is what the compiler passes; an absolute path
      # produces a different object file from the same source.
      #
      # It is a function of its TARGET, which is the one axis these three
      # commands have left: the IR is rung 1's and so carries THIS machine's
      # triple, and the cc that compiles `runtime.c` and links has to be the
      # target's own. Both splices below are inline in the phase rather than
      # lines of their own, because an empty one has to contribute nothing at
      # all -- a blank line would already be a different phase, and the native
      # argv being provably unchanged is the point of the shape.
      #
      #   * `llcFlags`: `-mtriple=<t>` and whatever else llc needs, leading
      #     space included.
      #   * `ccPath`: a directory to put first on PATH, reaching the phase's
      #     `clang` and the installed compiler's.
      #   * `gc`: the target's collector, which the phase links against and the
      #     wrapper points `clang` at.
      #   * `gcLink`: how the link names that collector -- `-lgc` (dynamic)
      #     unless a target says otherwise; see `monad` below for the one that
      #     does.
      #   * `checkPhase`: how to prove the result RUNS, for a target this
      #     machine cannot execute directly. Null for the native target, which
      #     runs in front of whoever built it.
      monadFor =
        {
          gc ? pkgs.boehmgc,
          gcLink ? "-lgc",
          llcFlags ? "",
          ccPath ? null,
          checkPhase ? null,
          # Extra flags for the final link step only (not `clang -c`).
          # Linux passes `" -static"` so the published binary carries no
          # /nix/store library paths; Darwin leaves this empty because
          # libSystem is always dynamic (platform convention).
          linkFlags ? "",
          # The -static archives of the libc the link targets: the native
          # leg's own on a native build, the cross leg's on a cross one
          # (`crossMonadFor`). stdenv puts its `lib` dir on the wrapped
          # clang's `-L` path, which is the only way `-static` finds
          # `libc.a` -- the default glibc output has no archives.
          glibcStatic ? pkgs.glibc.static,
        }:
        pkgs.stdenv.mkDerivation (
          {
            pname = "monad";
            version = monadVersion;

            src = compilerSrc;

            # No `git` here either (see nix/host.nix): a store copy has no `.git`,
            # so nothing in this build could name the revision from the tree it is
            # building. MONAD_BUILD_COMMIT below is the answer instead -- it wins
            # over the compiler's own revision in `build_commit_define`, which is
            # what makes the packaged compiler report the revision it was built
            # from rather than the one its host happens to have.
            #
            # `monadHost` is NOT here: this derivation never runs the interpreter.
            # It reads `rung1`'s output instead, which is the whole point.
            nativeBuildInputs = [
              pkgs.llvm
              pkgs.clang
              pkgs.lld
              pkgs.makeWrapper
              pkgs.bash
              pkgs.coreutils
            ]
            # Static glibc libraries (libc.a, libpthread.a, etc.) are needed
            # when linking with -static. The default stdenv only provides
            # shared glibc; glibcStatic provides the .a archives.
            ++ lib.optionals (linkFlags != "") [ glibcStatic ];
            buildInputs = [ gc ];

            buildPhase = ''
              runHook preBuild

              # Rung 1's IR, linked here with this commit's revision. `rung1` is a
              # build input and not a runtime one: the `.ll` is copied out of its
              # store path, and `llc` records the path it was GIVEN -- this build
              # directory -- so the finished binary should name no store path of
              # rung 1's. That is checked after the build with `nix-store -q
              # --references` on this derivation's output, not asserted here.
              ${
                lib.optionalString (ccPath != null) "export PATH=${ccPath}:$PATH\n"
              }install -Dm644 ${rung1}/share/monad/monad.ll "$PWD/monad.ll"

              llc -filetype=obj${llcFlags} "$PWD/monad.ll" -o "$PWD/monad.o"
              clang -pthread -c runtime/src/runtime.c \
                "-DMONAD_BUILD_COMMIT=\"${commit}\"" \
                -o "$PWD/monad_runtime.o"
              clang${linkFlags} -pthread "$PWD/monad.o" "$PWD/monad_runtime.o" ${gcLink} -o "$PWD/monad"

              runHook postBuild
            '';

            installPhase = installPhaseWith gc "--set MONAD_BUILD_COMMIT ${commit}" (
              lib.optionalString (ccPath != null) "${ccPath}:"
            );

            meta = {
              description = "The self-hosted Monad compiler";
              homepage = "https://monad-lang.org";
              license = lib.licenses.asl20;
              mainProgram = "monad";
            };
          }
          // lib.optionalAttrs (checkPhase != null) {
            # `//` on the ARGUMENT and not on the derivation: `doCheck` and
            # `checkPhase` are read out of the environment mkDerivation builds, so
            # setting them on its RESULT would put them outside the derivation and
            # the check would never run.
            doCheck = true;
            inherit checkPhase;
          }
        );

      # The native target, spelled as the empty spec: every default is the
      # answer that leaves the native phase and the wrapper byte-identical.
      #
      # Static gc on every target. Darwin already needed it (dyld loads the
      # .dylib's absolute install name -- a /nix/store path -- and the nightly
      # publishes the bare binary); Linux needs it so the published binary
      # carries no /nix/store library paths. The archive is passed BY PATH
      # rather than as `-lgc`: ld64 prefers a `.dylib` over a `.a` in the same
      # directory, and `enableStatic` builds both. `gc` is the same override
      # so the header the runtime is compiled against comes from the build
      # that produced the archive.
      #
      # Linux additionally passes `-static` to the final link, producing a
      # fully static binary (glibc + gc + pthread, no dynamic linker at all).
      # Darwin does NOT: libSystem is always dynamic (platform convention),
      # and `-static` is not supported the same way there. Only gc is static
      # on Darwin.
      monad = monadFor (
        {
          gc = gcStatic;
          gcLink = "${lib.getLib gcStatic}/lib/libgc.a";
        }
        // lib.optionalAttrs (!pkgs.stdenv.hostPlatform.isDarwin) {
          linkFlags = " -static";
        }
      );

      # A cross target: the same three commands, with llc told the triple the
      # IR is FOR -- rung 1's header says this machine's, because that is where
      # it was interpreted -- and a `clang` shim standing in for the target's
      # own cc.
      #
      # The gc flags have to be ARGV in the shim and not environment in the
      # phase: nixpkgs' wrapped cross cc overwrites `LIBRARY_PATH` and drops a
      # hand-set `NIX_LDFLAGS`, so `-lgc` never reaches its linker -- measured,
      # as a compile that succeeds and a link that fails, which reads as a gc
      # bug. The shim reaches the INSTALLED compiler too and not only the phase
      # that linked it: `llvm/src/link.mo` calls bare `clang` for a user's
      # build as well.
      #
      # `checkPhase` runs what it built, which is all a cross leg can honestly
      # claim: `checks.bootstrap`'s ladder costs ~20 minutes natively and hours
      # under emulation, so the ladder stays native and a cross target has to
      # be shown to RUN -- and to allocate, because a mis-detected cross
      # collector fails at run time rather than at build time.
      crossMonadFor =
        {
          crossPkgs,
          triple,
          llcFlags,
        }:
        let
          gc = crossPkgs.boehmgc.override { enableStatic = true; };
          # The cross cc wrapper drops a hand-set NIX_LDFLAGS, so the target
          # libc's `-static` archives reach the link as argv, like gc's.
          glibcStatic = crossPkgs.glibc.static;
          # `-L` of those archives only when `-static` is on the line. An
          # unconditional one sits ahead of the cc's own libc dir in the
          # `-L` order, and ld then resolves a DYNAMIC link's `-lc` from the
          # static-only dir too (`-Bdynamic` accepts a `.a` that is the only
          # match in the first dir searched): every user program the
          # compiler links -- the qemu allocprobe included, which is how
          # this was measured -- came out with static glibc inside a
          # dynamic binary and died on SIGSEGV.
          shim = pkgs.writeShellScriptBin "clang" ''
            staticFlags=""
            for arg in "$@"; do
              if [ "$arg" = "-static" ]; then
                staticFlags="-L${glibcStatic}/lib"
              fi
            done
            exec ${crossPkgs.stdenv.cc}/bin/${crossPkgs.stdenv.cc.targetPrefix}cc \
              -isystem ${lib.getDev gc}/include \
              -L${lib.getLib gc}/lib \
              $staticFlags \
              "$@"
          '';
          # qemu, which is the CROSS platform's `emulator` applied to the
          # NATIVE pkgs. Applied to the cross set it answers nixpkgs' binfmt
          # wrapper instead -- correct on a machine with binfmt_misc, and
          # unusable in a sandbox.
          emulator = crossPkgs.stdenv.hostPlatform.emulator pkgs;
        in
        monadFor {
          inherit gc llcFlags glibcStatic;
          gcLink = "${lib.getLib gc}/lib/libgc.a";
          linkFlags = " -static";
          ccPath = "${shim}/bin";
          checkPhase = ''
            runHook preCheck

            # The target's own `clang`, which is what the binary below calls
            # when it compiles a program's runtime and links it.
            export PATH=${shim}/bin:$PATH

            # `--target` is spelled out because this binary runs somewhere
            # else: it probes `clang -dumpmachine` for its native triple, and
            # under qemu that probe still answers for the x86_64 host.
            cat > allocprobe.mo <<'EOF'
            #![mote { name := "allocprobe", deps := [init] }]

            open IO {println}

            #[decreasing n]
            def grow (n : I64) (s : String) : String :=
                if I64.lt n 1 then s else grow (n - 1) (s ++ "xxxxxxxxxxxxxxxxxxxx")

            def main (args : List String) : IO Unit :=
                println (grow 3000 "allocprobe-ok")
            EOF

            ${emulator} "$PWD/monad" build allocprobe.mo --target ${triple} -o "$PWD/allocprobe"

            # Asserted on stdout and not on the exit status, which has been
            # both 0 and non-zero for a program that succeeded; a crash leaves
            # the marker missing, and that is the claim being made.
            ${emulator} "$PWD/allocprobe" > allocprobe.out || true
            grep -q '^allocprobe-ok' allocprobe.out
            # 3000 appends of 20 bytes, so a heap that is not being collected
            # to completion -- or a recursion that did not run to completion --
            # cannot reach this.
            test "$(wc -c < allocprobe.out)" -gt 60000

            runHook postCheck
          '';
        };

      # The aarch64-linux output: cross-built here, published by the nightly.
      # Nothing in this flake runs on aarch64-linux, which is why it is an
      # output of x86_64-linux rather than a flake system.
      monadAarch64Linux = crossMonadFor {
        crossPkgs = pkgs.pkgsCross.aarch64-multiplatform;
        triple = "aarch64-unknown-linux-gnu";
        llcFlags = " -mtriple=aarch64-unknown-linux-gnu";
      };

      # The riscv64-linux output, published as experimental: it is the one
      # target whose toolchain needs more than a triple told to llc, and these
      # are exactly `llvm/src/target.mo`'s riscv64 entry. The duplication is not
      # avoidable -- this relink drives llc directly and cannot read the
      # compiler's table -- and it is silent when it drifts, so the entry there
      # records when each part was measured.
      #
      #   * llc spells the triple differently from clang and from the sysroot,
      #     and REJECTS their `riscv64gc-...` with "unable to get target for".
      #   * no spelling selects the hard-float ABI, and llc's default is
      #     soft-float, so lp64d has to be asked for.
      #   * nixpkgs' riscv64 cc links PIE where llc's default is non-PIC, and
      #     the object then dies at the link with `relocation R_RISCV_HI20 ...
      #     recompile with -fPIC`.
      monadRiscv64Linux = crossMonadFor {
        crossPkgs = pkgs.pkgsCross.riscv64;
        triple = "riscv64gc-unknown-linux-gnu";
        llcFlags = " -mtriple=riscv64-unknown-linux-gnu -mattr=+m,+a,+f,+d,+c -target-abi=lp64d -relocation-model=pic";
      };

      # ── monadup ────────────────────────────────────────────────────────
      #
      # The compiler emits monadup's IR ONCE (natively) from the commit-free
      # rung-1 compiler; every published platform relinks that same `.ll`.
      # Using `monadRung1` rather than the stamped `monad` keeps this
      # derivation's hash off the per-commit revision: the emitted IR does
      # not depend on the stamp, and keying on it made every compiler change
      # rebuild the ~26-minute interpretation. The header's triple is
      # overridden by `llc -mtriple` (measured for the compiler's own rung-1
      # relink), so one interpretation serves all four platforms. The relink
      # is `monadFor`'s shape without the makeWrapper: a consumer downloads
      # the bare binary, not a store wrapper.
      monadupIr = pkgs.stdenv.mkDerivation {
        pname = "monadup-ir";
        version = monadVersion;
        src = monadupSrc;
        nativeBuildInputs = [ config.packages.monadRung1 pkgs.llvm pkgs.clang pkgs.coreutils pkgs.bash ];
        buildPhase = ''
          runHook preBuild
          export MONAD_ROOT="$PWD"
          export MONAD_TARGET_DIR="$TMPDIR/monad-target"
          ${lib.getExe config.packages.monadRung1} build motes/monadup --bin monadup \
            --release --no-cache -o "$PWD/monadup"
          test -f "$PWD/monadup.ll"
          runHook postBuild
        '';
        installPhase = ''
          runHook preInstall
          install -Dm644 "$PWD/monadup.ll" $out/share/monadup/monadup.ll
          runHook postInstall
        '';
        meta = {
          description = "monadup's emitted IR";
          homepage = "https://monad-lang.org";
          license = lib.licenses.asl20;
        };
      };

      monadupCrossShim =
        { crossPkgs, gc, glibcStatic }:
        pkgs.writeShellScriptBin "clang" ''
          staticFlags=""
          for arg in "$@"; do
            if [ "$arg" = "-static" ]; then staticFlags="-L${glibcStatic}/lib"; fi
          done
          exec ${crossPkgs.stdenv.cc}/bin/${crossPkgs.stdenv.cc.targetPrefix}cc \
            -isystem ${lib.getDev gc}/include \
            -L${lib.getLib gc}/lib \
            $staticFlags \
            "$@"
        '';

      monadupFor =
        {
          gc,
          gcLink,
          glibcStatic ? pkgs.glibc.static,
          llcFlags ? "",
          ccPath ? null,
          linkFlags ? "",
          checkPhase ? null,
        }:
        pkgs.stdenv.mkDerivation (
          {
            pname = "monadup";
            version = monadVersion;
            src = monadupSrc;
            nativeBuildInputs = [
              pkgs.llvm
              pkgs.clang
              pkgs.lld
              pkgs.coreutils
              pkgs.bash
              pkgs.gnugrep
            ];
            buildInputs = [ gc ] ++ lib.optionals (linkFlags != "") [ glibcStatic ];
            buildPhase = ''
              runHook preBuild
              ${lib.optionalString (ccPath != null) "export PATH=${ccPath}:$PATH\n"}install -Dm644 ${monadupIr}/share/monadup/monadup.ll "$PWD/monadup.ll"
              llc -filetype=obj${llcFlags} "$PWD/monadup.ll" -o "$PWD/monadup.o"
              clang -pthread -c runtime/src/runtime.c \
                "-DMONAD_BUILD_COMMIT=\"${commit}\"" \
                -o "$PWD/monadup_runtime.o"
              clang${linkFlags} -pthread "$PWD/monadup.o" "$PWD/monadup_runtime.o" ${gcLink} -o "$PWD/monadup"
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              install -Dm755 "$PWD/monadup" $out/bin/monadup
              runHook postInstall
            '';
            meta = {
              description = "Manage Monad nightly toolchains";
              homepage = "https://monad-lang.org";
              license = lib.licenses.asl20;
              mainProgram = "monadup";
            };
          }
          // lib.optionalAttrs (checkPhase != null) {
            doCheck = true;
            inherit checkPhase;
          }
        );

      monadup = monadupFor {
        gc = gcStatic;
        gcLink = "${lib.getLib gcStatic}/lib/libgc.a";
        linkFlags = lib.optionalString (!pkgs.stdenv.hostPlatform.isDarwin) " -static";
        checkPhase = ''
          runHook preCheck
          "$PWD/monadup" --version | grep -q '^monadup '
          runHook postCheck
        '';
      };

      monadupAarch64Linux =
        let
          crossPkgs = pkgs.pkgsCross.aarch64-multiplatform;
          gc = crossPkgs.boehmgc.override { enableStatic = true; };
          glibcStatic = crossPkgs.glibc.static;
          shim = monadupCrossShim { inherit crossPkgs gc glibcStatic; };
          emulator = crossPkgs.stdenv.hostPlatform.emulator pkgs;
        in
        monadupFor {
          inherit gc glibcStatic;
          gcLink = "${lib.getLib gc}/lib/libgc.a";
          llcFlags = " -mtriple=aarch64-unknown-linux-gnu";
          ccPath = "${shim}/bin";
          linkFlags = " -static";
          checkPhase = ''
            runHook preCheck
            ${emulator} "$PWD/monadup" --version | grep -q '^monadup '
            runHook postCheck
          '';
        };

      monadupRiscv64Linux =
        let
          crossPkgs = pkgs.pkgsCross.riscv64;
          gc = crossPkgs.boehmgc.override { enableStatic = true; };
          glibcStatic = crossPkgs.glibc.static;
          shim = monadupCrossShim { inherit crossPkgs gc glibcStatic; };
          emulator = crossPkgs.stdenv.hostPlatform.emulator pkgs;
        in
        monadupFor {
          inherit gc glibcStatic;
          gcLink = "${lib.getLib gc}/lib/libgc.a";
          llcFlags = " -mtriple=riscv64-unknown-linux-gnu -mattr=+m,+a,+f,+d,+c -target-abi=lp64d -relocation-model=pic";
          ccPath = "${shim}/bin";
          linkFlags = " -static";
          checkPhase = ''
            runHook preCheck
            ${emulator} "$PWD/monadup" --version | grep -q '^monadup '
            runHook postCheck
          '';
        };

      # `nix run .#monad`; the same program under two names, because
      # `apps.default` is what a bare `nix run` resolves and the named one is
      # what the flake's own documentation and CI use.
      app = {
        type = "app";
        program = "${monad}/bin/monad";
      };
    in
    {
      packages = {
        monad = monad;
        default = monad;
        # Rung 1 on its own, for CI's bootstrap ladder: it is what makes the
        # interpretation a store hit across commits that do not touch the
        # compiler's sources, and it is where the `.ll` that ladder compares
        # against now comes from.
        monadRung1 = rung1;
        monadup = monadup;
      }
      // lib.optionalAttrs (pkgs.stdenv.hostPlatform.system == "x86_64-linux") {
        # Named for the platform they are FOR, which is not one this flake
        # declares: they are cross-built, so they belong to the system that
        # builds them, and to that system alone.
        monad-aarch64-linux = monadAarch64Linux;
        monad-riscv64-linux = monadRiscv64Linux;
        monadup-aarch64-linux = monadupAarch64Linux;
        monadup-riscv64-linux = monadupRiscv64Linux;
      };

      apps.monad = app;
      apps.monadup = {
        type = "app";
        program = "${monadup}/bin/monadup";
      };
      apps.default = app;
    };
}
