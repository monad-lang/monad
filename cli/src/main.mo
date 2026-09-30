use std::list {List.length}
open IO {println, read_file, write_file, file_exists}
use std::process {exec_cmd, process_id}
use std::bench {Bench.now, Bench.report_since}
use lang::types {
  Decl, LocalScope, ModulePath, NamePath, id, show_identifier, show_module_path,
}
use llvm::ir {LLVMModule, emit_module}
use llvm::link {link_ir}
use llvm::target {TargetSpec}
use runtime {}
use lang::codegen::emit {compile_db_module_with_debug, compile_loaded_modules_to_ir_with_debug}
use lang::module {ElaboratedAndCache, collect_link_libs, get_loaded_all, ElaboratedModules, FileCheckAndCache, LoadedModules, ModuleInfo, ModuleInfoCache, bench_step, check_file_cached, check_file_cached_affine, check_module_with_scope, elaborate_loaded_modules, elaborate_loaded_modules_cached, elaborate_module_decls_best_effort, expand_check_paths, extract_directory, load_file_modules, load_module_with_info, module_name_from_path, module_info_cache_empty, resolve_runtime_src, try_parse_decls, try_parse_decls_strict}
use lang::scope {resolve_class_calls_decls}
use lang::mote {
  Mote.discover, Mote.discover_config_target_dir, Mote.target_roots,
  Mote.workspace_members, MoteManifest, BinTarget,
}
use build::closure {Build.input_hash}
use build::store {
  Build.artifact_ir_path, Build.ensure_dir, Build.ensure_entry_dir,
  Build.store_path, Build.target_dir_at, Build.target_dir_for,
  Build.target_dir_of, artifact,
}
use build::check {
  Build.check_block, Build.check_entry_read, Build.check_maybe_write,
  Build.check_plan, Build.check_plan_active, Build.check_plan_key,
  Build.check_plan_reason, Build.check_plan_root, Build.mote_root_of, CheckPlan,
}
use build::manage {
  Build.clean_run, Build.gc_run, Build.store_ls, Build.store_verify,
}
use std::map {}
use lang::pretty {show_decls}
use lang::codegen::test_driver {compile_loaded_modules_to_test_ir, is_no_tests_error, parse_driver_result}
use clap::args {*}
// `--verbose` stage/module trace and the colored finish/failure lines
// (`std/src/log.mo` -- its own header documents the gating rules).
use std::log {fail_line, ok_line, stage}
use lang::lower_core_ir {lower_ctx_from_decls, lower_root, LowerError}
use lang::core_ir {CoreIr}
use lang::core_eval {eval, basic_native_table}
use lang::core_value {GlobalTable, env_nil, global_cache_new, global_table_len}
use lang::typecheck::meta_eval {show_value_debug, show_core_eval_error_debug}
// The language server. It is a dependency of the BINARY and not of the
// library: `lsp_serve` is a whole program that talks on stdin/stdout, so
// nothing outside `main`'s `lsp` arm may reach it -- an editor's protocol
// stream and a compiler's diagnostic stream are the same two file
// descriptors, and `lsp_serve` returning means the session is over.
use lsp::server {lsp_serve}

#[native "build_commit"]
def build_commit : String
/// The default output directory for `compile`/`test` when no `--output`/
/// positional name supplies an absolute one. Includes the process ID so
/// parallel invocations (e.g. two `bootstrap test` runs, or `cargo test`
/// threads) don't collide on the same `/tmp/monad_test_bin_<N>` or output
/// binary paths.
def default_output_dir : Path := Path.path ("/tmp/monad_out_" ++ I64.to_string process_id)

/// `compile_loaded_modules_to_ir` can now fail cleanly -- either
/// `resolve_class_calls_decls` found a `ClassName.method` call with no
/// available instance, or `validate_no_unwired_natives` found a reachable
/// bodyless `#[native X]` def wired nowhere (both: see their own doc
/// comments in `lang.codegen.emit`) -- instead of only ever succeeding.
/// Report that failure the same way a typecheck failure already is
/// (`FAILED at stage: ...`) rather than proceeding to
/// `emit_module`/`link_ir` with no module to link. The error message
/// itself already names the exact def at fault, so a generic stage label
/// is enough here (the `--verbose` compile pipeline prints the precise
/// stage names too).
#[partial]
def link_compiled_module (mod_result : Result String LLVMModule) (link_libs : List String) (base_dir : String) (output_dir : Path) (output_name : Path) (ir : Option Path) (verbose : Bool) (target : TargetSpec) : IO I64 :=
    match mod_result {
        Result.err e => do {
            println ("FAILED at stage: compile_loaded_modules_to_ir (" ++ e ++ ")");
            return 1
        },
        Result.ok mod_ => do {
            // `emit_module` -- rendering the whole `LLVMModule` to `.ll` text --
            // was the largest untimed span in the pipeline: it sits between
            // `compile_loaded_modules_to_ir`'s own total and `link_ir`'s first
            // span, so a `--verbose` self-compile reported 52189ms of its
            // 275424ms nowhere at all (19%). `String.length` forces the
            // rendered text inside the span, the same `forced`-argument trick
            // `bench_step`'s own doc comment describes.
            let t_emit : I64 <- Bench.now;
            let ir_text : String := emit_module mod_;
            let _t_emit : I64 <- bench_step verbose "emit_module (render .ll)" t_emit (String.length ir_text);
            let runtime_src : String <- resolve_runtime_src base_dir;
            link_ir { runtime_c := runtime_src, ir_text := ir_text,
                ir_path := resolve_ir_path ir output_dir output_name,
                output_dir := output_dir, output_name := output_name,
                link_libs := link_libs, compiler_commit := build_commit,
                verbose := verbose, spec := target }
        },
    }

/// Parse a source file and compile + run it via LLVM. `source_path` is
/// the DWARF debug-info input (the `.mo` file debug info is being
/// generated for, from the `Term.ctx` wrappers on each def's body) --
/// pass `Option.none` to disable, same as
/// `compile_db_module_with_debug` itself. `link_ir` needs no
/// separate `--debug` flag of its own: `llc`/`clang` pick up whatever
/// debug metadata `emit_module` already wrote into `ir_text` with no
/// extra flag required (confirmed directly -- a `-g`-style flag doesn't
/// exist on `llc`, unlike `clang`'s own C-source `-g`).
#[partial]
def compile_parsed_decls (decl_list : List Decl) (base_dir : String) (output_dir : Path) (output_name : Path) (ir : Option Path) (verbose: Bool) (source_path : Option String) (target : TargetSpec) : IO I64 {
    let mod_ : LLVMModule := compile_db_module_with_debug decl_list source_path List.empty target.triple;
    let ir_text := emit_module mod_;
    let ir_path : Path := resolve_ir_path ir output_dir output_name;
    // This is the module-loading-FAILURE fallback: there is no
    // `LoadedModules`, so no manifest closure to read `[link] libs`
    // from. A program that needs `-l` flags cannot reach here anyway --
    // its `use` lines are what failed to load.
    println <| "Writing LLVM IR to: " ++ Path.to_string ir_path;
    let runtime_src : String <- resolve_runtime_src base_dir;
    link_ir { runtime_c := runtime_src, ir_text := ir_text, ir_path := ir_path,
        output_dir := output_dir, output_name := output_name,
        link_libs := List.empty, compiler_commit := build_commit,
        verbose := verbose, spec := target }
}

// (The v1 per-def location table this section used to build --
// `no_debug_info`/`debug_info_for_source`, fed by a second read of the
// target file -- is gone: since stage 6 a function's own location is the
// `Term.ctx` wrapper on its body.
//
// `with_located_decls`/`locate_module_info`/`locate_module_infos` are gone
// too, along with `mk_loaded_modules`/`mk_module_info`, which existed only
// to rebuild what they replaced. `parse_all_decls` (`lang/module.mo`) now
// locates on EVERY path, so the wrappers are already there by the time any
// command has a `LoadedModules` -- there is nothing left to swap in, and
// `--debug` no longer re-reads and re-parses the whole dependency graph to
// get them. That second parse was 76029ms of a 172143ms debug self-compile;
// it is now simply absent.)

/// The output name a mote's `[[bin]]` target is built as, given what the
/// caller asked for. Split out of `build_target` because a `let … in`
/// inside a do-block does not parse (see that def), and this is the
/// value it needs there.
///
/// `"source"` is the literal `Command.from_args` substitutes when
/// neither `-o`/`--output` nor a positional name was given; anything
/// else is the caller's own choice, which always wins.
///
/// `BinTarget.name` is always there -- an entry that declares no name
/// defaults to the mote's own -- so `module_name_from_path`'s
/// source-stem rule (`cli/src/main.mo` -> `main`) is now reached only by
/// a FILE compile, which has no manifest to ask. A mote whose single
/// target declares no name therefore produces the MOTE's name rather than
/// the source stem, which is the point of §2a's "defaults to the mote
/// name".
def compile_out_name (requested : String) (target : BinTarget) : String :=
    if Bool.not (String.beq requested "source") then requested
    else BinTarget.target_name target

/// `monad build [<path>]` with a mote-aware path. The one build verb --
/// `monad compile` was removed rather than kept as an alias, because two
/// verbs that both produce a binary differ only in which one you
/// remember.
///
/// Three input forms, one mechanism. A FILE compiles directly. A
/// DIRECTORY is read as a mote and one of its `[[bin]]` targets decides
/// what is built -- `monad build cli` from the workspace root, or
/// `monad build .` from inside `cli/`, builds `cli/src/main.mo` as
/// `monad`, which is what `cli/mote.toml`'s `[[bin]] path`/`[[bin]] name`
/// declare that binary to be. `--bin <name>` picks between several.
/// NO path is the third, and it is just `.`: `Command.from_args` supplies
/// it, so the mote containing the working directory gets built, matching
/// `check`/`test`'s own "with no paths" default instead of printing usage.
///
/// A target's `path` arrives already joined onto the mote's own `dir`
/// (`Mote.bin_target_of`), so it is a path relative to the working
/// directory exactly as stored -- which is what `compile_file` wants,
/// and what makes `monad build cli` work from the workspace root.
///
/// A directory that is not a mote, or one whose targets do not
/// distinguish themselves, is an error rather than a guess -- and the
/// guess this rules out is subtler than it used to be. `MoteManifest.bins`
/// supplies a CONVENTIONAL target (`src/main.mo`, named after the mote)
/// for a manifest that declares no bin table, so "declares no `[[bin]]`" is
/// no longer the same question as "has nothing to build". Both are
/// answered by the same test: a target is built only if its file exists.
/// A library mote -- `lang`, `std`, `llvm`, `init`, `runtime` -- declares
/// no `[[bin]]` and has no `src/main.mo`, so `monad build lang` still
/// refuses, and it refuses for the reason that is actually true.
#[partial]
/// `debug` or `release`, the two artifacts of one source tree that must
/// never share a cache entry.
def profile_name (debug : Bool) : String := if debug then "debug" else "release"

/// Build `src`, consulting the artifact store first.
///
/// A hit copies the stored binary to the destination and skips the
/// compile entirely. A miss builds and then stores, so the next identical
/// build is a hit.
///
/// When no SAFE key can be computed -- no digest tool, or no readable
/// `/proc/<pid>/exe` to identify this compiler -- the cache turns itself
/// OFF and the build proceeds normally. That is the rule the whole design
/// hangs on: a weaker key would serve a stale binary, and a stale binary
/// is worse than a slow build.
///
/// The caller's escape hatch (`--no-cache`, `MONAD_NO_CACHE`) means the
/// store is neither read nor written: a caller reaching for it is settling
/// a suspicion about a stored entry, so recording a new one from the run
/// it asked to be clean is the one thing it did not ask for. It is NOT,
/// however, checked before the key: the key is what names the intermediate
/// `.ll`, and the IR name is recorded inside the artifact, so a hatch build
/// that skipped the key would produce a byte-different binary from the
/// cached build it is supposed to be checking. See `resolve_ir_path`. (It
/// did use to come first, to spare a caller who declined the cache the cost
/// of a digest. One `sha256sum` fork against a compile of tens of seconds
/// is the cheaper side of that trade, and byte-comparability is the whole
/// value of the hatch.)
///
/// A platform with no procfs has no key to compute at all; the hatch still
/// works there, because "cannot name the IR by a key" is `Option.none` and
/// not a refusal to build.
///
/// Both of the things it needs -- which mote owns `src`, and which
/// directory that mote's store is under -- are `build`'s to answer
/// (`Build.mote_root_of`, `Build.target_dir_for`), because the `check`
/// and `test` caches need the identical answers and a second copy of
/// either rule is a second place for it to drift.
#[partial]
def build_cached (src : String) (dest_name : Path) (verbose : Bool) (debug : Bool) (no_cache : Bool) (target : TargetSpec) : IO I64 := do {
    // Resolved either way: it is where the binary lands, not a cache
    // decision.
    let target_dir <- Build.target_dir_for src;
    let dest_dir : String := build_dest_dir target_dir debug;
    let root <- Build.mote_root_of src;
    // The target is in the key, so a native aarch64 or darwin build cannot be
    // served an x86_64 artifact. `target.triple` is a `clang -dumpmachine`
    // probe, not the constant it replaced, so the key moves with PATH.
    let key <- Build.input_hash src root (profile_name debug) target.triple;
    // The key names the IR, so it is resolved from the key, and a key that
    // could not be taken leaves the IR where it always was (beside the
    // output). That is the ONLY case where a `build` puts `-o` inside the
    // artifact, and it is the case the cache has already declined to serve
    // -- so nothing stored can ever disagree with it.
    let ir : Option Path := match key {
        Result.ok h => Option.some (Path.path (Build.artifact_ir_path target_dir h)),
        Result.err _ => Option.none,
    };
    let enabled <- cache_enabled no_cache;
    if Bool.not enabled
    then do {
        stage verbose "cache off: MONAD_NO_CACHE (or --no-cache) is set";
        compile_file { file_path := src, output_dir := (Path.path dest_dir),
            output_name := dest_name, ir := ir, verbose := verbose,
            debug := debug, target := target }
    }
    else match key {
        Result.err m => do {
            stage verbose ("cache off: " ++ m);
            compile_file { file_path := src, output_dir := (Path.path dest_dir),
            output_name := dest_name, ir := ir, verbose := verbose,
            debug := debug, target := target }
        },
        Result.ok h => build_cached_keyed { src := src, target_dir := target_dir,
            h := h, ir := ir, dest_name := dest_name, verbose := verbose,
            debug := debug, target := target }
    }
}

/// The IR path to hand `llvm.link.link_ir`, given the caller's optional
/// key-derived one.
///
/// `Option.some` is a caller that HAS a cache key, and therefore a
/// standard, key-derived IR path (`Build.artifact_ir_path`); it is passed
/// through untouched, because the entire point is that the file `llc`
/// reads is named by the key rather than by the output.
///
/// `Option.none` is every caller with no key to name one by -- `run`, the
/// test driver, and a `build` whose compiler digest could not be taken --
/// and it falls back to the output-derived `<dest>.ll`, which is the
/// behaviour all of them had before this became a parameter. That fallback
/// is precisely what a cached build must NOT do: it puts the user's `-o`
/// into the artifact, by way of the filename `llc` records in the object
/// it emits. See `Build.artifact_ir_path` for the one-byte measurement
/// that makes this a correctness requirement rather than tidiness.
def resolve_ir_path (ir : Option Path) (output_dir : Path) (output_name : Path) : Path :=
    match ir {
        Option.some p => p,
        Option.none => Path.with_suffix (Path.join output_dir output_name) ".ll",
    }

/// `<target-dir>/<profile>` -- where a binary lands when the caller did
/// not name an absolute path.
///
/// This replaces `/tmp/monad_out_<pid>` as the DEFAULT only. An absolute
/// `-o` still wins outright, because `link_ir` joins with `Path.join` and
/// an absolute name replaces the directory -- which is what every ladder
/// script relies on (`self-compile-turn.sh`, `build-self-hosted.sh` and
/// `check-external-mote.sh` all pass absolute `-o` paths), so none of
/// them change behaviour.
def build_dest_dir (target_dir : String) (debug : Bool) : String :=
    String.concat target_dir (String.concat "/" (profile_name debug))

/// A HIT leaves the destination exactly as a MISS would -- binary AND IR.
///
/// The store holds the IR (`Build.artifact_ir_path`) because that is the
/// file `llc` read to make the artifact, so it is meaningful to replay
/// beside the binary, where the miss path's convenience copy lands. Two
/// callers read that file rather than the binary: the ladder
/// (`scripts/self-compile-turn.sh` promises `<out-dir>/<name>.ll`, and
/// `scripts/bootstrap-compile.sh` `cmp`s it against the previous rung's)
/// and `tools/debug_transparency_oracle.sh`. Without this a warm store made
/// the ladder fail on a missing file -- and, worse, made its rung vacuous.
/// Restoring it is also the honest reading of what the cache claims: the
/// entry is valid for the source AND the compiler digest it was keyed on,
/// so recompiling to re-derive a file already recorded is work the key has
/// proved unnecessary.
///
/// `cmp -s` first, so a hit does not rewrite a file that already holds the
/// right bytes -- `cp` would move its mtime, and "the `.ll` did not move" is
/// how a reader tells a hit from a miss (`target-monad/verify/escape_hatch.sh`
/// prints it as one of three signals). Nothing depends on it for
/// correctness: the ladder `cmp`s content. `cmp` is POSIX, so unlike the
/// digest tool of Phase 0c it needs no probe.
///
/// An entry whose IR has gone is a no-op, not an error. The cache is a
/// cache; a missing convenience copy costs a reader one `monad build`.
def replay_ir_beside (ir : Option Path) (dest : String) : IO Unit :=
    match ir {
        Option.none => return unit,
        Option.some p => do {
            let store_ir : String := Path.to_string p;
            let beside : String := String.concat dest ".ll";
            if String.beq store_ir beside
            then return unit
            else do {
                let stored <- IO.file_exists (Path.path store_ir);
                let have <- IO.file_exists (Path.path beside);
                if stored
                then do {
                    let same : I64 <- if have then exec_cmd "cmp" ["-s", store_ir, beside] else return 1;
                    if same == 0
                    then return unit
                    else do {
                        let _c <- exec_cmd "cp" ["-f", store_ir, beside];
                        return unit
                    }
                }
                else return unit
            }
        },
    }

#[partial]
def build_cached_keyed (src : String) (target_dir : String) (h : String) (ir : Option Path) (dest_name : Path) (verbose : Bool) (debug : Bool) (target : TargetSpec) : IO I64 := do {
    let dest_dir : String := build_dest_dir target_dir debug;
    let dest : String := Path.to_string (Path.join (Path.path dest_dir) dest_name);
    // No slug. It used to be the output's bare name, which made the name an
    // INPUT: a build under `-o a` could not share with the same build under
    // `-o b`, so one unchanged source compiled twice. The name reached the
    // artifact through the intermediate `.ll` -- named after the output, and
    // recorded by `llc` in the object it emits. Now the IR is keyed
    // (`Build.artifact_ir_path`), so the artifact is a function of the key
    // alone and the entry can be named by the key alone. The human-readable
    // half belongs in `db/<hash>.json`, the metadata kind the plan's layout
    // reserves for it.
    let entry : String := Build.store_path target_dir Entry.artifact h "";
    let hit <- IO.file_exists (Path.path entry);
    if hit
    then do {
        // `Path.parent dest`, not `dest_dir`: `-o sub/hello` nests, and the
        // MISS path gets that directory from `link_ir`'s own mkdir while a
        // hit has to make it here. Without it `cp` fails and the run still
        // prints `cached:` -- a success line over a failing exit code.
        let parent : String := Path.parent (Path.path dest);
        let _mk <- (if String.beq parent "" then return 0 else exec_cmd "mkdir" ["-p", parent]);
        let rc <- exec_cmd "cp" ["-f", entry, dest];
        let _ir <- replay_ir_beside ir dest;
        ok_line ("cached: " ++ dest ++ " (" ++ h ++ ")");
        return rc
    }
    else do {
        let rc <- compile_file { file_path := src,
            output_dir := (Path.path dest_dir), output_name := dest_name,
            ir := ir, verbose := verbose, debug := debug, target := target };
        if rc == 0
        then do {
            let _d <- Build.ensure_entry_dir target_dir Entry.artifact;
            // Temp then rename, with the status CHECKED. `cp -f` straight to
            // `entry` leaves a truncated file when it dies (an interrupt, a
            // full disk), and the hit test is a bare `file_exists` -- so a
            // stump would be served as a hit, printing `cached:` over a
            // binary that is not the one this key names. `mv` inside the
            // store directory is the atomic step that lets an entry appear
            // complete or not at all.
            let tmp : String := entry ++ ".tmp";
            let wrc <- exec_cmd "cp" ["-f", dest, tmp];
            if wrc == 0
            then do {
                let _m <- exec_cmd "mv" ["-f", tmp, entry];
                return rc
            }
            else do {
                let _r <- exec_cmd "rm" ["-f", tmp];
                return wrc
            }
        }
        else return rc
    }
}

/// The declared target whose `name` is `wanted`, or `none`. Linear rather
/// than `List.filter` because this file has no `Option`-returning finder,
/// and a name is unique by convention anyway.
def bin_named (bs : List BinTarget) (wanted : String) : Option BinTarget :=
    match bs {
        List.empty => Option.none,
        List.cons b rest =>
            if String.beq (BinTarget.target_name b) wanted
            then Option.some b
            else bin_named rest wanted
    }

/// The targets whose files actually EXIST, in declaration order, appended
/// onto `acc`. This is the half `MoteManifest.bins` cannot do: the parser
/// is pure, so it records where a target would be, and this asks the
/// filesystem.
def existing_bin_targets (bs : List BinTarget) (acc : List BinTarget) : IO (List BinTarget) := do {
    match bs {
        List.empty => do { return acc },
        List.cons b rest => do {
            let there <- IO.file_exists (Path.path (BinTarget.target_path b));
            if there
            then existing_bin_targets rest (List.append acc (List.cons b List.empty))
            else existing_bin_targets rest acc
        }
    }
}

/// The targets' names, comma-separated, for an error that has to say what
/// it found rather than only that it failed.
def bin_names_joined (bs : List BinTarget) : String :=
    match bs {
        List.empty => "",
        List.cons b rest =>
            if List.is_empty rest
            then BinTarget.target_name b
            else String.concat (BinTarget.target_name b) (String.concat ", " (bin_names_joined rest))
    }

/// Which target a `monad build <mote>` builds, or the message saying why
/// there is not exactly one.
///
/// `--bin <name>` selects by name, and the named target is checked against
/// the filesystem too -- a name that matches nothing, and a name that
/// matches a file that is not there, are different errors and both are
/// errors. With no flag the rule is "exactly ONE target exists": zero is a
/// library mote (or a binary mote whose declared file has gone missing),
/// and several need `--bin` to say which.
///
/// Nothing here builds a file that is not on disk, which is what keeps the
/// conventional `src/main.mo` default honest -- see `build_target`'s own
/// comment.
def choose_bin_target (manifest : MoteManifest) (path : String) (wanted : String) : IO (Result String BinTarget) := do {
    if Bool.not (String.is_empty wanted) then do {
        match bin_named manifest.bins wanted {
            Option.none => do {
                return (Result.err (String.concat_all [
                    "error: mote `", manifest.name, "` declares no [[bin]] target named `", wanted, "`",
                    "\n  declared: ", bin_names_joined manifest.bins,
                    "\nhint: `monad build ", path, " --bin <name>` names one of those",
                ]))
            },
            Option.some b => do {
                let there <- IO.file_exists (Path.path (BinTarget.target_path b));
                if there then do { return (Result.ok b) }
                else do {
                    return (Result.err (String.concat_all [
                        "error: mote `", manifest.name, "`'s [[bin]] target `", wanted, "` names a file that is not there",
                        "\n  ", BinTarget.target_path b,
                        "\nhint: create it, or fix `path` in ", path, "/mote.toml",
                    ]))
                }
            }
        }
    }
    else do {
        let existing <- existing_bin_targets manifest.bins List.empty;
        match existing {
            List.empty => do {
                // Unreachable while `Mote.bin_targets` always conses a target
                // (even `bin = []` falls through to the default); kept as
                // defence, since the fallback below reads badly without it.
                let declared : String := bin_names_joined manifest.bins;
                let named : String :=
                    if String.is_empty declared
                    then "declares no [[bin]] table"
                    else String.concat "names " declared;
                return (Result.err (String.concat_all [
                    "error: mote `", manifest.name, "` has no [[bin]] target to build",
                    "\n  it ", named, ", and none of those files exist",
                    "\nhint: a library mote needs no [[bin]] table -- `monad build <path>",
                    "/src/<file>.mo` still builds one file directly",
                ]))
            },
            List.cons b rest => do {
                if List.is_empty rest then do { return (Result.ok b) }
                else do {
                    return (Result.err (String.concat_all [
                        "error: mote `", manifest.name, "` has several [[bin]] targets that exist and no way to pick",
                        "\n  buildable: ", bin_names_joined existing,
                        "\nhint: `monad build ", path, " --bin <name>` picks one",
                    ]))
                }
            }
        }
    }
}

def build_target (path : String) (out_name : String) (bin : String) (verbose : Bool) (debug : Bool) (no_cache : Bool) (spec : TargetSpec) : IO I64 := do {
    let is_a_dir : Bool <- IO.is_dir (Path.path path);
    if Bool.not is_a_dir
    then build_cached { src := path, dest_name := (Path.path out_name),
        verbose := verbose, debug := debug, no_cache := no_cache,
        target := spec }
    else do {
        let m <- Mote.discover path;
        match m {
            Option.none => do {
                println ("error: " ++ path ++ " is a directory, and no mote.toml was found in it or above it");
                println "hint: `monad build <file.mo>` builds a single file";
                return 1
            },
            Option.some manifest => do {
                let chosen <- choose_bin_target manifest path bin;
                match chosen {
                    Result.err msg => do {
                        println msg;
                        return 1
                    },
                    Result.ok target => do {
                        let src := BinTarget.target_path target;
                        let name : String := compile_out_name out_name target;
                        println (String.concat_all [
                            "building mote `", manifest.name, "`'s [[bin]] target `",
                            BinTarget.target_name target, "`: ", src,
                        ]);
                        build_cached { src := src,
                            dest_name := (Path.path name), verbose := verbose,
                            debug := debug, no_cache := no_cache, target := spec }
                    }
                }
            }
        }
    }
}

/// Parse a source file and compile + run it via LLVM. Stage 3 of
/// `bootstrapping/unify-check-compile-test-elaboration.md`: gates on the
/// target file itself actually type-checking cleanly (via
/// `elaborate_loaded_modules` + `check_module_with_scope`, the same
/// pipeline `check` uses) BEFORE attempting codegen at all -- previously
/// `compile` skipped type-checking entirely and went straight to codegen,
/// so a real type error in the program being compiled either silently
/// produced wrong LLVM IR or surfaced as an obscure link-time failure
/// instead of a real diagnostic. Scoped to the TARGET file only (not the
/// whole loaded dependency graph, `check_deps=false`) to match `check`'s
/// own existing semantics and avoid blocking every compile on an
/// unrelated, pre-existing gap somewhere in prelude/init — `check_deps=true`
/// exists (see `elaborate_loaded_modules`'s own doc comment) but is not
/// yet safe to default to anywhere: it caused unbounded memory growth
/// checking `cli/src/main.mo`'s own full closure, root cause under
/// investigation (`bootstrapping/check-deps-memory-blowup.md`).
/// `compile_loaded_modules_to_ir` (`lang.codegen.emit`) separately attempts
/// whole-graph elaboration on its own, with its own graceful fallback,
/// purely to improve codegen's own dictionary-dispatch resolution (see its
/// own doc comment) -- that is NOT a second copy of this gate.
#[partial]
def compile_file (file_path : String) (output_dir : Path) (output_name : Path) (ir : Option Path) (verbose : Bool) (debug : Bool) (target : TargetSpec) : IO I64 {
    // Checked HERE, before anything is printed: a missing input is not a
    // load failure to be recovered from, and reporting it as one
    // ("FAILED at stage: load (could not load dependencies: ...)") buries
    // the actual problem under a stage name. `compile_file_codegen` has
    // the same guard for its own direct callers.
    let input_exists : Bool <- file_exists (Path.path file_path);
    if not input_exists then do {
        println ("error: file not found: " ++ file_path);
        return 1
    } else do {
    let total_start : I64 <- Bench.now;
    println <| "compiling: " ++ file_path ++ " to " ++ Path.to_string (Path.join output_dir output_name);
    stage verbose "load + elaborate modules";
    let t_elaborate : I64 <- Bench.now;
    let elaborated_result <- elaborate_loaded_modules file_path false verbose;
    if verbose then do {
        Bench.report_since "elaborate_loaded_modules" t_elaborate;
        return unit
    } else return unit;
    match elaborated_result {
        Result.ok em =>
            do {
                    let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
                    stage verbose "typecheck target";
                    let t_check : I64 <- Bench.now;
                    let diags <- check_module_with_scope em.scope em.target_decls empty_locs (Option.some file_path) verbose;
                    if verbose then do {
                        Bench.report_since "check_module_with_scope" t_check;
                        return unit
                    } else return unit;
                    match diags {
                        List.cons _ _ => do {
                            fail_line "FAILED at stage: typecheck (target file did not typecheck cleanly)";
                            print_diagnostics diags;
                            if verbose then do {
                                Bench.report_since "compile_file total (failed at typecheck)" total_start;
                                return unit
                            } else return unit;
                            return 1
                        },
                        List.empty => do {
                            stage verbose "codegen + link";
                            let link_result <- compile_file_codegen { file_path := file_path, output_dir := output_dir, output_name := output_name, ir := ir, verbose := verbose, debug := debug, target := target, preloaded := Option.some em.loaded };
                            if verbose then do {
                                Bench.report_since "compile_file total" total_start;
                                return unit
                            } else return unit;
                            return link_result
                        },
                    }
            },
        Result.err e => do {
            fail_line ("FAILED at stage: load (could not load dependencies: " ++ e ++ ")");
            let link_result <- compile_file_codegen { file_path := file_path, output_dir := output_dir, output_name := output_name, ir := ir, verbose := verbose, debug := debug, target := target, preloaded := Option.none };
            if verbose then do {
                Bench.report_since "compile_file total" total_start;
                return unit
            } else return unit;
            return link_result
        },
    }
    }
}

/// Compile a source file and execute the resulting native binary.
/// Mirrors the Rust host's `monad-rs run <file>` — compile through
/// `compile_file` (which type-checks, generates LLVM IR, and links via
/// llc+clang), then `exec_cmd` the binary. Returns the binary's exit
/// code, or 1 if compilation failed.
#[partial]
def run_file (file_path : String) (output_dir : Path) (verbose : Bool) (debug : Bool) : IO I64 {
    let out_name : Path := Path.path "run_out";
    // `Option.none`: a `run` is not a cache entry, so there is no key to
    // name the IR by -- the output-derived `run_out.ll` is what this path
    // has always used and it stays out of anything stored.
    let native <- TargetSpec.native;
    let compile_result <- compile_file { file_path := file_path,
        output_dir := output_dir, output_name := out_name, ir := Option.none,
        verbose := verbose, debug := debug, target := native };
    if not (compile_result == 0) then do {
        println "run: compilation failed";
        return 1
    } else do {
        let bin_path := Path.to_string (Path.join output_dir out_name);
        let exit_code <- exec_cmd bin_path [];
        return exit_code
    }
}

/// Evaluate a source file using the self-hosted interpreter (lower to
/// CoreIr + evaluate via `lang.core_eval`), without compiling to a
/// native binary. Mirrors the Rust host's `monad-rs run <file>` for
/// pure programs — loads the file's dependencies, elaborates, type-
/// checks the target, lowers to CoreIr, and evaluates `main`. Only the
/// 8 natives in `basic_native_table` are available (no IO/println);
/// programs using other natives fail with `ce_unknown_native`.
#[partial]
def eval_file (file_path : String) (verbose : Bool) : IO I64 {
    stage verbose "load + elaborate modules";
    let elaborated_result <- elaborate_loaded_modules file_path false verbose;
    match elaborated_result {
        Result.err e => do {
            fail_line ("FAILED at stage: load (could not load dependencies: " ++ e ++ ")");
            return 1
        },
        Result.ok em => do {
            let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
            stage verbose "typecheck target";
            let diags <- check_module_with_scope em.scope em.target_decls empty_locs (Option.some file_path) verbose;
            match diags {
                List.cons _ _ => do {
                    fail_line "FAILED at stage: typecheck (target file did not typecheck cleanly)";
                    print_diagnostics diags;
                    return 1
                },
                List.empty => do {
                    let eval_result <- eval_file_typechecked em verbose;
                    return eval_result
                },
            }
        },
    }
}

/// The `-- eval` pipeline after the typecheck gate passes: lower the
/// target's elaborated decls to CoreIr rooted at `main`, then hand the
/// result to `eval_file_lowered`. Split out of `eval_file` so its own
/// match/do nesting stays at the self-hosted parser's known-good depth
/// (same shape as `compile_file` delegating to `compile_file_codegen`)
/// -- the 4-deep bare-match chain this used to inline in one do-block
/// arm is exactly the shape `lang/parser.mo` fails to parse.
#[partial]
def eval_file_typechecked (em : ElaboratedModules) (verbose : Bool) : IO I64 {
    stage verbose "lower";
    // Prepare the whole graph for real execution before lowering --
    // the same "elaborate + dispatch" recipe the codegen pipeline and
    // `meta_eval_invoke`'s callers use (`compile_loaded_modules_to_ir_`
    // with_debug`/`expand_decls_graph`). `em.elaborated_decls` is the
    // raw elaborated graph: its class-method calls (`*` on I64 is
    // `HMul.mul` underneath) are still syntactic, and lowering them
    // failed with `le_unresolved_name` before this.
    let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
    let dispatched := resolve_class_calls_decls (elaborate_module_decls_best_effort em.scope em.elaborated_decls empty_locs);
    // `lower_root` roots at a DEF name, not a module name: the target
    // file's `main` def. The graph above is from BEFORE codegen's
    // `qualify_modules` stage, so def names are still bare -- rooting
    // at `[module_name]` failed lower with "unresolved module path
    // <module>".
    // Two shapes of the same root, because the two calls want
    // different ones: `lower_ctx_from_decls` carries a module identity
    // (`ModulePath`), `lower_root` roots at a DEF name (`NamePath`).
    // Both are the one-segment "main".
    let root_mp : ModulePath := ModulePath.mp [Identifier.id "main"];
    let root_np : NamePath := NamePath.npath [Identifier.id "main"];
    let ctx := lower_ctx_from_decls root_mp dispatched;
    match lower_root ctx root_np {
        Result.err e => do {
            fail_line ("FAILED at stage: lower (" ++ show_lower_error e ++ ")");
            return 1
        },
        Result.ok pr => do {
            match pr {
                Pair.pair ir globals => do {
                    let eval_result <- eval_file_lowered ir globals;
                    return eval_result
                },
            }
        },
    }
}

/// The tail of the `-- eval` pipeline: run the interpreter on lowered
/// CoreIr + globals and print the result. `eval` threads a memoized
/// global cache alongside the result; once the root value exists every
/// global it forced is already in it, so the cache is simply discarded.
#[partial]
def eval_file_lowered (ir : CoreIr) (globals : GlobalTable) : IO I64 {
    match eval ir Env.env_nil globals basic_native_table (global_cache_new (global_table_len globals)) {
        Pair.pair r _ => do {
            match r {
                Result.ok v => do {
                    println ("Eval result " ++ show_value_debug v);
                    return 0
                },
                Result.err e => do {
                    fail_line ("FAILED at stage: eval (" ++ show_core_eval_error_debug e ++ ")");
                    return 1
                },
            }
        },
    }
}

/// Render a `LowerError` for the eval command's error output. Covers
/// every variant: this is a `#[partial]` def, so a missing arm is not a
/// compile error but a runtime "non-exhaustive match" crash exactly
/// when the eval command needs its diagnosis most (that crash was the
/// first bug the eval smoke test hit -- `le_unresolved_name`).
#[partial]
def show_lower_error (e : LowerError) : String :=
    match e {
        LowerError.le_unresolved_name name => String.concat "unresolved name " (show_identifier name),
        LowerError.le_unresolved_module_path path => String.concat "unresolved module path " (show_module_path path),
        LowerError.le_unknown_inductive path => String.concat "unknown inductive " (show_module_path path),
        LowerError.le_unknown_constructor path => String.concat "unknown constructor " (show_module_path path),
        LowerError.le_unknown_native name => String.concat "unknown native " (show_identifier name),
        LowerError.le_type_level_term => "type-level term reached lowering",
        LowerError.le_con_hole_before_filled_arg => "constructor hole before a filled arg",
        LowerError.le_struct_lit_survived => "struct literal reached lowering un-desugared (give the literal an explicit `: StructName` annotation, or bind it to an annotated local)",
        LowerError.le_float_literal_unsupported => "float literals are not supported by `monad eval` (the eval IR cannot carry one yet); `monad test` and `monad build` compile them correctly",
        LowerError.le_in_def path inner => String.concat "in def " (String.concat (show_module_path path) (String.concat ": " (show_lower_error inner))),
    }

/// The original `compile_file` body, unchanged -- codegen's own loading
/// + compile pipeline, run only once the gate above has confirmed the
/// target file itself checks cleanly (or the gate's own dependency load
/// failed, in which case this redundant re-attempt produces the same
/// real, rendered diagnostic the old code already did via its own
/// fallback path below, rather than a bare "gate failed").
/// `debug` (from `Command.build`'s own field -- on by default,
/// `--release` opts out, `--debug`/`-g` opts back in) gates whether DWARF
/// is EMITTED, and nothing else. It used to also decide the SHAPE of the
/// term tree: the wrappers the debug info is built from were added by
/// re-parsing every loaded module (`with_located_decls`), so `--release`
/// and `--debug` ran the rest of the pipeline on structurally different
/// trees. `parse_all_decls` (`lang/module.mo`) now locates on every path,
/// so both modes see the same tree and this flag only reaches
/// `source_path`/`debug_files` -- see `parse_all_decls`' own doc comment
/// for the bug that divergence caused.
#[partial]
def compile_file_codegen (file_path : String) (output_dir : Path) (output_name : Path) (ir : Option Path) (verbose : Bool) (debug : Bool) (target : TargetSpec) (preloaded : Option LoadedModules) : IO I64 {
    // `preloaded` is the module set the typecheck gate already loaded, if
    // it got that far -- reusing it avoids reading and re-parsing the
    // target's ENTIRE transitive closure (prelude and init included) a
    // second time, which is exactly what this function used to do on
    // every successful compile. `Option.none` (the gate's own load
    // failed) falls back to loading here, so the error path still
    // produces the same rendered diagnostic it always did.
    // Fail FAST on a missing input. Without this the load below fails,
    // the error path falls back to "parse without dependencies for error
    // reporting", `read_file` on a nonexistent path yields empty text,
    // the lenient parser happily "succeeds" with an EMPTY decl list, and
    // the compile proceeds -- writing IR and invoking the linker for a
    // file that does not exist. The linker error that eventually appears
    // names an object file, not the missing source, which is a poor
    // diagnostic for the simplest possible mistake.
    let input_exists : Bool <- file_exists (Path.path file_path);
    if not input_exists then do {
        println ("error: file not found: " ++ file_path);
        return 1
    } else do {
    let res <-
        match preloaded {
            Option.some already => do { return (Result.ok already) },
            Option.none => load_file_modules file_path verbose,
        };
    match res {
        Result.ok loaded => do {
            // `source_path` is only set under `--debug`: it is what the debug
            // info names as the compile's source file. `parse_all_decls`
            // (`lang/module.mo`) locates every term on every path now, so
            // there is no debug-only re-parse to gate on anything.
            let source_path : Option String := if debug then Option.some file_path else Option.none;
            // `verbose` thread-through: previously this branch dumped the
            // ENTIRE `loaded : LoadedModules` struct (`Show.show loaded`,
            // walking every loaded module's full content) on every
            // successful compile -- pure noise on a working build AND a
            // real perf hit. Now `verbose` is forwarded to
            // `compile_loaded_modules_to_ir_with_debug`, whose own
            // `--verbose`-gated stage trace (its per-stage printlns, plus
            // the `Loaded N modules` count it prints on entry) is the one
            // place that progress is reported -- a count printed here too
            // would duplicate it two calls later.
            let mod_result <- compile_loaded_modules_to_ir_with_debug loaded verbose source_path target.triple;
            // `[link] libs` from every mote in the dependency closure --
            // a package-level build property, read from the manifests
            // rather than from any `#[extern "c"]` attribute.
            let link_libs : List String <- collect_link_libs (get_loaded_all loaded);
            link_compiled_module { mod_result := mod_result, link_libs := link_libs,
                base_dir := extract_directory file_path,
                output_dir := output_dir, output_name := output_name,
                ir := ir, verbose := verbose, target := target }
        },
        Result.err e => do {
            println ("Failed to parse dependencies: " ++ e);
            // Fallback to simple parsing without dependencies (for error reporting).
            // `file_path` was already used successfully by `load_file_modules`
            // just above (that's the error being handled), so it's known
            // non-empty -- `Path.path` directly, not `Path.of`.
            let source <- IO.read_file (Path.path file_path);
            match try_parse_decls source {
                Option.some decl_list => do {
                    let source_path : Option String := if debug then Option.some file_path else Option.none;
                    compile_parsed_decls { decl_list := decl_list,
                        base_dir := extract_directory file_path,
                        output_dir := output_dir, output_name := output_name,
                        ir := ir, verbose := verbose, source_path := source_path,
                        target := target }
                },
                Option.none => do {
                    // `try_parse_decls` (leniently truncate-and-succeed) just
                    // told us decls_parser bailed outright — genuinely rare
                    // (it usually silently "succeeds" with a truncated decl
                    // list instead), but when it does happen there's no
                    // information left to build a diagnostic from. Re-parse
                    // with the strict twin specifically to recover a real,
                    // rendered, Rust-diag.rs-style error instead of the bare
                    // "Parse error: <path>" this used to print.
                    match try_parse_decls_strict source (Option.some file_path) {
                        Result.ok _ => do {
                            // Can't actually happen (strict succeeding implies
                            // lenient does too), but keep this path total.
                            println (String.concat "Parse error: " file_path);
                            return 1
                        },
                        Result.err diagnostic => do {
                            println diagnostic;
                            return 1
                        }
                    }
                }
            }
        }
    }
    }
}

/// Print one diagnostic per line — `check_file_cached`'s per-file diagnostics
/// are already fully rendered (parse diagnostics via
/// `render_parse_error`, type errors via `render_type_error`), so this
/// is just a sequenced println loop.
#[partial]
def print_diagnostics (diags : List String) : IO I64 :=
    match diags {
        List.empty => do { return 0 },
        List.cons d rest => do {
            println d;
            print_diagnostics rest
        }
    }

/// The `check` verb's option flags in one bundle: threading (and later
/// adding or removing) a flag is then a single `opts` parameter, not a
/// positional at every call site along the check path.
struct CheckOptions {
    verbose : Bool,
    workspace : Bool,
    no_cache : Bool,
    affine : Bool,
}

/// `checked`/`errors` accumulate across all files — errors are counted
/// per-diagnostic (a file with 3 failing defs contributes 3), matching
/// `monad-rs check`'s own error-tally convention. Every file gets an
/// explicit `ok`/`FAIL` line (a passing file used to print nothing at
/// all, indistinguishable from "not reached" — see the corpus-check
/// driver this feeds, which needs a real per-file pass/fail matrix,
/// not just a final count).
///
/// `plan` is the `check` cache's decision for this run, and a HIT IS
/// REPLAYED IN PLACE — inside this one loop, at this file's own position
/// in the output. That is the whole point of the shape. The loop threads
/// ONE `ModuleInfoCache`, and that cache is what makes a file's
/// dependency closure free once an earlier file has loaded it (measured
/// at 75% of dependency loads across 5 files, `lang/src/module.mo`). A
/// cache that split the run into "the hits" and "the misses" — or worse,
/// into one invocation per file — would throw exactly that away, which is
/// why one large file on its own never finishes while all 195 together
/// are 789 seconds. Composability comes from the recorded keys, never
/// from splitting the work.
///
/// An inactive plan is the same code path with no keys: every file is
/// checked, nothing is recorded, and the output is byte-identical to what
/// this command printed before any cache existed.
#[partial]
def run_check_loop (cache : ModuleInfoCache) (files : List String) (checked : I64) (errors : I64) (opts : CheckOptions) (plan : CheckPlan) : IO I64 :=
    match files {
        List.empty => do {
            println (I64.to_string checked ++ " file(s) checked, " ++ I64.to_string errors ++ " error(s)");
            // Whole-run module cache visibility: `hits` counts dependency
            // loads served from an EARLIER file's own load in this same
            // run, instead of re-reading and re-parsing the file from
            // disk -- the direct measure of the cross-file redundancy
            // `ModuleInfoCache` (lang/module.mo) exists to remove.
            if opts.verbose then
                match cache {
                    ModuleInfoCache.mk _ hits misses =>
                        println ("module cache: " ++ I64.to_string hits ++ " hit(s), " ++ I64.to_string misses ++ " miss(es)")
                }
            else do { return unit };
            return (if I64.gt errors 0 then 1 else 0)
        },
        List.cons f rest => do {
            match Build.check_plan_key plan f {
                // No key for this file (the plan is inactive, or its
                // digest failed): check it, and record nothing.
                Option.none => run_check_file cache f rest checked errors opts plan Option.none,
                Option.some key => do {
                    let stored <- Build.check_entry_read (Build.check_plan_root plan) key;
                    match stored {
                        // A hit: replay what was recorded, verbatim, and
                        // count it exactly as the original run counted
                        // it. No `check_file_cached` call at all.
                        Option.some p =>
                            match p {
                                Pair.pair counted block => do {
                                    println block;
                                    run_check_loop cache rest (checked + 1) (errors + counted) opts plan
                                }
                            },
                        Option.none => run_check_file cache f rest checked errors opts plan (Option.some key)
                    }
                }
            }
        }
    }

/// Check one file and record the result. The only place a `check` result
/// is produced, replayed or not.
///
/// The whole per-file report is printed as ONE string built by
/// `Build.check_block`, where this used to print a header and then each
/// diagnostic on its own line. Same bytes -- `println (intercalate "\n"
/// xs)` is `mapM_ println xs` -- and routing both the printing and the
/// storing through one function is what keeps a replayed hit from
/// drifting out of step with a fresh miss.
///
/// `--affine` swaps in the M2-rule variant of the same file checker
/// (lang/module.mo's `check_file_cached_affine`): ordinary diagnostics
/// plus the affine rule's, so an over-use fails `check` exactly the way
/// a type error already does. The plan an affine run receives is
/// always inactive (see `run_check`), so nothing affine is recorded and
/// nothing recorded is replayed here.
#[partial]
def run_check_file (cache : ModuleInfoCache) (f : String) (rest : List String) (checked : I64) (errors : I64) (opts : CheckOptions) (plan : CheckPlan) (key : Option String) : IO I64 := do {
    let checked_and_cache <- if opts.affine
        then check_file_cached_affine cache f opts.verbose
        else check_file_cached cache f opts.verbose;
    match checked_and_cache {
        FileCheckAndCache.mk result updated_cache =>
            match result {
                FileCheckResult.mk path diags => do {
                    let block : String := Build.check_block path diags;
                    let counted : I64 := List.length diags;
                    println block;
                    let _rec <- Build.check_maybe_write plan key counted block;
                    run_check_loop updated_cache rest (checked + 1) (errors + counted) opts plan
                }
            }
    }
}

/// Parse + typecheck each file with `lang.module.check_file_cached` — no
/// execution, no compilation. See lang/module.mo's `check_file_cached`/
/// `check_module_with_scope` for what "does this file compile" means
/// today: real parse diagnostics (strict, not the lenient
/// truncate-and-succeed parser), plus every failing `def`/`type`
/// declaration's type error — other declaration kinds (use/open/
/// class/instance/struct) aren't checked yet, matching the self-hosted
/// typechecker's current coverage.
///
/// Any argument that's a directory is expanded to every `.mo` file
/// under it first (`lang.module.expand_check_paths`, recursive, via
/// `IO.list_dir`/`IO.is_dir`) — so `check init std lang examples` walks
/// the whole corpus the same way `monad-rs check --workspace` does,
/// without needing an external `find`. `verbose` (`--verbose`/`-v`)
/// prints a per-declaration progress trace as each file is checked —
/// for isolating exactly where a large file's check gets stuck, since
/// the flat diagnostic list alone doesn't say where the checker got to.
///
/// The cross-file redundancy this used to guard against — every file
/// independently reloading and reparsing prelude/init — is now removed
/// by `ModuleInfoCache` (`lang/module.mo`), threaded through every
/// `check_file_cached` call below. A separate `PreludeInitBase`,
/// prebuilt here and handed down, was accepted but never read by
/// `check_file_cached`, so building it cost ~3.7s of dead work on
/// every `check` invocation; it is gone.
/// Decide WHICH files `check` and `test` run, from the three modes the
/// two subcommands share:
///
///   * explicit paths -> exactly those (directories expanded by the
///                       caller, since `expand_check_paths` is one more
///                       I/O step neither wants inside here);
///   * `--workspace`  -> every mote in the enclosing workspace;
///   * neither        -> the mote containing the working directory, so
///                       `monad check` inside `std/` checks `std`.
///
/// `Option.none` means "nothing was asked for": no explicit paths, and
/// no `mote.toml` above. Both callers answer that with
/// `no_target_diagnostic` and exit 1 -- a bare subcommand in an
/// arbitrary directory has nothing to do, so it should say so rather
/// than sweep the filesystem, and it should NOT exit 0 while saying it.
/// Printing the whole usage screen and returning 0 (what this used to
/// do) is the shape a first-time user meets in an empty directory:
/// `mkdir game && cd game && monad check` reads as a pass on a mote that
/// does not exist yet, which is the one thing a check command must not
/// do.
///
/// `Option.some List.empty` is the other empty case and is deliberately
/// NOT folded into `Option.none`: `--workspace` was given, and no
/// `[workspace] members` was found above, so the subcommand was asked
/// to enumerate something and found nothing. The diagnostic is printed
/// here, where the flag is still in hand, and both callers turn the
/// empty list into a failing exit -- an invocation that was told to
/// cover a workspace and covered zero files is a broken invocation, not
/// a pass. (The explicit-path branch can never return `some []`, since
/// it only runs when the caller's list is non-empty.)
///
/// `verb` is the gerund the found mote is reported with ("Checking" /
/// "Testing") and `subcommand` the spelled-out name in the `--workspace`
/// diagnostic, so one helper serves both without either printing the
/// other's word.
///
/// **The mote root is what resolution keys off now, not the working
/// directory.** `lang/module.mo`'s `resolve_via_manifest` discovers the
/// manifest of the file being resolved and reads that manifest's own
/// `[dependencies.<name>] path = "..."` entries, so a mote found from
/// inside its own directory resolves its dependencies from its own
/// manifest wherever the CWD is. This used to be untrue -- resolution
/// walked a fixed directory cascade relative to the CWD, so
/// `monad test` from inside `llvm/` reported a wall of "unknown
/// variable" -- and the note that this def used to print saying so is
/// gone with the cause.
#[partial]
def resolve_target_paths (verb : String) (subcommand : String) (files : List String) (workspace : Bool) : IO (Option (List String)) := do {
    // `List.empty`/`List.cons` are deliberately NOT used as match
    // patterns here: this file's test driver loads the whole compiler
    // closure, where `BTreeMap` and `Vec` also declare `empty`/`cons`
    // and the bare pattern names turn ambiguous.
    if Bool.not (List.is_empty files) then return (Option.some files)
    else if workspace then do {
        // The workspace root is where the `[workspace]` manifest is.
        // `Mote.discover` stops AT a virtual root (returning none,
        // since a root declares no `[mote]`), so the root is found by
        // looking for the members list directly, walking up from here.
        // The walk hands back members already joined onto the root it
        // found, which is why `--workspace` works from a subdirectory.
        let members <- find_workspace_members "" 32;
        if List.is_empty members then do {
            println ("monad " ++ subcommand ++ " --workspace: no workspace manifest found (no [workspace] members above this directory)");
            return (Option.some List.empty)
        } else return (Option.some members)
    } else do {
        let m <- Mote.discover "";
        match m {
            Option.none => return Option.none,
            Option.some manifest => do {
                // `manifest.dir` is where the manifest was found,
                // RELATIVE to the working directory -- `""` when the
                // CWD is the mote root itself, which a path expander
                // wants spelled `"."`. Either way the mote is named
                // and located, so the two cases differ in the path
                // only.
                let dir := if String.beq manifest.dir "" then "." else manifest.dir;
                let roots : List String := Mote.target_roots manifest dir;
                println (verb ++ " mote " ++ manifest.name ++ " (" ++ dir ++ ")");
                return (Option.some roots)
            }
        }
    }
}

/// The message a bare subcommand prints when nothing was named and no
/// manifest was found above the working directory, paired with the exit
/// code that makes it a failure. A sibling of `resolve_target_paths`'s
/// `--workspace` arm, which prints its own reason and lets its caller
/// `return 1` for the same reason: an invocation that covered zero files
/// is a broken invocation, not a pass.
///
/// It replaces `print_help` in the `Option.none` arms rather than
/// sitting beside it. The usage screen answers "how do I use this
/// command", which is not the question asked here -- the question is
/// "why did nothing happen", and the answer is three concrete things the
/// user can do next. Help remains reachable by asking for it
/// (`monad`, `monad --help`), where it is what was wanted.
///
/// `subcommand` appears twice so one def serves both callers: as the
/// command that did nothing ("monad check: ...") and as the command
/// whose file form is the first way out.
def no_target_diagnostic (subcommand : String) : IO I64 := do {
    println ("monad " ++ subcommand ++ ": no mote.toml above this directory and no paths given");
    println ("  hint: name a file, run this inside a mote, or pass --workspace");
    return 1
}

/// Whether a run may use the store at all, from BOTH switches.
///
/// `--no-cache` and `MONAD_NO_CACHE` are one decision, and the environment
/// half treats ANY non-empty value as off -- `MONAD_NO_CACHE=0` included.
/// An escape hatch that the value someone happened to write can silently
/// disarm is not an escape hatch, and the variable's whole job is to be
/// believed.
///
/// Read by `build` as well as `check`, which is why this is named for the
/// decision and not for the caller. The environment half matters more to
/// `build` than the flag does: a gate that wants the compiler to actually
/// RUN -- `tools/debug_transparency_oracle.sh` inspects the `.ll` it emits,
/// and `scripts/check-external-mote.sh`'s config 4 asserts on a linked
/// binary `build` would otherwise copy out of the store -- cannot assume
/// the tool it drives has grown `--no-cache` yet, and a gate that silently
/// replays a stored answer instead of compiling is a gate that passed
/// without testing anything. The variable is how such a caller states its
/// requirement without depending on this flag's existence.
///
/// Off means off in BOTH directions for the ARTIFACT: nothing is read from
/// the store and no entry is recorded. A caller reaching for this is
/// settling a suspicion about a stored entry; recording a new one from the
/// run it asked for as clean is the one thing it did not ask for.
///
/// The key-named IR is the one thing a hatch build still writes, and it
/// writes it INTO the store (`<target-dir>/store/<hash>.ll`), deliberately:
/// the IR filename is what `llc` records in the object it emits, so a hatch
/// build that named its IR after `-o` instead would produce bytes that could
/// not be compared with the cached build it exists to check. That write is a
/// no-op in CONTENT whenever the key is a function of everything reaching
/// the IR -- which is the property the IR filename was made key-derived for
/// -- so it is invisible today in every case where the key is complete.
/// Measured where it is not: two byte-identical toolchain roots share one
/// key but carry different absolute `!DIFile` directories
/// (`llvm_split_path`, llvm/src/ir.mo:979, takes a module's path verbatim),
/// so a hatch build through one root REWRITES the IR the other recorded.
/// The artifact is never touched, so the answer served stays correct; what
/// this note corrects is only the older claim that a hatch run writes
/// nothing at all. See `target-monad/verify/c3c4_build.sh` for the measurement and
/// the plan's resolved-toolchain-root item for the fix.
#[partial]
def cache_enabled (no_cache : Bool) : IO Bool := do {
    if no_cache then return false
    else do {
        let e <- IO.get_env "MONAD_NO_CACHE";
        match e {
            Option.none => return true,
            Option.some v => return (String.is_empty v)
        }
    }
}

/// Make the store directory, if there is one to make.
#[partial]
def check_store_ready (plan : CheckPlan) : IO I64 := do {
    if Build.check_plan_active plan
    then Build.ensure_dir (Build.check_plan_root plan)
    else return 0
}

/// Say why the cache is off, when the reason is one a user can act on, and
/// create the store either way.
///
/// Nothing here can change an ANSWER: an inactive plan is exactly the
/// behaviour `check` had before a cache existed. So this is a diagnostic
/// and not a warning, which is why the two deliberate cases -- a
/// single-file run, and `--no-cache` -- carry no message at all, while a
/// missing digest tool or an unreadable `/proc/<pid>/exe` does. A silently
/// disabled cache on the machine that needed it is the one outcome worth
/// a line.
#[partial]
def announce_check_cache (plan : CheckPlan) : IO I64 := do {
    let reason : String := Build.check_plan_reason plan;
    if String.is_empty reason
    then check_store_ready plan
    else do {
        println ("check cache off: " ++ reason);
        check_store_ready plan
    }
}

#[partial]
def run_check (files : List String) (opts : CheckOptions) : IO I64 := do {
    let targets <- resolve_target_paths "Checking" "check" files opts.workspace;
    match targets {
        // Empty only from `--workspace` with no workspace manifest --
        // see `resolve_target_paths`, which has already printed why.
        // Failing rather than "0 file(s) checked" is the point: a
        // `--workspace` run that checked nothing did not pass.
        Option.some ts => if List.is_empty ts then return 1
        else do {
            let expanded : List String <- expand_check_paths ts;
            // One target directory for the whole run, resolved from the
            // working directory rather than per file: every file in a
            // workspace resolves to the same one anyway, and resolving it
            // once is what keeps a `--workspace` run over eleven motes
            // from writing eleven partial stores.
            let target_dir <- Build.target_dir_at "";
            let requested <- cache_enabled opts.no_cache;
            // `--verbose` disables the cache outright rather than
            // bypassing hits: its trace is a record of what the checker
            // DID, and a replayed entry has no trace to show. A cache
            // that silently suppressed the trace it was asked for would
            // be worse than a slow one.
            //
            // `--affine` disables the cache outright, for the same
            // kind of reason: a stored entry records the ORDINARY
            // check's result, and replaying it under `--affine` would
            // silently drop the very diagnostics the flag exists to
            // fail on -- while an affine result recorded under an
            // ordinary run's key would let the ordinary check pass
            // files the affine rule rejects. Neither direction is
            // safe, so neither reads nor writes happen.
            let plan <- Build.check_plan expanded target_dir (requested && Bool.not opts.verbose && Bool.not opts.affine);
            let _prep <- announce_check_cache plan;
            let cache : ModuleInfoCache := module_info_cache_empty;
            run_check_loop cache expanded 0 0 opts plan
        },
        // Nothing named, inside no mote: say why, and fail. `print_help`
        // with its exit 0 was the behaviour before any of this existed,
        // and it is exactly the bug -- see `no_target_diagnostic`.
        Option.none => no_target_diagnostic "check"
    }
}

/// The target directory a management verb should act on, resolved exactly
/// the way a build resolves it -- all four tiers of
/// `Build.resolve_target_dir` -- from the working directory.
///
/// `--target-dir` is the flag form of the highest tier, and it earns its
/// place on THESE verbs more than anywhere else: inspecting or reclaiming a
/// store without changing into the tree that owns it is most of the reason
/// to have them. An empty flag leaves the other three tiers to decide,
/// which is what `build` and `check` do.
///
/// `Mote.discover_config_target_dir`, not `Mote.discover`: the config is the
/// tool's, so the walk has no mote boundary to stop at -- and a store owned
/// by a virtual workspace root would otherwise be invisible from inside it.
/// `Build.target_dir_at` makes the same choice for the same reason.
#[partial]
def target_dir_flagged (flag : String) : IO String := do {
    let d <- Mote.discover_config_target_dir "";
    Build.target_dir_of flag d ""
}

/// `monad clean [--all]`: drop the output directories under `<target-dir>`,
/// or the whole directory with `--all`.
///
/// It takes no paths, on purpose. "Which files were built" is `gc`'s
/// question and it needs an answer; "where did the build put things" is
/// this one's and it does not.
#[partial]
def run_clean (all : Bool) (target_dir_flag : String) : IO I64 := do {
    let target_dir <- target_dir_flagged target_dir_flag;
    Build.clean_run target_dir all
}

/// `monad gc [<path>...]`: reclaim what the named files cannot reach.
///
/// Resolution mirrors `run_check`'s, step for step -- the same
/// `resolve_target_paths`, the same `expand_check_paths`, the same
/// directory-vs-file rules -- and it has to, because the reachable set this
/// deletes everything else in favour of is derived from exactly those
/// files. A `gc` that resolved a DIFFERENT set than `check` caches would
/// delete live entries.
#[partial]
def run_gc (files : List String) (workspace : Bool) (apply : Bool) (target_dir_flag : String) : IO I64 := do {
    let targets <- resolve_target_paths "Collecting garbage from" "gc" files workspace;
    match targets {
        // Empty only from `--workspace` with no workspace manifest, which
        // `resolve_target_paths` has already explained. Failing rather than
        // letting `Build.gc_run` refuse is not redundant: the refusal would
        // be correct and the message here is the one that names the cause.
        Option.some ts => if List.is_empty ts then return 1
        else do {
            let expanded : List String <- expand_check_paths ts;
            let target_dir <- target_dir_flagged target_dir_flag;
            let native <- TargetSpec.native;
            // Every target a build can key under, not just this machine's:
            // `native.triple` alone would make `gc` classify every cross-built
            // artifact as unreachable and remove it.
            Build.gc_run expanded target_dir (TargetSpec.keep_triples native.triple) apply
        },
        Option.none => no_target_diagnostic "gc"
    }
}

/// `monad store ls|verify`: what the store holds.
///
/// The two subcommands share `Build.entry_views`, so they cannot disagree
/// about what an entry IS; what differs is only what they do with it --
/// `ls` prints every entry, `verify` prints the failures and exits non-zero
/// on any. Neither derives a key; see `Build.store_verify` for what that
/// bounding is and why.
#[partial]
def run_store (sub : String) (target_dir_flag : String) : IO I64 := do {
    let target_dir <- target_dir_flagged target_dir_flag;
    if String.beq sub "ls" then Build.store_ls target_dir
    else if String.beq sub "verify" then Build.store_verify target_dir
    else do {
        println ("monad store: unknown subcommand `" ++ sub ++ "`");
        println "  usage: monad store ls|verify [--target-dir <dir>]";
        return 1
    }
}

/// A `monad test <path>...` subcommand mirroring `monad-rs test`: for
/// each resolved file, discover its own `#[test]` defs, compile a
/// native driver binary (`lang.codegen.test_driver`'s
/// `compile_loaded_modules_to_test_ir` — the same discover → synthesize
/// → compile pipeline `compile_file`'s own `compile` command's
/// `link_ir` already links and runs single programs with, reused here
/// per test file), and RUN it — the driver binary's own `println`
/// PASS/FAIL-per-test + summary line streams straight to inherited
/// stdout (`exec_cmd`'s own `std::process::Command::status()` inherits
/// stdio by default, `core/src/core_native.rs`), the same way
/// `lang.codegen.test_driver`'s own doc comment describes.
///
/// Any argument that's a directory is expanded to every `.mo` file
/// under it first (`expand_check_paths`, the same helper `check` uses)
/// — this is what makes `monad test lang/` (a directory) actually work,
/// unlike calling `compile_loaded_modules_to_test_ir` directly, which
/// is scoped to a single already-loaded file.
///
/// A file with no `#[test]`s is reported as `SKIP`, not `FAIL` — not a
/// real problem with that file. A file that defines its own top-level
/// `main` alongside its tests runs normally: the driver renames that
/// `main` out of its way (`rename_user_main`, test_driver.mo).
///
/// Counts are per TEST, not per file, matching the Rust runner. Each
/// driver binary reports its own failure count through a per-binary
/// RESULT FILE (`__MONAD_TEST__ <failed>`, written by the driver just
/// before it returns and read back here) -- a channel with no ceiling,
/// unlike the exit code it replaces, which is 8 bits and wraps past 255
/// failures (that ceiling is what used to refuse
/// `lang/src/parser.mo`, at 288 tests). The exit code is still written
/// by the driver for a human running the binary by hand, but is never
/// trusted here: a missing or unparseable result file means the driver
/// died before finishing, and is classified as a crash.
/// Decide WHICH files `monad test` runs (`resolve_target_paths`, the
/// dispatcher `check` shares), then run them.
///
/// Outside any mote and with no paths, it says why and exits 1
/// (`no_target_diagnostic`) -- a bare `monad test` in an arbitrary
/// directory has nothing to run, so it should say so rather than sweep
/// the filesystem, and it should not report success for having run
/// nothing.
///
/// Note that a mote-enumerating run covers only directories that ARE
/// motes: `examples/` has no manifest, so its 19 files are reached by
/// naming them (or by CI's own explicit sweep), not by `--workspace`.
#[partial]
def run_test_paths (files : List String) (workspace : Bool) (out_dir : String) (verbose : Bool) : IO I64 := do {
    let targets <- resolve_target_paths "Testing" "test" files workspace;
    match targets {
        // Empty only from `--workspace` with no workspace manifest --
        // see `resolve_target_paths`, which has already printed why.
        // `return 1` rather than reaching `run_test`'s own empty-list
        // "No tests found": same exit code, without a second line
        // saying the same thing.
        Option.some ts => if List.is_empty ts then return 1
        else run_test ts out_dir verbose,
        // Nothing named, inside no mote: say why, and fail -- see
        // `no_target_diagnostic`.
        Option.none => no_target_diagnostic "test"
    }
}

/// Walk up looking for a manifest with `[workspace] members`, returning
/// its expanded member directories. Bounded the same way `Mote.discover`
/// is, and for the same reason: the walk is string surgery on a path.
#[partial]
def find_workspace_members (dir : String) (depth : I64) : IO (List String) := do {
    if I64.lt depth 1 then do { return List.empty }
    else do {
        let here : List String <- Mote.workspace_members dir;
        // Same bare-pattern ambiguity as `run_test_paths` -- `List.is_empty`
        // instead of matching on the constructors.
        if List.is_empty here then
            if String.beq dir "" then find_workspace_members ".." (depth - 1)
            else if String.beq dir "/" then do { return List.empty }
            else find_workspace_members (raw_path_join dir "..") (depth - 1)
        else do { return here }
    }
}

#[partial]
def run_test (files : List String) (out_dir : String) (verbose : Bool) : IO I64 := do {
    let expanded : List String <- expand_check_paths files;
    let total_files : I64 := List.length expanded;
    run_test_loop { files := expanded, out_dir := out_dir, bin_idx := 0, tests_passed := 0, tests_failed := 0, files_failed := 0, skipped := 0, file_idx := 0, total_files := total_files, verbose := verbose, cache := module_info_cache_empty }
}

/// `tests_passed`/`tests_failed` count individual TESTS across all
/// files; `files_failed` counts files whose driver never produced usable
/// results (compile failure, or a driver that died), and `skipped`
/// counts files that had no runnable tests to begin with. The three are
/// kept apart deliberately: a file that failed to compile contributed no
/// test results either way, so folding it into the per-test totals would
/// invent results that do not exist.
/// `bin_idx` names each compiled test binary uniquely
/// (`monad_test_bin_<N>`, `out_dir`) so running `test` against several
/// files in one invocation doesn't have each file's driver binary
/// overwrite the last one's before it's even run.
///
/// `cache` is the same whole-run `ModuleInfoCache` `run_check_loop`
/// threads: every file in one `test` invocation shares most of its
/// dependency closure (prelude/init at minimum, plus whatever `std`/
/// `lang` modules the files have in common), and without the cache each
/// file re-read and re-parsed all of it from disk. Measured on a
/// 5-file `check` run over `lang/`, the same cache serves 69 of 92
/// dependency loads (75%) from an earlier file's work.
#[partial]
def run_test_loop (files : List String) (out_dir : String) (bin_idx : I64) (tests_passed : I64) (tests_failed : I64) (files_failed : I64) (skipped : I64) (file_idx : I64) (total_files : I64) (verbose : Bool) (cache : ModuleInfoCache) : IO I64 :=
    match files {
        List.empty => do {
            let total_tests := tests_passed + tests_failed;
            // `No tests found` + a failing exit, matching the Rust
            // runner: a sweep that silently found nothing is a broken
            // invocation, not a pass.
            if I64.beq total_tests 0 then do {
                println "No tests found";
                return 1
            } else do {
                let color : String := if I64.gt tests_failed 0 then "[31m" else "[32m";
                println (color ++ I64.to_string tests_passed ++ "/" ++ I64.to_string total_tests ++ " total tests passed" ++ "[0m");
                // Skips are reported separately rather than folded into
                // the ratio above -- a skipped file contributed no tests
                // to either side of it, and hiding that in a denominator
                // would misreport both.
                if I64.gt skipped 0 then
                    println (I64.to_string skipped ++ " file(s) skipped (no tests)")
                else do { return unit };
                // Same whole-run cache visibility `run_check_loop` prints --
                // `hits` counts dependency loads served from an earlier
                // file's own load in this same run.
                if verbose then
                    match cache {
                        ModuleInfoCache.mk _ hits misses =>
                            println ("module cache: " ++ I64.to_string hits ++ " hit(s), " ++ I64.to_string misses ++ " miss(es)")
                    }
                else do { return unit };
                return (if I64.gt tests_failed 0 || I64.gt files_failed 0 then 1 else 0)
            }
        },
        List.cons f rest => do {
            // The per-file header goes out BEFORE the typecheck gate, so
            // a file that ends up skipped still shows which file it was.
            println ("[33m[" ++ I64.to_string (file_idx + 1) ++ "/" ++ I64.to_string total_files ++ "] Testing " ++ f ++ "...[0m");
            // Stage 3 gate (see `compile_file`'s own identical doc
            // comment for the full rationale, including `check_deps`):
            // a file whose own decls don't type-check cleanly is reported
            // `SKIP`, not `FAIL` -- matching the existing "no #[test]s"
            // SKIP convention just below (a pre-existing problem with the
            // file, not a new test failure this run introduced).
            let ec <- elaborate_loaded_modules_cached f false cache verbose;
            // `out_cache`, not `cache`: this file's load extended it, and
            // every later file in the run needs the extended one.
            let out_cache : ModuleInfoCache := ec.cache;
            match ec.elaborated {
                Result.err e => do {
                    // A file that will not even load is a FAILURE, not a
                    // skip -- same reasoning as the driver-compile
                    // classification below, one gate earlier. Counting
                    // it as `skipped` (which affects no exit code) is
                    // what let broken files pass CI silently.
                    println ("[31mFAIL  " ++ f ++ " (" ++ e ++ ")[0m");
                    run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed + 1, skipped := skipped, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := out_cache }
                },
                Result.ok em =>
                    do {
                            let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
                            let diags <- check_module_with_scope em.scope em.target_decls empty_locs (Option.some f) verbose;
                            match diags {
                                List.cons _ _ => do {
                                    print_diagnostics diags;
                                    // Also a FAILURE, not a skip: the
                                    // diagnostics were already printed,
                                    // and a file whose tests cannot even
                                    // be type-checked has run nothing.
                                    println ("[31mFAIL  " ++ f ++ " (does not typecheck)[0m");
                                    run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed + 1, skipped := skipped, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := out_cache }
                                },
                                List.empty => run_test_loop_codegen { f := f, rest := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed, skipped := skipped, file_idx := file_idx, total_files := total_files, verbose := verbose, preloaded := Option.some em.loaded, cache := out_cache },
                            }
                    },
            }
        }
    }

/// The original `run_test_loop` body for one file, unchanged -- codegen's
/// own loading + compile + run pipeline, reached only once the gate
/// above has confirmed `f` itself checks cleanly.
#[partial]
def run_test_loop_codegen (f : String) (rest : List String) (out_dir : String) (bin_idx : I64) (tests_passed : I64) (tests_failed : I64) (files_failed : I64) (skipped : I64) (file_idx : I64) (total_files : I64) (verbose : Bool) (preloaded : Option LoadedModules) (cache : ModuleInfoCache) : IO I64 := do {
            // Reuses the module set `run_test_loop`'s typecheck gate
            // already loaded -- see `compile_file_codegen`'s own
            // `preloaded` comment for the redundancy this removes.
            // `cache` is carried, not consulted: this path never loads
            // anything itself (that's what `preloaded` is for), it only
            // has to hand the whole-run cache back to `run_test_loop`
            // for the NEXT file.
            let res <-
                match preloaded {
                    Option.some already => do { return (Result.ok already) },
                    Option.none => load_file_modules f verbose,
                };
            // Probed once here for both consumers below, and at this def's
            // top level rather than inside the `ok loaded` arm: a `<-` bind
            // nested in a match arm silently falls back to un-elaborated
            // decls (see `compile_test_driver_with`'s own doc comment). It
            // must FOLLOW the bind above, not precede it -- a dotted `<-`
            // bind immediately before a bind whose RHS is a `match` fails to
            // resolve `Monad.bind` (measured; either alone is fine).
            let native <- TargetSpec.native;
            match res {
                err e => do {
                    println ("SKIP  " ++ f ++ " (" ++ e ++ ")");
                    run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed, skipped := skipped + 1, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
                },
                ok loaded => do {
                    // The per-binary result file the driver writes its
                    // `__MONAD_TEST__ <failed>` marker to (see
                    // test_driver.mo's synthesis header). Unique per
                    // linked binary (`bin_idx` is bumped only when a
                    // binary is actually linked, so no two files ever
                    // share one) and per process (the out dir is
                    // pid-unique), so a driver that dies before writing
                    // leaves either no file or its OWN missing one --
                    // never a sibling's count.
                    let result_path : String := out_dir ++ "/monad_test_result_" ++ I64.to_string bin_idx ++ ".txt";
                    let ir_res <- compile_loaded_modules_to_test_ir loaded result_path native.triple;
                    match ir_res {
                        err e => do {
                            // Three outcomes, not two. A driver that
                            // cannot be built used to be counted as
                            // `skipped` whatever the reason, and
                            // `skipped` affects no exit code -- so a
                            // file that genuinely stopped compiling
                            // passed CI silently. The Rust reference
                            // books an uncompilable file as `failed: 1`
                            // (`core/src/lib.rs`), and so does this
                            // now, EXCEPT for the two cases that are
                            // not failures:
                            //
                            //   SKIP  the file has no #[test] defs at
                            //         all -- benign and expected
                            //         (matched by full equality, since
                            //         an instance error starts with the
                            //         same `no `; see
                            //         `is_no_tests_error`).
                            //   FAIL  anything else -- exit 1.
                            if is_no_tests_error e then do {
                                println ("SKIP  " ++ f ++ " (" ++ e ++ ")");
                                run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed, skipped := skipped + 1, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
                            } else do {
                            println ("[31mFAIL  " ++ f ++ " (" ++ e ++ ")[0m");
                            run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed + 1, skipped := skipped, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
                            }
                        },
                        ok ir_result => do {
                            let total : I64 := ir_result.total_tests;
                            // No exit-code ceiling any more: the count
                            // now travels in the result FILE as decimal
                            // text (`lang/src/parser.mo`, at 288 tests,
                            // was the one corpus file the old 8-bit
                            // exit-code channel had to refuse outright).
                            let ir_text := emit_module ir_result.mod_;
                            let bin_name := "monad_test_bin_" ++ I64.to_string bin_idx;
                            // Both always non-empty by construction --
                            // `out_dir` (see `run_test`'s own caller) and
                            // `bin_name` (a literal prefix + counter) --
                            // `Path.path` directly, not `Path.of`.
                            //
                            // The mote's `[link] libs` travel with the
                            // loaded set here exactly as they do on the
                            // compile path (`compile_file_codegen`): the
                            // set holds the TEST file's own module
                            // (`load_module_with_info` conses it onto its
                            // dependency closure), so `collect_link_libs`
                            // discovers this file's mote the same way. A
                            // test calling an `#[extern "c"]` binding
                            // whose symbol lives in a declared library
                            // (libm, say) gets the same `-l<name>` the
                            // `run`/`compile` path passes, instead of an
                            // `undefined reference` at link.
                            let link_libs : List String <- collect_link_libs (get_loaded_all loaded);
                            let runtime_src : String <- resolve_runtime_src (extract_directory f);
                            let link_result <- link_ir { runtime_c := runtime_src,
                                ir_text := ir_text,
                                ir_path := resolve_ir_path Option.none (Path.path out_dir) (Path.path bin_name),
                                output_dir := (Path.path out_dir),
                                output_name := (Path.path bin_name),
                                link_libs := link_libs, compiler_commit := build_commit,
                                verbose := verbose, spec := native };
                            if not (link_result == 0) then do {
                                // A file-level failure, counted as such:
                                // no test in it ever ran, so folding it
                                // into the per-test totals would invent
                                // results that do not exist. A recorded
                                // gap can fail HERE rather than at the
                                // driver compile -- `init/src/tests.mo`
                                // did, on an llc-rejected call to an
                                // undefined `@Pred` -- `llc`'s own message
                                // is not available here (it went to the
                                // console), so what is reported is this
                                // branch's own wording.
                                println ("[31mFAIL  " ++ f ++ " (compilation failed)[0m");
                                run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx + 1, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed + 1, skipped := skipped, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
                            } else do {
                                let bin_path := out_dir ++ "/" ++ bin_name;
                                // The driver's authoritative report is
                                // its result FILE, not its exit code
                                // (see test_driver.mo): it writes
                                // `__MONAD_TEST__ <failed>` to
                                // `result_path` right before returning.
                                // Read it back -- but only after
                                // checking the file EXISTS: the native
                                // read passes a missing file's NULL
                                // straight through as a String, and any
                                // operation on that NULL crashes the
                                // parent too.
                                let exit_code <- exec_cmd bin_path [];
                                let exists : Bool <- file_exists (Path.path result_path);
                                // Annotated, and the sweep that removed this
                                // file's other 13 do-bind annotations kept
                                // this one: the RHS is an `if` with two `do`
                                // branches, whose `IO` carrier is not resolved
                                // at this call, so without the annotation the
                                // bind below has no type and the checker
                                // reports `type mismatch: expected A, found
                                // I64 in run_test_loop_codegen`. Measured; the
                                // annotation is load-bearing, not historical.
                                let parsed : Option I64 <- if exists then do {
                                    let raw : String <- read_file (Path.path result_path);
                                    return (parse_driver_result raw)
                                } else do {
                                    return Option.none
                                };
                                // Bad = the driver died before writing a
                                // usable report: a signal death reaches
                                // `exec_cmd` as -1 (never forgiven by a
                                // parseable file -- the out dir is
                                // pid-unique, but a pid-collision reuse
                                // could otherwise resurrect a stale
                                // marker), a normal exit with a
                                // missing or unparseable file is a
                                // driver that skipped the write, and a
                                // count above the file's own total can
                                // only be garbage.
                                let unusable : Bool := match parsed {
                                    Option.some failed => I64.gt failed total,
                                    Option.none => true,
                                };
                                let bad : Bool := I64.lt exit_code 0 || unusable;
                                if bad then do {
                                    // A driver that died is normally a
                                    // real failure -- but a gap can also
                                    // be a RUNTIME one (the BEq (List A)
                                    // dictionary bug kills
                                    // std/src/sha256_tests.mo here, long
                                    // after it compiles), so the same
                                    // path-and-cause test applies. The
                                    // cause is the message this branch
                                    let why : String := "driver exited " ++ I64.to_string exit_code;
                                    println ("[31mFAIL  " ++ f ++ " (" ++ why ++ ")[0m");
                                    run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx + 1, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed + 1, skipped := skipped, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
                                } else do {
                                    // `bad` is false, so `parsed` is
                                    // `Option.some failed` with
                                    // 0 <= failed <= total -- the match's
                                    // other arm is unreachable, present
                                    // only so the bind has a total type.
                                    let failed : I64 := match parsed {
                                        Option.some failed2 => failed2,
                                        Option.none => 0,
                                    };
                                    run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx + 1, tests_passed := tests_passed + (total - failed), tests_failed := tests_failed + failed, files_failed := files_failed, skipped := skipped, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
                                }
                            }
                        }
                    }
                }
            }
}

// `Command` and its argv parser are hand-written (not `#[derive_cli]`) and
// this file stays free of any macro/attribute-derive syntax on purpose:
// cli/src/main.mo is one of the files the self-hosted parse/scope/typecheck
// test suite (slow_tests/parser_file_tests.mo, scope_all_tests.mo,
// typecheck_lang_tests.mo) re-parses with that self-hosted pipeline, and it is
// the file the bootstrap itself is built from — an attribute here would be
// load-bearing for the compiler building itself. `#[derive_cli]` was NOT the
// reason: it has worked self-hosted since `ae3a457`, and this comment claimed
// otherwise long after that. It does share `cli/src/args.mo`'s small runtime
// helpers with the macro-derived demo in motes/clap/src/tests/cli_derive_tests.mo,
// though — same argv-munging primitives either way.
type Command {
    build (file: Path) (out_name: Path) (bin: String) (verbose: Bool) (debug: Bool) (no_cache: Bool) (target: String),
    run (file: Path) (verbose: Bool) (debug: Bool),
    eval (file: Path) (verbose: Bool),
    pretty (file: String),
    check (files: List String) (opts: CheckOptions),
    test (files: List String) (verbose: Bool) (workspace: Bool),
    /// `monad clean [--all] [--target-dir <dir>]`. Removes the output
    /// directories under `<target-dir>` -- the profile directories -- and
    /// leaves the store; `--all` is the other verb, `<target-dir>` itself.
    clean (all: Bool) (target_dir: String),
    /// `monad gc [<path>...] [--workspace/-w] [--apply] [--target-dir <dir>]`.
    /// Dry run unless `--apply`; removes only what the named files cannot
    /// reach, and refuses to remove anything at all when it cannot derive
    /// a complete reachable set.
    gc (files: List String) (workspace: Bool) (apply: Bool) (target_dir: String),
    /// `monad store ls|verify [--target-dir <dir>]`.
    store (sub: String) (target_dir: String),
    /// `monad print-targets`: the triples `--target` accepts, which of them
    /// this llc can actually build for, and what this machine's own target is.
    print_targets,
    lsp,
    version,
    help
}

/// `compile <path> [name]` (original positional form) and `compile <path>
/// [--output/-o <name>] [--verbose/-v] [--debug/-g] [--release]` (flag
/// form) both work; an explicit `--output`/`-o` wins over a positional
/// name if both are given. DWARF debug info (plans/bootstrapping/
/// debug-info.md: one location per def, plus per-term locations once
/// stage 3 landed) is ON BY DEFAULT, like rustc's dev profile: a debug
/// build is what you want from a compile unless you asked for a release
/// one, and the flag is how you ask. `--release` opts out;
/// `--debug`/`-g` stays accepted as an explicit opt-in and wins over
/// `--release` if both are given (asking twice, with the more specific
/// request, is not an error).
def Command.from_args (args : List String) : Command :=
    match args {
        List.cons cmd rest =>
            if cmd == "build" then
                match Cli.take_flag "verbose" "v" rest {
                    Cli.FlagResult.flag_result verbose rest1 =>
                        match Cli.take_flag "debug" "g" rest1 {
                            Cli.FlagResult.flag_result debug_explicit rest1a =>
                                match Cli.take_flag "release" "" rest1a {
                                    Cli.FlagResult.flag_result release rest1b =>
                                        // Debug info defaults ON (rustc's own
                                        // dev-profile default): `--release`
                                        // opts out, an explicit `--debug`/
                                        // `-g` opts back in over it.
                                        let debug := if debug_explicit then true else not release in
                                        // Peeled here rather than after the
                                        // positionals, for the reason `check`
                                        // gives: `--no-cache` is a flag, not a
                                        // path, and left in the list it would be
                                        // handed to the path expander as a
                                        // filename.
                                        match Cli.take_flag "no-cache" "" rest1b {
                                            Cli.FlagResult.flag_result no_cache rest1c =>
                                        // `--bin <name>` selects among a mote's
                                        // `[[bin]]` targets. Peeled with the
                                        // other flags, for the same reason:
                                        // left in the list, `--bin` would be
                                        // handed to the positional reader as a
                                        // path and its NAME as the output name.
                                        match Cli.take_opt "bin" "" "" rest1c {
                                            Cli.OptResult.opt_result bin_name rest1d =>
                                        // `--target <triple>` is what to build
                                        // FOR, and it is peeled with the other
                                        // flags for the same reason: left in
                                        // the list, `--target` is read as the
                                        // positional path and its TRIPLE as
                                        // the output name. Space-separated
                                        // only -- `Cli.take_opt` has no
                                        // `--target=<triple>` form.
                                        match Cli.take_opt "target" "" "" rest1d {
                                            Cli.OptResult.opt_result target_name rest1e =>
                                        match Cli.take_opt "output" "o" "" rest1e {
                                    Cli.OptResult.opt_result opt_out_name rest2 =>
                                        match Cli.take_positional rest2 {
                                            Cli.PosResult.pos_result path_opt rest3 =>
                                                match Cli.take_positional rest3 {
                                                    Cli.PosResult.pos_result name_opt _ =>
                                                        let out_name :=
                                                            if String.is_empty opt_out_name then
                                                                match name_opt {
                                                                    Option.some n => n,
                                                                    Option.none => "source",
                                                                }
                                                            else
                                                                opt_out_name
                                                        in
                                                        // No positional path means the mote containing the
                                                        // working directory -- the same default `check` and
                                                        // `test` already have. Reached by handing `.` to
                                                        // `build_target`, whose `Mote.discover` walks up from
                                                        // there, so `monad build` and `monad build .` are one
                                                        // spelling of one thing rather than two code paths.
                                                        let path : String := match path_opt {
                                                            Option.some p => p,
                                                            Option.none => ".",
                                                        } in
                                                        // A path/out_name that fails to validate (currently:
                                                        // only the empty string) falls back to `Command.help`.
                                                        match Path.of path {
                                                            err _ => Command.help,
                                                            ok p => match Path.of out_name {
                                                                err _ => Command.help,
                                                                ok o => Command.build p o bin_name verbose debug no_cache target_name,
                                                            },
                                                        },
                                                },
                                        },
                                            },
                                            },
                                },
                                            },
                        },
                },
                }
            else if cmd == "run" then
                match Cli.take_flag "verbose" "v" rest {
                    Cli.FlagResult.flag_result verbose rest1 =>
                        match Cli.take_flag "debug" "g" rest1 {
                            Cli.FlagResult.flag_result debug_explicit rest1a =>
                                match Cli.take_flag "release" "" rest1a {
                                    Cli.FlagResult.flag_result release rest1b =>
                                        let debug := if debug_explicit then true else not release in
                                        match Cli.take_positional rest1b {
                                            Cli.PosResult.pos_result path_opt _ =>
                                                match path_opt {
                                                    Option.some path =>
                                                        match Path.of path {
                                                            err _ => Command.help,
                                                            ok p => Command.run p verbose debug,
                                                        },
                                                    Option.none => Command.help,
                                                },
                                        },
                                },
                        },
                }
            else if cmd == "eval" then
                match Cli.take_flag "verbose" "v" rest {
                    Cli.FlagResult.flag_result verbose rest1 =>
                        match Cli.take_positional rest1 {
                            Cli.PosResult.pos_result path_opt _ =>
                                match path_opt {
                                    Option.some path =>
                                        match Path.of path {
                                                            err _ => Command.help,
                                                            ok p => Command.eval p verbose,
                                                        },
                                    Option.none => Command.help,
                                },
                        },
                }
            else if cmd == "pretty" then
                match Cli.take_positional rest {
                    Cli.PosResult.pos_result path_opt _ =>
                        match path_opt {
                            Option.some path => Command.pretty path,
                            Option.none => Command.help,
                        },
                }
            else if cmd == "check" then
                match Cli.take_flag "verbose" "v" rest {
                    Cli.FlagResult.flag_result verbose rest1 =>
                        // Same peeling order as `test` below, and for
                        // the same reason: `--workspace` is a flag, not
                        // a path, and left in the list it would be
                        // handed to the path expander as a filename.
                        // It is also what replaced the old
                        // "no paths -> `Command.help`" arm: a bare
                        // `monad check` is now the mote-containing-the-
                        // CWD mode, so emptiness is `run_check`'s
                        // question, not this one's.
                        match Cli.take_flag "workspace" "w" rest1 {
                            Cli.FlagResult.flag_result workspace rest2 =>
                                // `--no-cache` is peeled here for the same
                                // reason `--workspace` is: it is a flag,
                                // not a path, and left in the list it
                                // would be handed to the path expander as
                                // a filename.
                                match Cli.take_flag "no-cache" "" rest2 {
                                    Cli.FlagResult.flag_result no_cache rest3 =>
                                        // `--affine`: promote the M2 usage
                                        // rule's advisory diagnostics
                                        // (copy_required /
                                        // value_used_after_move /
                                        // linear_unused,
                                        // lang/typecheck/affine.mo) to hard
                                        // failures — the same check, one
                                        // more rule. No short form: it is
                                        // a corpus-migration flag, not a
                                        // daily one.
                                        match Cli.take_flag "affine" "" rest3 {
                                            Cli.FlagResult.flag_result affine rest4 =>
                                                let opts : CheckOptions := { verbose := verbose, workspace := workspace, no_cache := no_cache, affine := affine } in
                                                Command.check rest4 opts,
                                        },
                                },
                        },
                }
            else if cmd == "test" then
                match Cli.take_flag "verbose" "v" rest {
                    Cli.FlagResult.flag_result verbose rest1 =>
                        // `--workspace` is peeled BEFORE the emptiness
                        // test: it is a flag, not a path, and left in
                        // `rest1` it would both defeat the "no paths
                        // given" branch and be handed to the path
                        // expander as a filename.
                        match Cli.take_flag "workspace" "w" rest1 {
                            Cli.FlagResult.flag_result workspace rest2 =>
                                Command.test rest2 verbose workspace,
                        },
                }
            else if cmd == "clean" then
                // `--all` is peeled before `--target-dir` for the reason
                // `check` gives for its own two flags: a flag left in the
                // list is handed to whatever comes next as if it were a
                // path. Nothing takes a positional here, so the remainder
                // is deliberately dropped rather than validated.
                match Cli.take_flag "all" "" rest {
                    Cli.FlagResult.flag_result all rest1 =>
                        match Cli.take_opt "target-dir" "" "" rest1 {
                            Cli.OptResult.opt_result target_dir _rest2 =>
                                Command.clean all target_dir,
                        },
                }
            else if cmd == "gc" then
                // The positionals are NOT peeled here: unlike `clean`,
                // this verb takes paths, and `rest3` is exactly the list
                // `resolve_target_paths` wants. An empty one means "the
                // mote containing the working directory", the same
                // default `check` has.
                match Cli.take_flag "workspace" "w" rest {
                    Cli.FlagResult.flag_result workspace rest1 =>
                        match Cli.take_flag "apply" "" rest1 {
                            Cli.FlagResult.flag_result apply rest2 =>
                                match Cli.take_opt "target-dir" "" "" rest2 {
                                    Cli.OptResult.opt_result target_dir rest3 =>
                                        Command.gc rest3 workspace apply target_dir,
                                },
                        },
                }
            else if cmd == "store" then
                // `ls`/`verify` is a positional, and the flag has to be
                // taken out from around it first -- `take_opt` walks the
                // whole list, so `monad store ls --target-dir x` and
                // `monad store --target-dir x ls` both land here.
                match Cli.take_opt "target-dir" "" "" rest {
                    Cli.OptResult.opt_result target_dir rest1 =>
                        match Cli.take_positional rest1 {
                            Cli.PosResult.pos_result sub_opt _rest2 =>
                                match sub_opt {
                                    Option.some sub => Command.store sub target_dir,
                                    Option.none => Command.help,
                                },
                        },
                }
            else if cmd == "print-targets" then
                Command.print_targets
            else if cmd == "lsp" then
                Command.lsp
            else if cmd == "version" then
                Command.version
            else
                Command.help,
        List.empty => Command.help,
    }

/// Current main entrypoint of self hosted compiler
def main (args : List String) : IO I64 {
    let cmd : Command := Command.from_args args;
    match cmd {
        build file_path out_name bin verbose debug no_cache target_name => do {
            // Resolved HERE rather than in `from_args`, which is pure and
            // has no IO to probe a toolchain with. An empty name is this
            // machine, and a name this compiler does not know is still taken
            // verbatim (see `TargetSpec.resolve`); `--print-targets` is what
            // answers "can this toolchain build that?".
            let resolved <- TargetSpec.resolve target_name;
            match resolved {
                Result.err m => do {
                    println m;
                    return 1
                },
                Result.ok target => do {
                    // A directory is a mote to build (`build_target`); a file
                    // goes straight to `compile_file`.
                    build_target { path := Path.to_string file_path,
                        out_name := Path.to_string out_name, bin := bin,
                        verbose := verbose, debug := debug, no_cache := no_cache,
                        spec := target }
                },
            }
        },
        run file_path verbose debug => do {
            run_file (Path.to_string file_path) default_output_dir verbose debug
        },
        eval file_path verbose => do {
            eval_file (Path.to_string file_path) verbose
        },
        pretty file_path => do {
            // Prints the TARGET FILE's own declarations, pretty-printed
            // back to source text via `lang.pretty.show_decls`. Only
            // `file_path`'s own decls are shown (not its transitive `use`
            // dependencies), matching `ModuleInfo.decl_list`'s existing
            // "this module's own decls only" convention (see
            // `lang/codegen/test_driver.mo`'s `discover_test_defs` for the
            // same convention elsewhere) — so this loads just the ONE
            // target module (`load_module_with_info`, no dependency walk
            // at all) rather than `load_file_modules`'s full transitive
            // closure (prelude/init/everything), which this command used
            // to pay for in full only to discard all of it but the
            // target's own decls.
            let base_dir : String := extract_directory file_path;
            let module_name : String := module_name_from_path file_path;
            let mp : ModulePath := ModulePath.mp [Identifier.id module_name];
            let module_opt <- load_module_with_info base_dir mp;
            match module_opt {
                Option.some mi => do {
                    let decls := mi.decl_list;
                    println (show_decls decls);
                    return 0
                },
                Option.none => do {
                    println ("Failed to parse " ++ file_path);
                    return 1
                }
            }
        },
        check files opts => do {
            run_check files opts
        },
        test files verbose workspace => do {
            run_test_paths files workspace (Path.to_string default_output_dir) verbose
        },
        clean all target_dir => do {
            run_clean all target_dir
        },
        gc files workspace apply target_dir => do {
            run_gc files workspace apply target_dir
        },
        store sub target_dir => do {
            run_store sub target_dir
        },
        print_targets => run_print_targets,
        lsp => lsp_serve,
        version => do {
            println build_commit;
            return 0
        },
        help => do {
            print_help
        }
    }
}

/// `monad print-targets`. The tabulated targets, each marked when this llc
/// cannot build for it; then this machine's own target (what no `--target`
/// means); then llc's whole registered architecture list, which is what
/// `--target` is validated against.
#[partial]
def run_print_targets : IO I64 := do {
    let archs <- TargetSpec.registered_archs;
    let native <- TargetSpec.native;
    println "Targets this compiler has a measured spelling for:";
    println (TargetSpec.describe_all archs TargetSpec.known_targets);
    println (String.concat "This machine: " (String.concat native.triple "  (what no --target builds for)"));
    println "Architectures this llc registers (--target accepts any target built on one):";
    println (TargetSpec.arch_line archs);
    return 0
}

#[partial]
def print_help : IO I64 {
    println "Monad is in alpha mode and under heavy development.";
    println "Expect breaking changes, bugs, and incomplete features.";
    println "";
    println "Usage: monad build [<path>] [name] [--bin <name>] [--output/-o <name>] [--target <triple>] [--verbose/-v] [--debug/-g] [--release] [--no-cache]";
    println "         Compile a .mo source file, or a mote, to a native binary";
    println "         <path> may be a mote DIRECTORY, in which case its [[bin]] target is built";
    println "           (`monad build cli` builds cli/src/main.mo as `monad`)";
    println "         --bin <name> picks one when several [[bin]] targets exist on disk";
    println "           (a mote declares none, but builds `src/main.mo` as its own name, when";
    println "            `src/main.mo` exists and no [[bin]] table does)";
    println "         With no <path>, builds the mote containing the working directory";
    println "         --verbose/-v prints each module as it loads and one line per pipeline stage";
    println "         --debug/-g emits DWARF debug info (one source location per top-level def)";
    println "         --target <triple> builds for another target (space-separated: --target=x does not parse)";
    println "           `monad print-targets` lists the spellings this compiler has measured";
    println "         --no-cache (or MONAD_NO_CACHE) compiles for real, reading and writing no store entry";
    println "       monad run <path> [--verbose/-v] [--debug/-g] [--release]  Compile and execute a .mo source file";
    println "       monad eval <path> [--verbose/-v]  Evaluate a .mo source file using the built-in interpreter (pure programs only)";
    println "       monad pretty <path>  Parse and pretty print a .mo source file";
    println "       monad check [<path>...] [--workspace/-w] [--verbose/-v] [--no-cache] [--affine]  Parse and typecheck .mo source files (no execution)";
    println "         Any <path> that's a directory is recursively expanded to its *.mo files";
    println "         With no <path>, checks the mote containing the working directory";
    println "         --workspace/-w checks every mote in the enclosing workspace";
    println "           (only directories that ARE motes: examples/ has no manifest)";
    println "         --verbose/-v prints a per-declaration progress trace while checking";
    println "         Results are cached under <target-dir>/check for multi-file runs, keyed on";
    println "           the file, its mote's whole declared closure, and the running compiler";
    println "         --no-cache (or MONAD_NO_CACHE) skips the cache; a single-file run always does";
    println "         --affine also fails on affine over-uses (used 2+ times without a";
    println "           Copy instance) — the existing diagnostics, promoted to errors;";
    println "           it also disables the check cache (a stored entry records the";
    println "           ordinary check's result, which has no affine verdict in it)";
    println "       monad test [<path>...] [--workspace/-w] [--verbose/-v]  Compile and run each file's own #[test] defs as a native binary";
    println "         Any <path> that's a directory is recursively expanded to its *.mo files";
    println "         With no <path>, tests the mote containing the working directory";
    println "         --workspace/-w tests every mote in the enclosing workspace";
    println "           (only directories that ARE motes: examples/ has no manifest)";
    println "         --verbose/-v prints per-file timing and module-cache statistics";
    println "         A file with no #[test]s is skipped, not failed";
    println "       monad clean [--all] [--target-dir <dir>]  Remove build output, keeping the store";
    println "         Removes every output directory under <target-dir> (the profile directories)";
    println "         --all removes <target-dir> itself, the store included";
    println "       monad gc [<path>...] [--workspace/-w] [--apply] [--target-dir <dir>]  Remove store entries the named files cannot reach";
    println "         Dry run by default; --apply removes them. Takes the same <path> forms as check";
    println "         Refuses to remove ANYTHING when it cannot derive a complete reachable set,";
    println "           because an incomplete one would delete the store itself";
    println "       monad store ls|verify [--target-dir <dir>]  List the store, or check its entries";
    println "         Each line is <kind> <key> <bytes> <state>; an artifact is its binary AND its IR";
    println "         verify is structural: an entry records neither the file nor the sources behind";
    println "           it, so it checks that an entry is complete and readable, not that its key";
    println "           is the right key. It exits non-zero on any incomplete entry";
    println "       monad print-targets  List the triples --target accepts, and what this llc can build for";
    println "         Each is the spelling the emitter writes; `(llc ...)` adds the argv when llc needs more";
    println "         A --target name whose architecture this llc does not register is rejected by name";
    println "       monad lsp  Speak the Language Server Protocol on stdin and stdout, until stdin ends";
    println "         Started by an editor, which is told nothing else: no arguments, no flags";
    println "       monad version  Print the git commit this binary was built from";
    return 0
}
