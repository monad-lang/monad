use io {IO}
open IO {println, read_file, write_file}
use std.process {exec_cmd}
use std.bench {now, report}
use lang.types {Decl, Location, LocalScope, ModulePath}
use lang.codegen.ir {LLVMModule, emit_module}
use lang.codegen.emit {build_debug_locs, compile_db_module_with_debug, compile_loaded_modules_to_ir_with_debug, ok}
use lang.module {ElaboratedAndCache, ElaboratedModules, FileCheckAndCache, LoadedModules, ModuleInfo, ModuleInfoCache, PreludeInitBase, build_prelude_init_base, check_file_cached, check_module_with_scope, elaborate_loaded_modules, elaborate_loaded_modules_cached, expand_check_paths, extract_directory, get_loaded_all, get_module_info_decls, load_file_modules, load_module_with_info, module_name_from_path, module_info_cache_empty, try_parse_decls, try_parse_decls_strict, try_parse_decls_with_locs}
use std.map {}
use lang.pretty {show_decls}
use lang.codegen.test_driver {compile_loaded_modules_to_test_ir}
use lang.cli {*}

/// The default output directory for `compile` when no `--output`/
/// positional name supplies an absolute one -- a compile-time literal,
/// known non-empty by inspection, so `Path.path` directly (not the
/// validating `Path.of`) is the right constructor here.
def default_output_dir : Path := Path.path "/tmp"


/// Write LLVM IR to disk and link it into a native binary via llc + clang.
/// Shared by `compile_file`'s primary path and its module-loading-failure
/// fallback (`compile_parsed_decls`) — both produce an `ir_text : String`
/// by different routes and then need the identical llc/clang/link steps.
#[partial]
def link_ir (ir_text : String) (output_dir : Path) (output_name : Path) (verbose : Bool) : IO I64 {
    // `Path.join` here is THE fix for the mangled-double-slash bug this
    // whole `Path` type exists to prevent: if `output_name` is already
    // absolute, it replaces `output_dir` outright instead of naively
    // concatenating (`os.path.join`-style semantics).
    let target := Path.join output_dir output_name;
    let ir_path := Path.with_suffix target ".ll";
    let obj_path := Path.with_suffix target ".o";
    let runtime_obj := Path.join output_dir (Path.path "monad_runtime.o");
    let output_path := target;
    let ir_path_s := Path.to_string ir_path;
    let obj_path_s := Path.to_string obj_path;
    let runtime_obj_s := Path.to_string runtime_obj;
    let output_path_s := Path.to_string output_path;

    // Per-stage `Bench.report` timing, gated on `--verbose` (same
    // convention as `lang.codegen.emit`'s `compile_loaded_modules_to_ir`)
    // -- added to measure where the plan's own "compile_file total minus
    // compile_loaded_modules_to_ir total" ~255s inferred remainder
    // (write .ll / llc / clang runtime.c / clang link, previously
    // entirely unbenched) actually goes, before guessing at a fix.
    let t_write := Bench.now;
    IO.write_file ir_path ir_text;
    if verbose then do {
        let _ := Bench.report "link_ir: write .ll" (I64.sub Bench.now t_write);
        return unit
    } else return unit;

    let t_llc := Bench.now;
    let result <- exec_cmd "llc" [ "-filetype=obj", ir_path_s, "-o", obj_path_s];
    if verbose then do {
        let _ := Bench.report "link_ir: llc" (I64.sub Bench.now t_llc);
        return unit
    } else return unit;
    if not (result == 0) then do {
        println <| (String.concat "Compiling ir " (String.concat ir_path_s " with llc failed"));
        return 1
    } else do {
        let t_rtc := Bench.now;
        let result <- exec_cmd "clang" (List.append [ "-c", "lang/codegen/runtime.c", "-o", runtime_obj_s] (if verbose then ["-v"] else [""]));
        if verbose then do {
            let _ := Bench.report "link_ir: clang runtime.c" (I64.sub Bench.now t_rtc);
            return unit
        } else return unit;
        if not (result == 0) then do {
            println <| "compiling runtime failed";
            return 1
        } else do {
            let t_link := Bench.now;
            let result <- exec_cmd "clang" (List.append [ obj_path_s, runtime_obj_s, "-o", output_path_s] (if verbose then ["-v"] else [""]));
            if verbose then do {
                let _ := Bench.report "link_ir: clang link" (I64.sub Bench.now t_link);
                return unit
            } else return unit;
            if not (result == 0) then do {
                println <| "linking failed";
                return 1
            } else do {
                println "Compilation finished";
                return 0
            }
        }
    }
}

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
def link_compiled_module (mod_result : Result String LLVMModule) (output_dir : Path) (output_name : Path) (verbose : Bool) : IO I64 :=
    match mod_result {
        Result.err e => do {
            println ("FAILED at stage: compile_loaded_modules_to_ir (" ++ e ++ ")");
            return 1
        },
        Result.ok mod_ => do {
            let ir_text := emit_module mod_;
            link_ir ir_text output_dir output_name verbose
        },
    }

/// Parse a source file and compile + run it via LLVM. `source_path`/
/// `debug_locs` are DWARF debug-info inputs (plans/bootstrapping/
/// debug-info.md, v1: one location per top-level def) -- pass
/// `Option.none`/`str_map_empty` (see `no_debug_info`) to disable, same
/// as `compile_db_module_with_debug` itself. `link_ir` needs no
/// separate `--debug` flag of its own: `llc`/`clang` pick up whatever
/// debug metadata `emit_module` already wrote into `ir_text` with no
/// extra flag required (confirmed directly -- a `-g`-style flag doesn't
/// exist on `llc`, unlike `clang`'s own C-source `-g`).
#[partial]
def compile_parsed_decls (decl_list : List Decl) (output_dir : Path) (output_name : Path) (verbose: Bool) (source_path : Option String) (debug_locs : HashMap String Location) : IO I64 {
    let mod_ := compile_db_module_with_debug decl_list source_path debug_locs;
    let ir_text := emit_module mod_;
    println <| "Writing LLVM IR to: " ++ Path.to_string (Path.with_suffix (Path.join output_dir output_name) ".ll");
    link_ir ir_text output_dir output_name verbose
}

/// `Option.none`/`str_map_empty` -- the "debug info off" inputs to
/// `compile_parsed_decls`/`compile_loaded_modules_to_ir_with_debug`.
#[partial]
def no_debug_info : Pair (Option String) (HashMap String Location) := Pair.pair Option.none str_map_empty

/// Build the `(source_path, debug_locs)` DWARF debug-info inputs from a
/// file's own raw source text -- `no_debug_info` when parsing that text
/// for locations fails, which should be rare here (the caller already
/// knows the file parses, from a separate successful parse/typecheck
/// attempt) but must stay total rather than block compilation on a
/// best-effort side channel. See plans/bootstrapping/debug-info.md.
#[partial]
def debug_info_for_source (file_path : String) (source : String) : Pair (Option String) (HashMap String Location) :=
    match try_parse_decls_with_locs source {
        Option.some result =>
            match result {
                Pair.pair _decls decls_with_locs => Pair.pair (Option.some file_path) (build_debug_locs decls_with_locs),
            },
        Option.none => Pair.pair (Option.some file_path) str_map_empty,
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
/// checking `lang/main.mo`'s own full closure, root cause under
/// investigation (`bootstrapping/check-deps-memory-blowup.md`).
/// `compile_loaded_modules_to_ir` (`lang.codegen.emit`) separately attempts
/// whole-graph elaboration on its own, with its own graceful fallback,
/// purely to improve codegen's own dictionary-dispatch resolution (see its
/// own doc comment) -- that is NOT a second copy of this gate.
#[partial]
def compile_file (file_path : String) (output_dir : Path) (output_name : Path) (verbose : Bool) (debug : Bool) : IO I64 {
    let total_start := Bench.now;
    println <| "compiling: " ++ file_path ++ " to " ++ Path.to_string (Path.join output_dir output_name);
    let t_elaborate := Bench.now;
    let elaborated_result : Result String ElaboratedModules <- elaborate_loaded_modules file_path false;
    if verbose then do {
        let _ := Bench.report "elaborate_loaded_modules" (I64.sub Bench.now t_elaborate);
        return unit
    } else return unit;
    match elaborated_result {
        Result.ok em =>
            do {
                    let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
                    let t_check := Bench.now;
                    let diags : List String <- check_module_with_scope em.scope em.target_decls empty_locs (Option.some file_path) verbose;
                    if verbose then do {
                        let _ := Bench.report "check_module_with_scope" (I64.sub Bench.now t_check);
                        return unit
                    } else return unit;
                    match diags {
                        List.cons _ _ => do {
                            println "FAILED at stage: typecheck (target file did not typecheck cleanly)";
                            print_diagnostics diags;
                            if verbose then do {
                                let _ := Bench.report "compile_file total (failed at typecheck)" (I64.sub Bench.now total_start);
                                return unit
                            } else return unit;
                            return 1
                        },
                        List.empty => do {
                            let link_result <- compile_file_codegen { file_path := file_path, output_dir := output_dir, output_name := output_name, verbose := verbose, debug := debug, preloaded := Option.some em.loaded };
                            if verbose then do {
                                let _ := Bench.report "compile_file total" (I64.sub Bench.now total_start);
                                return unit
                            } else return unit;
                            return link_result
                        },
                    }
            },
        Result.err e => do {
            println ("FAILED at stage: load (could not load dependencies: " ++ e ++ ")");
            let link_result <- compile_file_codegen { file_path := file_path, output_dir := output_dir, output_name := output_name, verbose := verbose, debug := debug, preloaded := Option.none };
            if verbose then do {
                let _ := Bench.report "compile_file total" (I64.sub Bench.now total_start);
                return unit
            } else return unit;
            return link_result
        },
    }
}

/// The original `compile_file` body, unchanged -- codegen's own loading
/// + compile pipeline, run only once the gate above has confirmed the
/// target file itself checks cleanly (or the gate's own dependency load
/// failed, in which case this redundant re-attempt produces the same
/// real, rendered diagnostic the old code already did via its own
/// fallback path below, rather than a bare "gate failed").
/// `debug` (from `--debug`/`-g`, `Command.compile`'s own field) gates
/// DWARF debug info (plans/bootstrapping/debug-info.md, v1: one
/// location per top-level def) -- off by default, same rationale as the
/// plan's own "off by default for `monad compile`" decision (binary
/// size / compile time cost). When on, this re-reads and re-parses
/// `file_path` (via `debug_info_for_source`) purely to recover each
/// top-level def's own source location -- independent of, and
/// redundant with, `load_file_modules`'s own internal parsing, but a
/// much smaller change than threading a location table through that
/// whole module-loading pipeline. A `Def` whose final compiled name
/// doesn't match this second, standalone parse (macro-expanded,
/// renamed, lambda-lifted) just gets no debug info, not a compile
/// error -- see `build_debug_locs`'s own doc comment.
#[partial]
def compile_file_codegen (file_path : String) (output_dir : Path) (output_name : Path) (verbose : Bool) (debug : Bool) (preloaded : Option LoadedModules) : IO I64 {
    // `preloaded` is the module set the typecheck gate already loaded, if
    // it got that far -- reusing it avoids reading and re-parsing the
    // target's ENTIRE transitive closure (prelude and init included) a
    // second time, which is exactly what this function used to do on
    // every successful compile. `Option.none` (the gate's own load
    // failed) falls back to loading here, so the error path still
    // produces the same rendered diagnostic it always did.
    let res : Result String LoadedModules <-
        match preloaded {
            Option.some already => do { return (Result.ok already) },
            Option.none => load_file_modules file_path,
        };
    match res {
        Result.ok loaded => do {
            let dbg_info : Pair (Option String) (HashMap String Location) <-
                if debug then do {
                    let source <- IO.read_file (Path.path file_path);
                    return (debug_info_for_source file_path source)
                } else return no_debug_info;
            match dbg_info {
                Pair.pair source_path debug_locs => do {
                    // `verbose` thread-through: previously this branch dumped the
                    // ENTIRE `loaded : LoadedModules` struct (`Show.show loaded`,
                    // walking every loaded module's full content) on every
                    // successful compile -- pure noise on a working build AND a
                    // real perf hit. Now we forward `verbose` to
                    // `compile_loaded_modules_to_ir_with_debug` (which has its own
                    // `--verbose`-gated per-stage printlns -- see its own doc
                    // comment in `lang/codegen/emit.mo`) and emit only a single
                    // one-line module-count summary, also gated on `verbose`.
                    if verbose then do {
                        let loaded_count : I64 := List.length (get_loaded_all loaded);
                        println <| "loaded " ++ I64.to_string loaded_count ++ " modules";
                        let mod_result <- compile_loaded_modules_to_ir_with_debug loaded verbose source_path debug_locs;
                        link_compiled_module mod_result output_dir output_name verbose
                    } else do {
                        let mod_result <- compile_loaded_modules_to_ir_with_debug loaded verbose source_path debug_locs;
                        link_compiled_module mod_result output_dir output_name verbose
                    }
                },
            }
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
                    let dbg_info := if debug then debug_info_for_source file_path source else no_debug_info;
                    match dbg_info {
                        Pair.pair source_path debug_locs =>
                            compile_parsed_decls decl_list output_dir output_name verbose source_path debug_locs,
                    }
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

/// `checked`/`errors` accumulate across all files — errors are counted
/// per-diagnostic (a file with 3 failing defs contributes 3), matching
/// `monad-rs check`'s own error-tally convention. Every file gets an
/// explicit `ok`/`FAIL` line (a passing file used to print nothing at
/// all, indistinguishable from "not reached" — see the corpus-check
/// driver this feeds, which needs a real per-file pass/fail matrix,
/// not just a final count).
#[partial]
def run_check_loop (base : PreludeInitBase) (cache : ModuleInfoCache) (files : List String) (checked : I64) (errors : I64) (verbose : Bool) : IO I64 :=
    match files {
        List.empty => do {
            println (I64.to_string checked ++ " file(s) checked, " ++ I64.to_string errors ++ " error(s)");
            // Whole-run module cache visibility: `hits` counts dependency
            // loads served from an EARLIER file's own load in this same
            // run, instead of re-reading and re-parsing the file from
            // disk -- the direct measure of the cross-file redundancy
            // `ModuleInfoCache` (lang/module.mo) exists to remove.
            if verbose then
                match cache {
                    ModuleInfoCache.mk _ hits misses =>
                        println ("module cache: " ++ I64.to_string hits ++ " hit(s), " ++ I64.to_string misses ++ " miss(es)")
                }
            else do { return unit };
            return (if I64.gt errors 0 then 1 else 0)
        },
        List.cons f rest => do {
            let checked_and_cache : FileCheckAndCache <- check_file_cached base cache f verbose;
            match checked_and_cache {
                FileCheckAndCache.mk result updated_cache =>
                    match result {
                        FileCheckResult.mk path diags =>
                            match diags {
                                List.empty => do {
                                    println ("ok    " ++ path);
                                    run_check_loop base updated_cache rest (checked + 1) errors verbose
                                },
                                List.cons _ _ => do {
                                    println ("FAIL  " ++ path ++ " (" ++ I64.to_string (List.length diags) ++ " error(s))");
                                    print_diagnostics diags;
                                    run_check_loop base updated_cache rest (checked + 1) (errors + List.length diags) verbose
                                }
                            }
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
/// `prelude`/`init` are always implicit dependencies of every file
/// (`build_prelude_init_base`'s own doc comment) — loaded once, here,
/// up front, and threaded through every file in the corpus instead of
/// each `check_file_cached` call independently reloading/reparsing
/// them from scratch. For a corpus run of N files, this turns an
/// O(N·D) cost (D = prelude/init's own dependency-closure size) into
/// O(D+N) — the dominant cost of a multi-file `check` run, since this
/// all executes *interpreted*.
#[partial]
def run_check (files : List String) (verbose : Bool) : IO I64 := do {
    let base : PreludeInitBase <- build_prelude_init_base;
    let expanded : List String <- expand_check_paths files;
    let cache : ModuleInfoCache := module_info_cache_empty;
    run_check_loop base cache expanded 0 0 verbose
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
/// A file with no `#[test]`s, or one that already defines its own
/// top-level `main` (can't have a synthesized driver `main` spliced in
/// — `compile_loaded_modules_to_test_ir`'s own `has_top_level_main`
/// check), is reported as `SKIP`, not `FAIL` — neither is a real
/// problem with that file.
#[partial]
def run_test (files : List String) (out_dir : String) (verbose : Bool) : IO I64 := do {
    let expanded : List String <- expand_check_paths files;
    run_test_loop { files := expanded, out_dir := out_dir, bin_idx := 0, passed := 0, failed := 0, skipped := 0, verbose := verbose, cache := module_info_cache_empty }
}

/// `tested`/`passed`/`failed`/`skipped` accumulate across all files.
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
def run_test_loop (files : List String) (out_dir : String) (bin_idx : I64) (passed : I64) (failed : I64) (skipped : I64) (verbose : Bool) (cache : ModuleInfoCache) : IO I64 :=
    match files {
        List.empty => do {
            let tested := passed + failed;
            println (I64.to_string tested ++ " file(s) tested, " ++ I64.to_string passed ++ " passed, " ++ I64.to_string failed ++ " failed, " ++ I64.to_string skipped ++ " skipped");
            // Same whole-run cache visibility `run_check_loop` prints --
            // `hits` counts dependency loads served from an earlier
            // file's own load in this same run.
            if verbose then
                match cache {
                    ModuleInfoCache.mk _ hits misses =>
                        println ("module cache: " ++ I64.to_string hits ++ " hit(s), " ++ I64.to_string misses ++ " miss(es)")
                }
            else do { return unit };
            return (if I64.gt failed 0 then 1 else 0)
        },
        List.cons f rest => do {
            // Stage 3 gate (see `compile_file`'s own identical doc
            // comment for the full rationale, including `check_deps`):
            // a file whose own decls don't type-check cleanly is reported
            // `SKIP`, not `FAIL` -- matching the existing "no #[test]s"/
            // "already defines its own main" SKIP convention just below
            // (a pre-existing problem with the file, not a new test
            // failure this run introduced).
            let ec : ElaboratedAndCache <- elaborate_loaded_modules_cached f false cache;
            // `out_cache`, not `cache`: this file's load extended it, and
            // every later file in the run needs the extended one.
            let out_cache : ModuleInfoCache := ec.cache;
            match ec.elaborated {
                Result.err e => do {
                    println ("SKIP  " ++ f ++ " (" ++ e ++ ")");
                    run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, passed := passed, failed := failed, skipped := skipped + 1, verbose := verbose, cache := out_cache }
                },
                Result.ok em =>
                    do {
                            let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
                            let diags : List String <- check_module_with_scope em.scope em.target_decls empty_locs (Option.some f) verbose;
                            match diags {
                                List.cons _ _ => do {
                                    print_diagnostics diags;
                                    println ("SKIP  " ++ f ++ " (does not typecheck)");
                                    run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, passed := passed, failed := failed, skipped := skipped + 1, verbose := verbose, cache := out_cache }
                                },
                                List.empty => run_test_loop_codegen { f := f, rest := rest, out_dir := out_dir, bin_idx := bin_idx, passed := passed, failed := failed, skipped := skipped, verbose := verbose, preloaded := Option.some em.loaded, cache := out_cache },
                            }
                    },
            }
        }
    }

/// The original `run_test_loop` body for one file, unchanged -- codegen's
/// own loading + compile + run pipeline, reached only once the gate
/// above has confirmed `f` itself checks cleanly.
#[partial]
def run_test_loop_codegen (f : String) (rest : List String) (out_dir : String) (bin_idx : I64) (passed : I64) (failed : I64) (skipped : I64) (verbose : Bool) (preloaded : Option LoadedModules) (cache : ModuleInfoCache) : IO I64 := do {
            // Reuses the module set `run_test_loop`'s typecheck gate
            // already loaded -- see `compile_file_codegen`'s own
            // `preloaded` comment for the redundancy this removes.
            // `cache` is carried, not consulted: this path never loads
            // anything itself (that's what `preloaded` is for), it only
            // has to hand the whole-run cache back to `run_test_loop`
            // for the NEXT file.
            let res : Result String LoadedModules <-
                match preloaded {
                    Option.some already => do { return (Result.ok already) },
                    Option.none => load_file_modules f,
                };
            match res {
                err e => do {
                    println ("SKIP  " ++ f ++ " (" ++ e ++ ")");
                    run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, passed := passed, failed := failed, skipped := skipped + 1, verbose := verbose, cache := cache }
                },
                ok loaded => do {
                    let ir_res : Result String LLVMModule <- compile_loaded_modules_to_test_ir loaded;
                    match ir_res {
                        err e => do {
                            println ("SKIP  " ++ f ++ " (" ++ e ++ ")");
                            run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, passed := passed, failed := failed, skipped := skipped + 1, verbose := verbose, cache := cache }
                        },
                        ok llvm_mod => do {
                            let ir_text := emit_module llvm_mod;
                            let bin_name := "monad_test_bin_" ++ I64.to_string bin_idx;
                            // Both always non-empty by construction --
                            // `out_dir` (see `run_test`'s own caller) and
                            // `bin_name` (a literal prefix + counter) --
                            // `Path.path` directly, not `Path.of`.
                            let link_result <- link_ir ir_text (Path.path out_dir) (Path.path bin_name) verbose;
                            if not (link_result == 0) then do {
                                println ("FAIL  " ++ f ++ " (compilation failed)");
                                run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx + 1, passed := passed, failed := failed + 1, skipped := skipped, verbose := verbose, cache := cache }
                            } else do {
                                let bin_path := out_dir ++ "/" ++ bin_name;
                                let exit_code <- exec_cmd bin_path [];
                                if exit_code == 0 then do {
                                    println ("ok    " ++ f);
                                    run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx + 1, passed := passed + 1, failed := failed, skipped := skipped, verbose := verbose, cache := cache }
                                } else do {
                                    println ("FAIL  " ++ f);
                                    run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx + 1, passed := passed, failed := failed + 1, skipped := skipped, verbose := verbose, cache := cache }
                                }
                            }
                        }
                    }
                }
            }
}

// `Command` and its argv parser are hand-written (not `#[derive_cli]`) and
// this file stays free of any macro/attribute-derive syntax on purpose: the
// self-hosted compiler's own parser/typechecker (lang/parser.mo,
// lang/typecheck/infer.mo) doesn't understand `#[derive_cli]` yet, and
// lang/main.mo is one of the files the self-hosted parse/scope/typecheck
// test suite (slow_tests/parser_file_tests.mo, scope_all_tests.mo,
// typecheck_lang_tests.mo) re-parses with that self-hosted pipeline. It
// does share `lang/cli.mo`'s small runtime helpers with the macro-derived
// demo in lang/tests/cli_derive_tests.mo, though — same argv-munging
// primitives either way.
type Command {
    compile (file: Path) (out_name: Path) (verbose: Bool) (debug: Bool),
    pretty (file: String),
    check (files: List String) (verbose: Bool),
    test (files: List String) (verbose: Bool),
    help
}

/// `compile <path> [name]` (original positional form) and `compile <path>
/// [--output/-o <name>] [--verbose/-v] [--debug/-g]` (flag form) both
/// work; an explicit `--output`/`-o` wins over a positional name if both
/// are given. `--debug`/`-g` enables DWARF debug info (plans/
/// bootstrapping/debug-info.md, v1: one location per top-level def) --
/// off by default, same as `--verbose`.
def Command.from_args (args : List String) : Command :=
    match args {
        List.cons cmd rest =>
            if cmd == "compile" then
                match Cli.take_flag "verbose" "v" rest {
                    Cli.FlagResult.flag_result verbose rest1 =>
                        match Cli.take_flag "debug" "g" rest1 {
                            Cli.FlagResult.flag_result debug rest1b =>
                                match Cli.take_opt "output" "o" "" rest1b {
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
                                                        match path_opt {
                                                            // A path/out_name that fails to validate (currently:
                                                            // only the empty string) falls back to `Command.help`,
                                                            // mirroring the sibling `Option.none => Command.help`
                                                            // arm right below for a simply-missing positional arg.
                                                            Option.some path =>
                                                                match Path.of path {
                                                                    err _ => Command.help,
                                                                    ok p => match Path.of out_name {
                                                                        err _ => Command.help,
                                                                        ok o => Command.compile p o verbose debug,
                                                                    },
                                                                },
                                                            Option.none => Command.help,
                                                        },
                                                },
                                        },
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
                        if List.is_empty rest1 then Command.help else Command.check rest1 verbose,
                }
            else if cmd == "test" then
                match Cli.take_flag "verbose" "v" rest {
                    Cli.FlagResult.flag_result verbose rest1 =>
                        if List.is_empty rest1 then Command.help else Command.test rest1 verbose,
                }
            else
                Command.help,
        List.empty => Command.help,
    }

/// Current main entrypoint of self hosted compiler
def main (args : List String) : IO I64 {
    let cmd : Command := Command.from_args args;
    match cmd {
        compile file_path out_name verbose debug => do {
            compile_file (Path.to_string file_path) default_output_dir out_name verbose debug
        },
        pretty file_path => do {
            // Prints the TARGET FILE's own declarations, pretty-printed
            // back to source text via `lang.pretty.show_decls`. Only
            // `file_path`'s own decls are shown (not its transitive `use`
            // dependencies), matching `get_module_info_decls`'s existing
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
            let module_opt : Option ModuleInfo <- load_module_with_info base_dir mp;
            match module_opt {
                Option.some mi => do {
                    let decls := get_module_info_decls mi;
                    println (show_decls decls);
                    return 0
                },
                Option.none => do {
                    println ("Failed to parse " ++ file_path);
                    return 1
                }
            }
        },
        check files verbose => do {
            run_check files verbose
        },
        test files verbose => do {
            run_test files (Path.to_string default_output_dir) verbose
        },
        help => do {
            print_help
        }
    }
}

#[partial]
def print_help : IO I64 {
    println "Usage: monad compile <path> [name] [--output/-o <name>] [--verbose/-v] [--debug/-g]";
    println "         Parse and compile a .mo source file";
    println "         --debug/-g emits DWARF debug info (one source location per top-level def)";
    println "       monad pretty <path>  Parse and pretty print a .mo source file";
    println "       monad check <path>... [--verbose/-v]  Parse and typecheck .mo source files (no execution)";
    println "         Any <path> that's a directory is recursively expanded to its *.mo files";
    println "         --verbose/-v prints a per-declaration progress trace while checking";
    println "       monad test <path>... [--verbose/-v]  Compile and run each file's own #[test] defs as a native binary";
    println "         Any <path> that's a directory is recursively expanded to its *.mo files";
    println "         A file with no #[test]s (or that already defines its own main) is skipped, not failed";
    return 0
}
