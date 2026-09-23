use io {IO}
open IO {println, read_file, write_file, file_exists}
use std::process {exec_cmd, process_id}
use std::bench {now, report_since}
use lang::types {Decl, LocalScope, ModulePath, NamePath, show_module_path, show_identifier}
use llvm::ir {LLVMModule, emit_module}
use llvm::link {link_ir}
use runtime {}
use lang::codegen::emit {compile_db_module_with_debug, compile_loaded_modules_to_ir_with_debug, ok}
use lang::module {ElaboratedAndCache, collect_link_libs, get_loaded_all, ElaboratedModules, FileCheckAndCache, LoadedModules, ModuleInfo, ModuleInfoCache, bench_step, check_file_cached, check_module_with_scope, elaborate_loaded_modules, elaborate_loaded_modules_cached, elaborate_module_decls_best_effort, expand_check_paths, extract_directory, load_file_modules, load_module_with_info, module_name_from_path, module_info_cache_empty, try_parse_decls, try_parse_decls_strict}
use lang::scope {resolve_class_calls_decls}
use lang::mote {MoteManifest}
use std::map {}
use lang::pretty {show_decls}
use lang::codegen::test_driver {TestIrResult, compile_loaded_modules_to_test_ir, is_no_tests_error, parse_driver_result}
use lib::test_gaps {gap_reason_for, is_known_gap}
use lib::args {*}
// `--verbose` stage/module trace and the colored finish/failure lines
// (`std/src/log.mo` -- its own header documents the gating rules).
use std::log {fail_line, stage}
use lang::lower_core_ir {lower_ctx_from_decls, lower_root, LowerError}
use lang::core_ir {CoreIr}
use lang::core_eval {eval, basic_native_table}
use lang::core_value {GlobalTable, global_cache_new, global_table_len}
use lang::typecheck::meta_eval {show_value_debug, show_core_eval_error_debug}

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
def link_compiled_module (mod_result : Result String LLVMModule) (link_libs : List String) (output_dir : Path) (output_name : Path) (verbose : Bool) : IO I64 :=
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
            let runtime_src : String <- resolve_runtime_src;
            link_ir runtime_src ir_text output_dir output_name link_libs verbose
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
def compile_parsed_decls (decl_list : List Decl) (output_dir : Path) (output_name : Path) (verbose: Bool) (source_path : Option String) : IO I64 {
    let mod_ : LLVMModule := compile_db_module_with_debug decl_list source_path List.empty;
    let ir_text := emit_module mod_;
    // This is the module-loading-FAILURE fallback: there is no
    // `LoadedModules`, so no manifest closure to read `[link] libs`
    // from. A program that needs `-l` flags cannot reach here anyway --
    // its `use` lines are what failed to load.
    println <| "Writing LLVM IR to: " ++ Path.to_string (Path.with_suffix (Path.join output_dir output_name) ".ll");
    let runtime_src : String <- resolve_runtime_src;
    link_ir runtime_src ir_text output_dir output_name List.empty verbose
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

/// The output name a mote's `[bin]` target is built as, given what the
/// caller asked for. Split out of `compile_target` because a `let … in`
/// inside a do-block does not parse (see that def), and this is the
/// value it needs there.
///
/// `"source"` is the literal `Command.from_args` substitutes when
/// neither `-o`/`--output` nor a positional name was given; anything
/// else is the caller's own choice, which always wins.
/// With no name of the manifest's own either, the source file's own
/// stem is used -- `cli/src/main.mo` -> `main`, the same rule a
/// file compile has always applied via
/// `module_name_from_path`.
def compile_out_name (requested : String) (manifest : MoteManifest) (src : String) : String :=
    if Bool.not (String.beq requested "source") then requested
    else match manifest.bin_name {
        Option.some n => n,
        Option.none => module_name_from_path src,
    }

/// `monad compile <path>` with a mote-aware path.
///
/// A FILE compiles exactly as before. A DIRECTORY is read as a mote and
/// its `[bin]` target decides what is built -- `monad compile cli` from
/// the workspace root, or `monad compile .` from inside `cli/`, builds
/// `cli/src/main.mo` as `monad`, which is what `cli/mote.toml`'s
/// `[bin] path`/`[bin] name` declare that binary to be. This is the
/// mirror, in the only spelling `compile` has, of `check`/`test`'s
/// "with no paths, the mote containing the working directory": it takes
/// one positional path, so handing it a directory is the request to
/// build that mote.
///
/// `manifest.bin_path` arrives already joined onto the mote's own `dir`
/// (`Mote.bin_target_path`), so it is a path relative to the working
/// directory exactly as stored -- which is what `compile_file` wants,
/// and what makes `monad compile cli` work from the workspace root.
///
/// A directory that is not a mote, or is one with no `[bin]` target, is
/// an error rather than a guess: `[bin]` is the manifest's own statement
/// of what this mote's binary is, and inventing one (`src/main.mo`, say)
/// would build something the mote never declared. Note that only a mote
/// with a binary target needs a `[bin]` table at all -- `lang`, `std`,
/// `llvm`, `init` and `runtime` are libraries and correctly have none.
#[partial]
def compile_target (path : String) (out_name : String) (verbose : Bool) (debug : Bool) : IO I64 := do {
    let is_a_dir : Bool <- IO.is_dir (Path.path path);
    if Bool.not is_a_dir
    then compile_file path default_output_dir (Path.path out_name) verbose debug
    else do {
        let m : Option MoteManifest <- Mote.discover path;
        match m {
            Option.none => do {
                println ("error: " ++ path ++ " is a directory, and no mote.toml was found in it or above it");
                println "hint: `monad compile <file.mo>` compiles a single file";
                return 1
            },
            Option.some manifest => do {
                match manifest.bin_path {
                    Option.none => do {
                        println ("error: mote `" ++ manifest.name ++ "` declares no [bin] target, so there is nothing to build");
                        println ("hint: add a [bin] table to " ++ path ++ "/mote.toml, naming `path` and (optionally) `name`");
                        return 1
                    },
                    Option.some src => do {
                        let name : String := compile_out_name out_name manifest src;
                        println ("building mote `" ++ manifest.name ++ "`'s [bin] target: " ++ src);
                        compile_file src default_output_dir (Path.path name) verbose debug
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
def compile_file (file_path : String) (output_dir : Path) (output_name : Path) (verbose : Bool) (debug : Bool) : IO I64 {
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
    let elaborated_result : Result String ElaboratedModules <- elaborate_loaded_modules file_path false verbose;
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
                    let diags : List String <- check_module_with_scope em.scope em.target_decls empty_locs (Option.some file_path) verbose;
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
                            let link_result <- compile_file_codegen { file_path := file_path, output_dir := output_dir, output_name := output_name, verbose := verbose, debug := debug, preloaded := Option.some em.loaded };
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
            let link_result <- compile_file_codegen { file_path := file_path, output_dir := output_dir, output_name := output_name, verbose := verbose, debug := debug, preloaded := Option.none };
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
    let compile_result <- compile_file file_path output_dir out_name verbose debug;
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
    let elaborated_result : Result String ElaboratedModules <- elaborate_loaded_modules file_path false verbose;
    match elaborated_result {
        Result.err e => do {
            fail_line ("FAILED at stage: load (could not load dependencies: " ++ e ++ ")");
            return 1
        },
        Result.ok em => do {
            let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
            stage verbose "typecheck target";
            let diags : List String <- check_module_with_scope em.scope em.target_decls empty_locs (Option.some file_path) verbose;
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
        LowerError.le_in_def path inner => String.concat "in def " (String.concat (show_module_path path) (String.concat ": " (show_lower_error inner))),
    }

/// The original `compile_file` body, unchanged -- codegen's own loading
/// + compile pipeline, run only once the gate above has confirmed the
/// target file itself checks cleanly (or the gate's own dependency load
/// failed, in which case this redundant re-attempt produces the same
/// real, rendered diagnostic the old code already did via its own
/// fallback path below, rather than a bare "gate failed").
/// `debug` (from `Command.compile`'s own field -- on by default,
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
def compile_file_codegen (file_path : String) (output_dir : Path) (output_name : Path) (verbose : Bool) (debug : Bool) (preloaded : Option LoadedModules) : IO I64 {
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
    let res : Result String LoadedModules <-
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
            let mod_result <- compile_loaded_modules_to_ir_with_debug loaded verbose source_path;
            // `[link] libs` from every mote in the dependency closure --
            // a package-level build property, read from the manifests
            // rather than from any `#[extern "c"]` attribute.
            let link_libs : List String <- collect_link_libs (get_loaded_all loaded);
            link_compiled_module mod_result link_libs output_dir output_name verbose
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
                    compile_parsed_decls decl_list output_dir output_name verbose source_path
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

/// `checked`/`errors` accumulate across all files — errors are counted
/// per-diagnostic (a file with 3 failing defs contributes 3), matching
/// `monad-rs check`'s own error-tally convention. Every file gets an
/// explicit `ok`/`FAIL` line (a passing file used to print nothing at
/// all, indistinguishable from "not reached" — see the corpus-check
/// driver this feeds, which needs a real per-file pass/fail matrix,
/// not just a final count).
#[partial]
def run_check_loop (cache : ModuleInfoCache) (files : List String) (checked : I64) (errors : I64) (verbose : Bool) : IO I64 :=
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
            let checked_and_cache : FileCheckAndCache <- check_file_cached cache f verbose;
            match checked_and_cache {
                FileCheckAndCache.mk result updated_cache =>
                    match result {
                        FileCheckResult.mk path diags =>
                            match diags {
                                List.empty => do {
                                    println ("ok    " ++ path);
                                    run_check_loop updated_cache rest (checked + 1) errors verbose
                                },
                                List.cons _ _ => do {
                                    println ("FAIL  " ++ path ++ " (" ++ I64.to_string (List.length diags) ++ " error(s))");
                                    print_diagnostics diags;
                                    run_check_loop updated_cache rest (checked + 1) (errors + List.length diags) verbose
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
/// no `mote.toml` above. Both callers answer that the same way `check`
/// and `test` did before any of this existed -- `print_help`, exit 0 --
/// because a bare subcommand in an arbitrary directory has nothing to
/// do and should say so rather than sweep the filesystem.
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
        // Annotated like lang/module.mo's own `Mote.discover` call
        // sites: the checker only knows the bind's type from the
        // annotation, and the match below needs the scrutinee's type.
        let m : Option MoteManifest <- Mote.discover "";
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
                println (verb ++ " mote " ++ manifest.name ++ " (" ++ dir ++ ")");
                return (Option.some (List.cons dir List.empty))
            }
        }
    }
}

#[partial]
def run_check (files : List String) (workspace : Bool) (verbose : Bool) : IO I64 := do {
    let targets <- resolve_target_paths "Checking" "check" files workspace;
    match targets {
        // Empty only from `--workspace` with no workspace manifest --
        // see `resolve_target_paths`, which has already printed why.
        // Failing rather than "0 file(s) checked" is the point: a
        // `--workspace` run that checked nothing did not pass.
        Option.some ts => if List.is_empty ts then return 1
        else do {
            let expanded : List String <- expand_check_paths ts;
            let cache : ModuleInfoCache := module_info_cache_empty;
            run_check_loop cache expanded 0 0 verbose
        },
        // Nothing named, inside no mote: the behaviour before any of
        // this existed, kept because a bare `monad check` in an
        // arbitrary directory has nothing to check and should say so
        // rather than sweep the filesystem.
        Option.none => print_help
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
/// Outside any mote and with no paths, it prints help and exits 0 --
/// the behaviour before this existed, kept because a bare `monad test`
/// in an arbitrary directory has nothing to run and should say so
/// rather than sweep the filesystem.
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
        Option.none => print_help
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

/// The workspace ROOT above `dir`: the directory whose `mote.toml` carries
/// `[workspace] members`. `find_workspace_members` is the same walk, and it
/// answers with that root's expanded MEMBERS; a caller looking for a file
/// that is not one of them (see `resolve_runtime_src`) needs the root
/// itself, which is the one thing the expansion throws away.
///
/// `Option.some ""` means the working directory is the root -- the same
/// case `find_workspace_members ""` already handles, where `dir` is `""`
/// and every path the caller builds from it stays CWD-relative.
#[partial]
def find_workspace_root (dir : String) (depth : I64) : IO (Option String) := do {
    if I64.lt depth 1 then do { return Option.none }
    else do {
        let here : List String <- Mote.workspace_members dir;
        if Bool.not (List.is_empty here) then do { return (Option.some dir) }
        else if String.beq dir "" then find_workspace_root ".." (depth - 1)
        else if String.beq dir "/" then do { return Option.none }
        else find_workspace_root (raw_path_join dir "..") (depth - 1)
    }
}

/// The runtime C source, located from the workspace root above the working
/// directory.
///
/// `Runtime.c_path` is the checkout-root-relative literal for it
/// (`runtime/src/lib.mo`), and that is the right answer exactly when the
/// working directory IS that root. Everything else about a `monad test`
/// from inside `cli/` resolves from the mote now, and this argument was the
/// one input left that was still CWD-relative: the typecheck passed, the
/// driver compiled, and then `clang: error: no such file or directory:
/// 'runtime/src/runtime.c'`, `compiling runtime failed`.
///
/// The working directory is the only correct anchor here, and not as a
/// convenience: `clang` resolves this argument against the COMPILER's own
/// CWD, so any other base -- `runtime/src/lib.mo`'s own resolved path, say,
/// which is the anchor module resolution uses -- would name a file that
/// clang then goes looking for somewhere else entirely. Walking up from
/// `""` for the workspace root is the anchor `--workspace` already uses,
/// and the root is what makes the answer portable: `../runtime/src/
/// runtime.c` holds from inside `cli/`, where `runtime/src/runtime.c` does
/// not.
///
/// Falls back to `Runtime.c_path` when there is no workspace root above the
/// working directory (a single-mote checkout, a file outside the workspace),
/// which is the behaviour that existed before this. The candidate is
/// existence-checked first for the same reason: at the root the walk answers
/// `""` and the candidate IS `Runtime.c_path`, so nothing about the root
/// path changes.
///
/// Deliberately NOT passed through `lang.module.mo`'s `normalize_path`,
/// even though the walk leaves the `..` in: that spelling is valid only
/// relative to the CWD it was walked from, so collapsing it to
/// `runtime/src/runtime.c` would name a file that does not exist from
/// inside `cli/`. `normalize_path` is safe for module resolution because
/// the resolved path is read in the same process that resolved it; this one
/// is handed to a child process.
def resolve_runtime_src : IO String := do {
    let root <- find_workspace_root "" 32;
    match root {
        Option.none => return Runtime.c_path,
        Option.some r => do {
            let candidate := raw_path_join r "runtime/src/runtime.c";
            let exists <- file_exists (Path.path candidate);
            return (if exists then candidate else Runtime.c_path)
        }
    }
}

#[partial]
def run_test (files : List String) (out_dir : String) (verbose : Bool) : IO I64 := do {
    let expanded : List String <- expand_check_paths files;
    let total_files : I64 := List.length expanded;
    run_test_loop { files := expanded, out_dir := out_dir, bin_idx := 0, tests_passed := 0, tests_failed := 0, files_failed := 0, skipped := 0, gaps := 0, file_idx := 0, total_files := total_files, verbose := verbose, cache := module_info_cache_empty }
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
def run_test_loop (files : List String) (out_dir : String) (bin_idx : I64) (tests_passed : I64) (tests_failed : I64) (files_failed : I64) (skipped : I64) (gaps : I64) (file_idx : I64) (total_files : I64) (verbose : Bool) (cache : ModuleInfoCache) : IO I64 :=
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
                // Kept distinct from `skipped`, and from the exit code:
                // a gap is a file whose tests genuinely do not run, for
                // a reason recorded in `cli/src/test_gaps.mo`. Reporting
                // it as "skipped" is what hid ~220 tests running nowhere;
                // failing on it would block CI on already-tracked work.
                // The line is loud on purpose -- it should shrink to
                // nothing and take that file with it.
                if I64.gt gaps 0 then
                    println (I64.to_string gaps ++ " file(s) with known gaps (see cli/src/test_gaps.mo)")
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
            let ec : ElaboratedAndCache <- elaborate_loaded_modules_cached f false cache verbose;
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
                    if is_known_gap f e then do {
                        println ("[33mGAP   " ++ f ++ " (" ++ gap_reason_for f ++ ")[0m");
                        run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed, skipped := skipped, gaps := gaps + 1, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := out_cache }
                    } else do {
                        println ("[31mFAIL  " ++ f ++ " (" ++ e ++ ")[0m");
                        run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed + 1, skipped := skipped, gaps := gaps, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := out_cache }
                    }
                },
                Result.ok em =>
                    do {
                            let empty_locs : LocalScope := { vars := List.empty, parent := Option.none };
                            let diags : List String <- check_module_with_scope em.scope em.target_decls empty_locs (Option.some f) verbose;
                            match diags {
                                List.cons _ _ => do {
                                    print_diagnostics diags;
                                    // Also a FAILURE, not a skip: the
                                    // diagnostics were already printed,
                                    // and a file whose tests cannot even
                                    // be type-checked has run nothing.
                                    // A gap file is excused only if its
                                    // recorded cause still matches.
                                    if is_known_gap f "does not typecheck" then do {
                                        println ("[33mGAP   " ++ f ++ " (" ++ gap_reason_for f ++ ")[0m");
                                        run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed, skipped := skipped, gaps := gaps + 1, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := out_cache }
                                    } else do {
                                        println ("[31mFAIL  " ++ f ++ " (does not typecheck)[0m");
                                        run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed + 1, skipped := skipped, gaps := gaps, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := out_cache }
                                    }
                                },
                                List.empty => run_test_loop_codegen { f := f, rest := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed, skipped := skipped, gaps := gaps, file_idx := file_idx, total_files := total_files, verbose := verbose, preloaded := Option.some em.loaded, cache := out_cache },
                            }
                    },
            }
        }
    }

/// The original `run_test_loop` body for one file, unchanged -- codegen's
/// own loading + compile + run pipeline, reached only once the gate
/// above has confirmed `f` itself checks cleanly.
#[partial]
def run_test_loop_codegen (f : String) (rest : List String) (out_dir : String) (bin_idx : I64) (tests_passed : I64) (tests_failed : I64) (files_failed : I64) (skipped : I64) (gaps : I64) (file_idx : I64) (total_files : I64) (verbose : Bool) (preloaded : Option LoadedModules) (cache : ModuleInfoCache) : IO I64 := do {
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
                    Option.none => load_file_modules f verbose,
                };
            match res {
                err e => do {
                    println ("SKIP  " ++ f ++ " (" ++ e ++ ")");
                    run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed, skipped := skipped + 1, gaps := gaps, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
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
                    let ir_res : Result String TestIrResult <- compile_loaded_modules_to_test_ir loaded result_path;
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
                            //   GAP   a known, recorded failure, matched
                            //         on PATH AND CAUSE
                            //         (`cli/src/test_gaps.mo`), so a
                            //         listed file failing a NEW way
                            //         still fails here.
                            //   FAIL  anything else -- exit 1.
                            if is_no_tests_error e then do {
                                println ("SKIP  " ++ f ++ " (" ++ e ++ ")");
                                run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed, skipped := skipped + 1, gaps := gaps, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
                            } else if is_known_gap f e then do {
                                println ("[33mGAP   " ++ f ++ " (" ++ gap_reason_for f ++ ")[0m");
                                run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed, skipped := skipped, gaps := gaps + 1, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
                            } else do {
                                println ("[31mFAIL  " ++ f ++ " (" ++ e ++ ")[0m");
                                run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed + 1, skipped := skipped, gaps := gaps, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
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
                            let runtime_src : String <- resolve_runtime_src;
                            let link_result <- link_ir runtime_src ir_text (Path.path out_dir) (Path.path bin_name) link_libs verbose;
                            if not (link_result == 0) then do {
                                // A file-level failure, counted as such:
                                // no test in it ever ran, so folding it
                                // into the per-test totals would invent
                                // results that do not exist. A recorded
                                // gap can fail HERE rather than at the
                                // driver compile -- `init/src/tests.mo`
                                // did, on an llc-rejected call to an
                                // undefined `@Pred` -- so the gap test
                                // belongs on this path too; it is kept
                                // though nothing is listed for it today,
                                // because which stage fails is a
                                // property of the gap and not something
                                // a new entry gets to choose. `llc`'s own
                                // message is not available here -- it
                                // went to the console -- so the cause
                                // matched is this branch's own wording.
                                if is_known_gap f "compilation failed" then do {
                                    println ("[33mGAP   " ++ f ++ " (" ++ gap_reason_for f ++ ")[0m");
                                    run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx + 1, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed, skipped := skipped, gaps := gaps + 1, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
                                } else do {
                                    println ("[31mFAIL  " ++ f ++ " (compilation failed)[0m");
                                    run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx + 1, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed + 1, skipped := skipped, gaps := gaps, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
                                }
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
                                    // itself prints, so a listed file
                                    // that starts failing with a
                                    // different exit code is still
                                    // reported.
                                    let why : String := "driver exited " ++ I64.to_string exit_code;
                                    if is_known_gap f why then do {
                                        println ("[33mGAP   " ++ f ++ " (" ++ gap_reason_for f ++ ")[0m");
                                        run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx + 1, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed, skipped := skipped, gaps := gaps + 1, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
                                    } else do {
                                        println ("[31mFAIL  " ++ f ++ " (" ++ why ++ ")[0m");
                                        run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx + 1, tests_passed := tests_passed, tests_failed := tests_failed, files_failed := files_failed + 1, skipped := skipped, gaps := gaps, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
                                    }
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
                                    run_test_loop { files := rest, out_dir := out_dir, bin_idx := bin_idx + 1, tests_passed := tests_passed + (total - failed), tests_failed := tests_failed + failed, files_failed := files_failed, skipped := skipped, gaps := gaps, file_idx := file_idx + 1, total_files := total_files, verbose := verbose, cache := cache }
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
// helpers with the macro-derived demo in cli/src/tests/cli_derive_tests.mo,
// though — same argv-munging primitives either way.
type Command {
    compile (file: Path) (out_name: Path) (verbose: Bool) (debug: Bool),
    run (file: Path) (verbose: Bool) (debug: Bool),
    eval (file: Path) (verbose: Bool),
    pretty (file: String),
    check (files: List String) (verbose: Bool) (workspace: Bool),
    test (files: List String) (verbose: Bool) (workspace: Bool),
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
            if cmd == "compile" then
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
                                Command.check rest2 verbose workspace,
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
        compile file_path out_name verbose debug => do {
            // A directory is a mote to build (`compile_target`); a file
            // goes straight to `compile_file`, unchanged.
            compile_target (Path.to_string file_path) (Path.to_string out_name) verbose debug
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
            let module_opt : Option ModuleInfo <- load_module_with_info base_dir mp;
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
        check files verbose workspace => do {
            run_check files workspace verbose
        },
        test files verbose workspace => do {
            run_test_paths files workspace (Path.to_string default_output_dir) verbose
        },
        version => do {
            println build_commit;
            return 0
        },
        help => do {
            print_help
        }
    }
}

#[partial]
def print_help : IO I64 {
    println "Monad is in alpha mode and under heavy development.";
    println "Expect breaking changes, bugs, and incomplete features.";
    println "";
    println "Usage: monad compile <path> [name] [--output/-o <name>] [--verbose/-v] [--debug/-g] [--release]";
    println "         Parse and compile a .mo source file";
    println "         <path> may be a mote DIRECTORY, in which case its [bin] target is built";
    println "           (`monad compile cli` builds cli/src/main.mo as `monad`)";
    println "         --verbose/-v prints each module as it loads and one line per pipeline stage";
    println "         --debug/-g emits DWARF debug info (one source location per top-level def)";
    println "       monad run <path> [--verbose/-v] [--debug/-g] [--release]  Compile and execute a .mo source file";
    println "       monad eval <path> [--verbose/-v]  Evaluate a .mo source file using the built-in interpreter (pure programs only)";
    println "       monad pretty <path>  Parse and pretty print a .mo source file";
    println "       monad check [<path>...] [--workspace/-w] [--verbose/-v]  Parse and typecheck .mo source files (no execution)";
    println "         Any <path> that's a directory is recursively expanded to its *.mo files";
    println "         With no <path>, checks the mote containing the working directory";
    println "         --workspace/-w checks every mote in the enclosing workspace";
    println "           (only directories that ARE motes: examples/ has no manifest)";
    println "         --verbose/-v prints a per-declaration progress trace while checking";
    println "       monad test [<path>...] [--workspace/-w] [--verbose/-v]  Compile and run each file's own #[test] defs as a native binary";
    println "         Any <path> that's a directory is recursively expanded to its *.mo files";
    println "         With no <path>, tests the mote containing the working directory";
    println "         --workspace/-w tests every mote in the enclosing workspace";
    println "           (only directories that ARE motes: examples/ has no manifest)";
    println "         --verbose/-v prints per-file timing and module-cache statistics";
    println "         A file with no #[test]s is skipped, not failed";
    println "       monad version  Print the git commit this binary was built from";
    return 0
}
