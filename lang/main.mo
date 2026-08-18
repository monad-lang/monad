use io {IO, println, read_file, write_file}
open IO {println, read_file, write_file}
use process {exec_cmd}
use lang.types {Decl, LoadedModules}
use lang.codegen.ir {emit_module}
use lang.codegen.emit {compile_db_module, compile_loaded_modules_to_ir, ok}
use lang.module {FileCheckAndCache, LoadedModules, ModuleScopeCache, PreludeInitBase, build_prelude_init_base, check_file_cached, expand_check_paths, load_file_modules, module_scope_cache_empty, try_parse_decls, try_parse_decls_strict}
use lang.cli {*}
use std.list {Show}


/// Write LLVM IR to disk and link it into a native binary via llc + clang.
/// Shared by `compile_file`'s primary path and its module-loading-failure
/// fallback (`compile_parsed_decls`) — both produce an `ir_text : String`
/// by different routes and then need the identical llc/clang/link steps.
#[partial]
def link_ir (ir_text : String) (output_dir : String) (output_name : String) (verbose : Bool) : IO I64 {
    let ir_path := output_dir ++ "/" ++ output_name ++ ".ll";
    let obj_path := output_dir ++ "/" ++ output_name ++ ".o";
    let runtime_obj := output_dir ++ "/monad_runtime.o";
    let output_path := output_dir ++ "/" ++ output_name;

    IO.write_file ir_path ir_text;

    let result <- exec_cmd "llc" [ "-filetype=obj", ir_path, "-o", obj_path];
    if not (result == 0) then do {
        println <| (String.concat "Compiling ir " (String.concat ir_path " with llc failed"));
        return 1
    } else do {
        let result <- exec_cmd "clang" (List.append [ "-c", "lang/codegen/runtime.c", "-o", runtime_obj] (if verbose then ["-v"] else [""]));
        if not (result == 0) then do {
            println <| "compiling runtime failed";
            return 1
        } else do {
            let result <- exec_cmd "clang" (List.append [ obj_path, runtime_obj, "-o", output_path] (if verbose then ["-v"] else [""]));
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

/// Parse a source file and compile + run it via LLVM.
#[partial]
def compile_parsed_decls (decls : List Decl) (output_dir : String) (output_name : String) (verbose: Bool) : IO I64 {
    let mod_ := compile_db_module decls;
    let ir_text := emit_module mod_;
    println <| "Writing LLVM IR to: " ++ output_dir ++ "/" ++ output_name ++ ".ll";
    link_ir ir_text output_dir output_name verbose
}

/// Parse a source file and compile + run it via LLVM.
#[partial]
def compile_file (file_path : String) (output_dir : String) (output_name : String) (verbose : Bool) : IO I64 {
    println <| "compiling: " ++ file_path ++ " to " ++ output_dir ++ "/" ++ output_name;
    // First try to load with module boundaries preserved
    let res : Result String LoadedModules <- load_file_modules file_path;
    match res {
        Result.ok loaded => do {
            println <| "modules loaded:\n" ++ Show.show loaded;
            let mod_ <- compile_loaded_modules_to_ir loaded;
            let ir_text := emit_module mod_;
            link_ir ir_text output_dir output_name verbose
        },
        Result.err e => do {
            println ("Failed to parse dependencies: " ++ e);
            // Fallback to simple parsing without dependencies (for error reporting)
            let source <- IO.read_file file_path;
            match lang.module.try_parse_decls source {
                Option.some decls => compile_parsed_decls decls output_dir output_name verbose,
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

/// Print one diagnostic per line — `check_file`'s per-file diagnostics
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
def run_check_loop (base : PreludeInitBase) (cache : ModuleScopeCache) (files : List String) (checked : I64) (errors : I64) (verbose : Bool) : IO I64 :=
    match files {
        List.empty => do {
            println (I64.to_string checked ++ " file(s) checked, " ++ I64.to_string errors ++ " error(s)");
            // Whole-run module-scope cache visibility (see ModuleScopeCache's
            // own doc comment, lang/module.mo): `hits` is how many times a
            // dependency load was served from a PRIOR file's own load in
            // this same run instead of re-reading/re-parsing/re-scope-
            // building it from scratch -- the direct measure of the
            // redundant-reload cost this cache eliminates.
            if verbose then
                match cache {
                    ModuleScopeCache.mk _ hits misses =>
                        println ("module scope cache: " ++ I64.to_string hits ++ " hit(s), " ++ I64.to_string misses ++ " miss(es)")
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

/// Parse + typecheck each file with `lang.module.check_file` — no
/// execution, no compilation. See lang/module.mo's `check_file`/
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
    let cache : ModuleScopeCache := module_scope_cache_empty;
    run_check_loop base cache expanded 0 0 verbose
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
    compile (file: String) (out_name: String) (verbose: Bool),
    pretty (file: String),
    check (files: List String) (verbose: Bool),
    help
}

/// `compile <path> [name]` (original positional form) and `compile <path>
/// [--output/-o <name>] [--verbose/-v]` (flag form) both work; an explicit
/// `--output`/`-o` wins over a positional name if both are given.
def Command.from_args (args : List String) : Command :=
    match args {
        List.cons cmd rest =>
            if cmd == "compile" then
                match Cli.take_flag "verbose" "v" rest {
                    Cli.FlagResult.flag_result verbose rest1 =>
                        match Cli.take_opt "output" "o" "" rest1 {
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
                                                    Option.some path => Command.compile path out_name verbose,
                                                    Option.none => Command.help,
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
            else
                Command.help,
        List.empty => Command.help,
    }

/// Current main entrypoint of self hosted compiler
def main (args : List String) : IO I64 {
    let out_dir := "/tmp";
    let cmd : Command := Command.from_args args;
    match cmd {
        compile file_path out_name verbose => do {
            compile_file file_path out_dir out_name verbose
        },
        pretty file_path => do {
            println <| "loading " ++ file_path;
            // TODO fix type checking bug on res
            let res : Result String LoadedModules <- load_file_modules file_path;
            match res {
                ok loaded => do {
                    println <| "modules loaded:\n" ++ Show.show loaded;
                    return 0
                },
                err e => do {
                    println ("Failed to parse dependencies: " ++ e);
                    return 1
                }
            }
        },
        check files verbose => do {
            run_check files verbose
        },
        help => do {
            print_help
        }
    }
}

#[partial]
def print_help : IO I64 {
    println "Usage: monad compile <path> [name] [--output/-o <name>] [--verbose/-v]";
    println "         Parse and compile a .mo source file";
    println "       monad pretty <path>  Parse and pretty print a .mo source file";
    println "       monad check <path>... [--verbose/-v]  Parse and typecheck .mo source files (no execution)";
    println "         Any <path> that's a directory is recursively expanded to its *.mo files";
    println "         --verbose/-v prints a per-declaration progress trace while checking";
    return 0
}
