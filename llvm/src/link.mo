/// External-tool glue: LLVM IR text -> object file -> linked binary.
///
/// This lived twice -- `link_ir` in the compiler's CLI and an inlined copy
/// of the same llc/clang/link sequence in the codegen e2e harness, which
/// had already drifted (different flags, no build-commit define). It is one
/// implementation here, in the `llvm` mote, because none of it knows
/// anything about Monad terms: it is the LLVM toolchain seen from outside.
///
/// The runtime C file is a PARAMETER, never a literal. The `runtime` mote
/// owns that path (`Runtime.c_path`) and depends on this one, so baking it
/// in here would invert the dependency -- and it was previously copied into
/// four call sites, each of which had to be found and fixed by hand when
/// the file moved.

use io {IO}
open IO {println}
use std::process {exec_cmd, process_id}
use std::bench {now, report_since}
use std::log {fail_line, ok_line, stage}

/// `llc -filetype=obj`. Returns llc's exit code.
#[partial]
pub def compile_ir_to_obj (ir_path : String) (obj_path : String) : IO I64 := do {
    exec_cmd "llc" ["-filetype=obj", ir_path, "-o", obj_path]
}

/// `clang -c` on the runtime. `extra_flags` carries anything the caller
/// wants defined at compile time (the build-commit define, `-v`).
#[partial]
pub def compile_runtime_obj (runtime_c : String) (extra_flags : List String) (obj_path : String) : IO I64 := do {
    exec_cmd "clang" (List.append ["-c", runtime_c] (List.append extra_flags ["-o", obj_path]))
}

/// Link objects into an executable. `-lgc`: the generated runtime's heap is
/// collected (see `monad_alloc` in runtime/src/runtime.c, and
/// plans/bootstrapping/linear-types-memory.md for why that is temporary).
/// The include and library search paths come from the nix cc-wrapper via
/// `boehmgc` in devenv.nix, so nothing here hardcodes a store path.
#[partial]
pub def link_objects (objs : List String) (output : String) (extra_flags : List String) : IO I64 := do {
    exec_cmd "clang" (List.append objs (List.append ["-lgc"] (List.append extra_flags ["-o", output])))
}

/// The git commit hash, to bake into the binary as a build-time constant.
/// `exec_cmd` doesn't capture stdout, so this redirects to a temp file and
/// reads it back.
#[partial]
def build_commit_hash : IO String := do {
    let hash_path := "/tmp/monad_build_hash_" ++ I64.to_string process_id;
    let _ <- exec_cmd "sh" ["-c", "git rev-parse --short HEAD 2>/dev/null > " ++ hash_path];
    let hash_exists <- IO.file_exists (Path.path hash_path);
    if hash_exists then do {
        let raw <- IO.read_file (Path.path hash_path);
        let _ <- exec_cmd "rm" ["-f", hash_path];
        return (String.trim raw)
    } else return "unknown"
}

/// Write LLVM IR to disk and link it into a native binary via llc + clang.
/// Returns 0 on success, 1 on any tool failure (each reported on the way
/// out).
///
/// Per-stage `Bench.report` timing is gated on `verbose`, same convention as
/// `lang.codegen.emit`'s `compile_loaded_modules_to_ir` -- added to measure
/// where the "compile_file total minus compile_loaded_modules_to_ir total"
/// remainder actually goes, before guessing at a fix.
#[partial]
pub def link_ir (runtime_c : String) (ir_text : String) (output_dir : Path) (output_name : Path) (verbose : Bool) : IO I64 {
    // `Path.join` here is THE fix for the mangled-double-slash bug this
    // whole `Path` type exists to prevent: if `output_name` is already
    // absolute, it replaces `output_dir` outright instead of naively
    // concatenating (`os.path.join`-style semantics).
    let target := Path.join output_dir output_name;
    let ir_path := Path.with_suffix target ".ll";
    let obj_path := Path.with_suffix target ".o";
    // Beside the other artifacts (i.e. next to `target`), NOT in
    // `output_dir` -- an absolute or directory-bearing `output_name`
    // makes those two different places, and only the former is created
    // below.
    let runtime_obj := Path.with_suffix target "_runtime.o";
    let ir_path_s := Path.to_string ir_path;
    let obj_path_s := Path.to_string obj_path;
    let runtime_obj_s := Path.to_string runtime_obj;
    let output_path_s := Path.to_string target;

    // Nothing creates the directory these artifacts are written into.
    // The CLI's default output dir is `/tmp/monad_out_<pid>` -- a fresh
    // path every single run -- so `clang -o .../monad_runtime.o` failed
    // with "unable to open output file ... No such file or directory"
    // AFTER a full ~18-minute codegen had already succeeded. Derived from
    // the JOINED target rather than `output_dir` alone, because
    // `Path.join` lets an absolute `output_name` replace `output_dir`
    // outright, and because a relative name like `out/hello` puts the
    // real directory inside the NAME. An empty result means "current
    // directory", which needs no mkdir.
    let target_dir : String := Path.parent target;
    let _mkdir <- (if String.beq target_dir ""
        then return 0
        else exec_cmd "mkdir" ["-p", target_dir]);

    let t_write : I64 <- Bench.now;
    IO.write_file ir_path ir_text;
    if verbose then do {
        Bench.report_since "link_ir: write .ll" t_write;
        return unit
    } else return unit;

    // Stage trace (`std.log`): each line prints BEFORE its `Bench.now`
    // start, so a user watching a long stage sees life before it ends.
    stage verbose "link: llc";
    let t_llc : I64 <- Bench.now;
    let result <- compile_ir_to_obj ir_path_s obj_path_s;
    if verbose then do {
        Bench.report_since "link_ir: llc" t_llc;
        return unit
    } else return unit;
    if not (result == 0) then do {
        fail_line ("Compiling ir " ++ ir_path_s ++ " with llc failed");
        return 1
    } else do {
        stage verbose "link: clang runtime.c";
        let t_rtc : I64 <- Bench.now;
        let build_hash <- build_commit_hash;
        let commit_flag := "-DMONAD_BUILD_COMMIT=\"" ++ build_hash ++ "\"";
        let result <- compile_runtime_obj runtime_c (List.append [commit_flag] (if verbose then ["-v"] else [""])) runtime_obj_s;
        if verbose then do {
            Bench.report_since "link_ir: clang runtime.c" t_rtc;
            return unit
        } else return unit;
        if not (result == 0) then do {
            fail_line "compiling runtime failed";
            return 1
        } else do {
            stage verbose "link: clang link";
            let t_link : I64 <- Bench.now;
            let result <- link_objects [obj_path_s, runtime_obj_s] output_path_s (if verbose then ["-v"] else [""]);
            if verbose then do {
                Bench.report_since "link_ir: clang link" t_link;
                return unit
            } else return unit;
            if not (result == 0) then do {
                fail_line "linking failed";
                return 1
            } else do {
                ok_line "Compilation finished";
                return 0
            }
        }
    }
}
