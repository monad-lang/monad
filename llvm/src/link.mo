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

open IO {println}
use std::process {exec_cmd, Proc.capture}
use std::bench {Bench.now, Bench.report_since}
use std::log {fail_line, ok_line, stage}
use lib::target {TargetSpec}

/// `llc -filetype=obj`, for the machine this compiler is running on.
///
/// A sibling-function wrapper rather than a required argument, for the same
/// reason `compile_db_decls_ir` gives: the codegen e2e harnesses that call
/// this build and immediately run a binary, so a target is not a thing any
/// of them has. A native spec is flag-free, so this buys argv stability, not
/// portability: the module header is still `emit.mo`'s x86_64 literal.
#[partial]
pub def compile_ir_to_obj (ir_path : String) (obj_path : String) : IO I64 := do {
    let native <- TargetSpec.native;
    compile_ir_to_obj_with native ir_path obj_path
}

/// `llc -filetype=obj` for `target`. Returns llc's exit code.
///
/// The target supplies `-mtriple` only when llc's spelling differs from the
/// module header's (`llvm/src/target.mo`), so a native build's argv is
/// byte-for-byte what it was before targets existed and only a cross build's
/// changes.
#[partial]
pub def compile_ir_to_obj_with (target : TargetSpec) (ir_path : String) (obj_path : String) : IO I64 := do {
    exec_cmd "llc" (List.append ["-filetype=obj"] (List.append (TargetSpec.llc_argv target) [ir_path, "-o", obj_path]))
}

/// `clang -c` on the runtime. `extra_flags` carries anything the caller
/// wants defined at compile time (the build-commit define, `-v`).
///
/// `-pthread` is not decoration: the runtime is a THREADED Boehm build
/// (`GC_THREADS` at the head of runtime/src/runtime.c) and its fiber
/// objects are real OS threads, so the compile needs `_REENTRANT` set for
/// the system headers and the link needs the threads library. On a glibc
/// 2.34+ system the symbols live in libc and the link would happen to
/// succeed without it, which is exactly why it is spelled out.
#[partial]
pub def compile_runtime_obj (runtime_c : String) (extra_flags : List String) (obj_path : String) : IO I64 := do {
    let inc <- darwin_gc_flag "-I" "includedir";
    exec_cmd "clang" (List.append ["-pthread", "-c", runtime_c] (List.append inc (List.append extra_flags ["-o", obj_path])))
}

/// Link objects into an executable. `-lgc`: the generated runtime's heap is
/// collected (see `monad_alloc` in runtime/src/runtime.c, and
/// plans/bootstrapping/linear-types-memory.md for why that is temporary).
/// The include and library search paths come from the nix cc-wrapper via
/// `boehmgc` in devenv.nix, so nothing here hardcodes a store path; on
/// macOS, from pkg-config (`darwin_gc_flag`).
/// `-pthread` here for the same reason as `compile_runtime_obj` above.
#[partial]
pub def link_objects (objs : List String) (output : String) (extra_flags : List String) : IO I64 := do {
    let lib <- darwin_gc_flag "-L" "libdir";
    exec_cmd "clang" (List.append ["-pthread"] (List.append objs (List.append lib (List.append ["-lgc"] (List.append extra_flags ["-o", output])))))
}

/// `<flag><dir>` for Boehm GC's `var` directory (`includedir`, `libdir`)
/// as `pkg-config` reports it -- macOS only, and nothing when pkg-config
/// is absent or does not know `bdw-gc`.
///
/// On Linux the toolchain already finds libgc (the nix cc-wrapper via
/// `boehmgc` in devenv.nix, or the distro's default paths), so the argv
/// there stays exactly what it was. On macOS outside nix, nothing puts a
/// package manager's prefix on clang's search path. Asking pkg-config
/// rather than naming one keeps this neutral between Homebrew, MacPorts
/// and nix: each ships `bdw-gc.pc`, and `PKG_CONFIG_PATH` picks between
/// them. Temporary along with libgc itself (see `link_objects`).
#[partial]
def darwin_gc_flag (flag : String) (var : String) : IO (List String) := do {
    let darwin <- os_is_darwin;
    if darwin then do {
        let dir <- capture_line "pkg-config" ["--variable=" ++ var, "bdw-gc"];
        return (dir_flag flag dir)
    } else return List.empty
}

/// Whether this compiler is running on macOS, by `uname -s`.
#[partial]
def os_is_darwin : IO Bool := do {
    let os <- capture_line "uname" ["-s"];
    return (match os {
        Option.some s => String.beq s "Darwin",
        Option.none => false,
    })
}

def dir_flag (flag : String) (dir : Option String) : List String := match dir {
    Option.some d => [flag ++ d],
    Option.none => List.empty,
}

/// A command's trimmed output, or `none` when it fails (including when it
/// is not installed) or prints nothing.
#[partial]
def capture_line (cmd : String) (args : List String) : IO (Option String) := do {
    let r <- Proc.capture cmd args;
    match r {
        Pair.pair code out =>
            if code == 0 && Bool.not (String.is_empty (String.trim out))
            then return (Option.some (String.trim out))
            else return Option.none
    }
}

/// Maps library names (e.g. `["m"]` from a mote's `[link] libs`) to the
/// `clang` flags that link them (`["-lm"]`). Lives here rather
/// than in the compiler because `link_objects` above is what knows the
/// linker's argv shape -- codegen collects the names and deliberately
/// does not translate them.
#[partial]
pub def map_dash_l (libs : List String) : List String := match libs {
    List.empty => List.empty,
    List.cons hd tl => List.cons (String.concat "-l" hd) (map_dash_l tl),
}

/// `-v`, or NOTHING AT ALL. An empty STRING in argv is a FILENAME, not an
/// absent flag -- the wrapped native clang tolerates `clang -c "" x.c`, which
/// is why this went unnoticed, while a cross gcc refuses the whole command
/// with `error: : linker input file not found`.
def verbose_argv (verbose : Bool) : List String :=
    if verbose then ["-v"] else List.empty

/// `MONAD_BUILD_COMMIT`, trimmed, or `""` when it is unset (or set to
/// nothing but whitespace). A nix build's source is a store copy: no `.git`,
/// so the compiler inside it cannot name its own revision, and the flake
/// exports the one it is building instead.
#[partial]
def env_commit_hash (from_env : Option String) : String := match from_env {
    Option.some s => String.trim s,
    Option.none => ""
}

/// The commit to bake into a linked binary as `-DMONAD_BUILD_COMMIT`, from
/// the two sources that can know it, in the order that lets the more
/// specific answer win.
///
/// `MONAD_BUILD_COMMIT` wins because a nix build's source is a store copy
/// with no `.git` in it: the flake exports the revision it is building, and
/// that is the only source that can answer there.
///
/// Otherwise the answer is the COMPILER's own revision -- the string
/// `monad version` prints, threaded down from `cli/src/main.mo`'s
/// `build_commit` native. This used to be a `git rev-parse --short HEAD`
/// probe run in the WORKING DIRECTORY, which asked the wrong repository
/// entirely: a user compiling their own program got their own repo's HEAD
/// stamped into monad's runtime (two forks per link to do it). Outside any
/// repository the probe's redirect still created the file, so the trim
/// produced `""` rather than the `unknown` the docs promise -- the
/// compiler could always have named itself here, and now does.
///
/// `unknown` survives as the last resort, for a compiler that cannot name
/// itself (the `monad-rs run cli/src/main.mo` prototype, where the native
/// falls back to its own default): the string it stamps is then the one the
/// docs already described.
pub def build_commit_define (from_env : Option String) (compiler_commit : String) : String :=
    if String.is_empty (env_commit_hash from_env) then
        (if String.is_empty (String.trim compiler_commit) then "unknown" else String.trim compiler_commit)
    else env_commit_hash from_env

/// Write LLVM IR to disk and link it into a native binary via llc + clang.
/// Returns 0 on success, 1 on any tool failure (each reported on the way
/// out).
///
/// `ir_path` is the file `llc` is pointed at, and the CALLER owns it.
/// That is deliberate: `llc` records its input's name in the object it
/// emits, so this path ends up inside the linked binary. Naming it after
/// the caller's output would therefore make the artifact depend on
/// something that is not an input, and two builds of one source under two
/// output names would differ by a byte -- see `Build.artifact_ir_path`,
/// which is what the cached `build` path passes here. A caller with no
/// key to name it by (a `run`, a test driver, a build whose compiler
/// digest could not be taken) passes the output-derived path by way of
/// `cli/src/main.mo`'s `resolve_ir_path`, which is the behaviour every one
/// of them had before this was a parameter.
///
/// The output-derived `.ll` is still written, as a convenience copy, for
/// the readers that already know that path -- `tools/debug_transparency_
/// oracle.sh` and anyone inspecting a build by hand. It is written from
/// the same text rather than copied, and it is never what `llc` reads:
/// a convenience copy that the compiler consulted would put the leak
/// straight back.
///
/// `link_libs` is the deduplicated union of `[link] libs` across every mote
/// in the program's dependency closure (`lang.module`'s `collect_link_libs`);
/// each becomes a `-l<lib>` on the final link, which is what makes a mote
/// declaring `libs = ["m"]` actually link libm. Empty preserves the original
/// no-extra-flags behaviour.
///
/// `compiler_commit` is the revision of the COMPILER doing the linking
/// (`cli/src/main.mo`'s `build_commit` native, the same string `monad
/// version` prints), which is what gets stamped into the linked program
/// unless `MONAD_BUILD_COMMIT` overrides it -- see `build_commit_define`.
/// It is a parameter rather than something this def works out for itself
/// because the answer is the caller's identity, and because finding it out
/// used to cost a `git` fork in the working directory that named the wrong
/// repository.
///
/// Per-stage `Bench.report` timing is gated on `verbose`, same convention as
/// `lang.codegen.emit`'s `compile_loaded_modules_to_ir` -- added to measure
/// where the "compile_file total minus compile_loaded_modules_to_ir total"
/// remainder actually goes, before guessing at a fix.
#[partial]
pub def link_ir (runtime_c : String) (ir_text : String) (ir_path : Path) (output_dir : Path) (output_name : Path) (link_libs : List String) (compiler_commit : String) (verbose : Bool) (spec : TargetSpec) : IO I64 {
    // `Path.join` here is THE fix for the mangled-double-slash bug this
    // whole `Path` type exists to prevent: if `output_name` is already
    // absolute, it replaces `output_dir` outright instead of naively
    // concatenating (`os.path.join`-style semantics).
    let target := Path.join output_dir output_name;
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

    // ...and the IR's own directory, which is a DIFFERENT one on the
    // cached `build` path: the target sits in `<target-dir>/<profile>/`
    // while the IR sits in `<target-dir>/store/`. Two calls rather than
    // one because which two directories those are is the caller's
    // business; `mkdir -p` is idempotent, and this is two forks against a
    // compile that costs tens of seconds.
    let ir_dir : String := Path.parent ir_path;
    let _mkdir_ir <- (if String.beq ir_dir ""
        then return 0
        else exec_cmd "mkdir" ["-p", ir_dir]);

    let t_write : I64 <- Bench.now;
    IO.write_file ir_path ir_text;
    // The convenience copy, for a reader that already knows this path
    // because `-o` implies it. Skipped when it IS the IR (the callers with
    // no key to name one by), so the common case still writes one file.
    let beside : String := Path.to_string (Path.with_suffix target ".ll");
    if Bool.not (String.beq beside ir_path_s) then do {
        IO.write_file (Path.path beside) ir_text;
        return unit
    } else return unit;
    if verbose then do {
        Bench.report_since "link_ir: write .ll" t_write;
        return unit
    } else return unit;

    // Stage trace (`std.log`): each line prints BEFORE its `Bench.now`
    // start, so a user watching a long stage sees life before it ends.
    stage verbose "link: llc";
    let t_llc : I64 <- Bench.now;
    let result <- compile_ir_to_obj_with spec ir_path_s obj_path_s;
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
        let from_env <- IO.get_env "MONAD_BUILD_COMMIT";
        let build_hash : String := build_commit_define from_env compiler_commit;
        let commit_flag := "-DMONAD_BUILD_COMMIT=\"" ++ build_hash ++ "\"";
        let result <- compile_runtime_obj runtime_c (List.append [commit_flag] (verbose_argv verbose)) runtime_obj_s;
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
            // `-l<lib>` for every library the program's motes declared,
            // ahead of the verbose flag. An empty `link_libs` leaves the
            // argv exactly as it was.
            let dash_l : List String := map_dash_l link_libs;
            let link_flags : List String := List.append dash_l (verbose_argv verbose);
            let result <- link_objects [obj_path_s, runtime_obj_s] output_path_s link_flags;
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

// `build_commit_define`'s three answers, pinned. Its whole job is to pick
// between sources that disagree -- the flake's export, the compiler's own
// revision and "no answer at all" -- and the middle one is the only case a
// developer ever sees, which is why it is the one a regression would land in
// silently: a binary stamped with the wrong revision still builds and runs.

#[test]
def test_build_commit_define_prefers_the_environment : Bool :=
    String.beq (build_commit_define (Option.some "env-c0ffee") "compiler-1") "env-c0ffee"

#[test]
def test_build_commit_define_trims_the_environment : Bool :=
    String.beq (build_commit_define (Option.some "  env-c0ffee  ") "compiler-1") "env-c0ffee"

// A set-but-blank variable is the shape `git rev-parse` left behind when it
// had nothing to say (the redirect still wrote the file), so it has to read
// as unset rather than as a revision spelled with spaces.
#[test]
def test_build_commit_define_reads_a_blank_environment_as_unset : Bool :=
    String.beq (build_commit_define (Option.some "   ") "compiler-1") "compiler-1"

#[test]
def test_build_commit_define_falls_back_to_the_compiler : Bool :=
    String.beq (build_commit_define Option.none "compiler-1") "compiler-1"

#[test]
def test_build_commit_define_keeps_unknown_as_the_last_resort : Bool :=
    String.beq (build_commit_define Option.none "") "unknown"

#[test]
def test_build_commit_define_keeps_unknown_when_the_compiler_is_blank : Bool :=
    String.beq (build_commit_define Option.none "   ") "unknown"

// An empty STRING in argv is a filename, not an absent flag -- a cross cc dies
// on it where the wrapped native clang tolerates it -- so the non-verbose
// answer has to be an empty LIST.
#[test]
def test_verbose_argv_is_empty_when_not_verbose : Bool :=
    List.is_empty (verbose_argv false)

#[test]
def test_verbose_argv_is_the_flag_when_verbose : Bool :=
    match verbose_argv true {
        List.cons hd tl => String.beq hd "-v" && List.is_empty tl,
        List.empty => false,
    }
