/// Smoke tests for `cli/src/main.mo`'s `Command.from_args` argv parser.
///
/// This used to say `cargo run -- run cli/src/main.mo ...` (actually
/// executing `main`) hit a separate, pre-existing `instance-Monad-IO
/// not found` failure — no longer reproduces (confirmed via many real
/// `build`/`check`/`pretty`/`test` invocations, 2026-08-19); whatever
/// that was has since been fixed elsewhere, or this repro was itself
/// stale. Kept testing `Command.from_args` directly anyway (isolating
/// argv-parsing from everything downstream is still the more precise
/// unit of test coverage, real end-to-end runs notwithstanding).
use lib::main {*}

#[test]
def test_from_args_build_positional_name : Bool :=
    match Command.from_args ["build", "a.mo", "myname"] {
        Command.build path out_name _bin verbose debug _no_cache _target =>
            Path.to_string path == "a.mo" && Path.to_string out_name == "myname" && verbose == false && debug == true,
        _ => false,
    }

#[test]
def test_from_args_build_default_name : Bool :=
    match Command.from_args ["build", "a.mo"] {
        Command.build path out_name _bin verbose debug _no_cache _target =>
            Path.to_string path == "a.mo" && Path.to_string out_name == "source" && verbose == false && debug == true,
        _ => false,
    }

#[test]
def test_from_args_build_output_flag : Bool :=
    match Command.from_args ["build", "a.mo", "--output", "out", "--verbose"] {
        Command.build path out_name _bin verbose debug _no_cache _target =>
            Path.to_string path == "a.mo" && Path.to_string out_name == "out" && verbose == true && debug == true,
        _ => false,
    }

#[test]
def test_from_args_build_short_flags : Bool :=
    match Command.from_args ["build", "a.mo", "-o", "out", "-v"] {
        Command.build path out_name _bin verbose debug _no_cache _target =>
            Path.to_string path == "a.mo" && Path.to_string out_name == "out" && verbose == true && debug == true,
        _ => false,
    }

#[test]
def test_from_args_build_debug_flag : Bool :=
    match Command.from_args ["build", "a.mo", "--debug"] {
        Command.build path out_name _bin verbose debug _no_cache _target =>
            Path.to_string path == "a.mo" && verbose == false && debug == true,
        _ => false,
    }

#[test]
def test_from_args_build_debug_short_flag : Bool :=
    match Command.from_args ["build", "a.mo", "-g", "-v"] {
        Command.build path out_name _bin verbose debug _no_cache _target =>
            Path.to_string path == "a.mo" && verbose == true && debug == true,
        _ => false,
    }

/// Debug info is ON by default (rustc's own dev-profile default);
/// `--release` is how you opt out.
#[test]
def test_from_args_build_release_opts_out_of_debug : Bool :=
    match Command.from_args ["build", "a.mo", "--release"] {
        Command.build path out_name _bin verbose debug _no_cache _target =>
            Path.to_string path == "a.mo" && verbose == false && debug == false,
        _ => false,
    }

/// An explicit `--debug` wins over `--release` -- asking twice, with
/// the more specific request, is not an error.
#[test]
def test_from_args_build_debug_beats_release : Bool :=
    match Command.from_args ["build", "a.mo", "--release", "--debug"] {
        Command.build path out_name _bin verbose debug _no_cache _target =>
            Path.to_string path == "a.mo" && verbose == false && debug == true,
        _ => false,
    }

/// `monad build` with no path is `monad build .` -- the mote containing
/// the working directory, matching `check`/`test`'s own default. It used
/// to print usage, which is what made `compile` the one verb with no
/// zero-argument form.
#[test]
def test_from_args_build_with_no_path_defaults_to_the_mote : Bool :=
    match Command.from_args ["build"] {
        Command.build path out_name _bin verbose debug _no_cache _target =>
            Path.to_string path == "." && Path.to_string out_name == "source" && verbose == false && debug == true,
        _ => false,
    }

/// `build .` and a bare `build` are one code path, so they must parse to
/// the same command.
#[test]
def test_from_args_build_bare_and_dot_agree : Bool :=
    match Command.from_args ["build"] {
        Command.build p1 o1 _b1 _v1 _d1 _n1 _target => match Command.from_args ["build", "."] {
            Command.build p2 o2 _b2 _v2 _d2 _n2 _target =>
                Path.to_string p1 == Path.to_string p2 && Path.to_string o1 == Path.to_string o2,
            _ => false,
        },
        _ => false,
    }

// `build`'s cache escape hatch, peeled for the same reason `check`'s is:
// it is a flag, not a path, and left in the list it would be handed to the
// path expander as a filename.
#[test]
def test_from_args_build_no_cache_flag : Bool :=
    match Command.from_args ["build", "a.mo", "--no-cache"] {
        Command.build path _out_name _bin _verbose _debug no_cache _target =>
            Path.to_string path == "a.mo" && no_cache == true,
        _ => false,
    }

// `--bin <name>` is peeled with the other flags for the same reason: left
// in the list it would be read as the positional PATH and its name as the
// positional output name, so `monad build --bin tool .` would build `.` as
// `tool` -- one argument, two meanings, both wrong.
#[test]
def test_from_args_build_bin_flag : Bool :=
    match Command.from_args ["build", "a.mo", "--bin", "tool"] {
        Command.build path out_name bin _verbose _debug _no_cache _target =>
            Path.to_string path == "a.mo" && bin == "tool" && Path.to_string out_name == "source",
        _ => false,
    }

// `--target <triple>` is peeled with the other flags for the same reason
// `--bin` is: left in the list, `--target` reads as the positional PATH and
// the triple as the output name.
#[test]
def test_from_args_print_targets : Bool :=
    match Command.from_args ["print-targets"] {
        Command.print_targets => true,
        _ => false,
    }

#[test]
def test_from_args_build_target_flag : Bool :=
    match Command.from_args ["build", "a.mo", "--target", "aarch64-unknown-linux-gnu"] {
        Command.build path out_name _bin _verbose _debug _no_cache target =>
            Path.to_string path == "a.mo"
                && target == "aarch64-unknown-linux-gnu"
                && Path.to_string out_name == "source",
        _ => false,
    }

/// And with no `--target` at all it is empty, which `TargetSpec.resolve`
/// reads as "this machine" rather than as a target named "".
#[test]
def test_from_args_build_without_target_is_empty : Bool :=
    match Command.from_args ["build", "a.mo"] {
        Command.build _path _out_name _bin _verbose _debug _no_cache target => target == "",
        _ => false,
    }

/// Empty, not a name: "no `--bin` was given" is a different state from
/// "`--bin` named something", and only the empty one lets `build_target`
/// fall back to "the target that exists".
#[test]
def test_from_args_build_without_bin_is_empty : Bool :=
    match Command.from_args ["build", "a.mo"] {
        Command.build _path _out_name bin _verbose _debug _no_cache _target => bin == "",
        _ => false,
    }

// Named, not merely accepted: a build that did not ask for the hatch must
// not get it, or the flag would be indistinguishable from one that is
// silently always on.
#[test]
def test_from_args_build_without_no_cache_is_false : Bool :=
    match Command.from_args ["build", "a.mo"] {
        Command.build _path _out_name _bin _verbose _debug no_cache _target => no_cache == false,
        _ => false,
    }

/// The removed verb must not be silently accepted as something else --
/// `compile` is now an ordinary unknown word, so it falls to `help`.
#[test]
def test_from_args_compile_is_no_longer_a_verb : Bool :=
    match Command.from_args ["compile", "a.mo"] {
        Command.help => true,
        _ => false,
    }

#[test]
def test_from_args_pretty : Bool :=
    match Command.from_args ["pretty", "b.mo"] {
        Command.pretty path => path == "b.mo",
        _ => false,
    }

#[test]
def test_from_args_check : Bool :=
    match Command.from_args ["check", "a.mo", "b.mo", "-v"] {
        Command.check files opts =>
            files == ["a.mo", "b.mo"] && opts.verbose == true && opts.workspace == false && opts.no_cache == false && opts.affine == false,
        _ => false,
    }

#[test]
def test_from_args_check_workspace_flag : Bool :=
    match Command.from_args ["check", "--workspace"] {
        Command.check files opts =>
            List.is_empty files && opts.workspace == true && opts.verbose == false && opts.no_cache == false && opts.affine == false,
        _ => false,
    }

#[test]
def test_from_args_check_workspace_short_flag : Bool :=
    match Command.from_args ["check", "-w", "-v"] {
        Command.check files opts =>
            List.is_empty files && opts.workspace == true && opts.verbose == true && opts.no_cache == false && opts.affine == false,
        _ => false,
    }

// The flag must be PEELED, not left among the paths -- otherwise it is
// handed to the path expander as a filename.
#[test]
def test_from_args_check_workspace_flag_not_a_path : Bool :=
    match Command.from_args ["check", "--workspace", "a.mo"] {
        Command.check files opts =>
            files == ["a.mo"] && opts.workspace == true && opts.no_cache == false && opts.affine == false,
        _ => false,
    }

// A bare `monad check` no longer means "print help": it means "check the
// mote containing the working directory" (and only falls back, at RUN
// time and with exit 1, to `no_target_diagnostic` when there is no such
// mote). Mirroring `test_from_args_test_no_files_is_a_test_command`,
// which Phase 9b made true for `test` too.
#[test]
def test_from_args_check_no_files_is_a_check_command : Bool :=
    match Command.from_args ["check"] {
        Command.check files opts =>
            List.is_empty files && opts.workspace == false && opts.verbose == false && opts.no_cache == false && opts.affine == false,
        _ => false,
    }

// `--no-cache` is peeled for the same reason `--workspace` is: it is a
// flag, not a path. Left in the list it would be handed to the path
// expander as a filename, where it would surface as a file that does not
// exist rather than as a flag that was ignored.
#[test]
def test_from_args_check_no_cache_flag : Bool :=
    match Command.from_args ["check", "--no-cache", "a.mo"] {
        Command.check files opts =>
            files == ["a.mo"] && opts.no_cache == true && opts.workspace == false && opts.verbose == false && opts.affine == false,
        _ => false,
    }

#[test]
def test_from_args_check_no_cache_flag_combines_with_workspace : Bool :=
    match Command.from_args ["check", "-w", "--no-cache", "a.mo", "b.mo"] {
        Command.check files opts =>
            files == ["a.mo", "b.mo"] && opts.workspace == true && opts.no_cache == true && opts.affine == false,
        _ => false,
    }

#[test]
def test_from_args_check_without_no_cache_is_false : Bool :=
    match Command.from_args ["check", "a.mo"] {
        Command.check files opts =>
            files == ["a.mo"] && opts.no_cache == false && opts.affine == false,
        _ => false,
    }

// `--affine` must be PEELED (not handed to the path expander as a
// filename) and must set its flag, mirroring the `--workspace` and
// `--no-cache` peel tests just above.
#[test]
def test_from_args_check_affine_flag : Bool :=
    match Command.from_args ["check", "--affine", "a.mo"] {
        Command.check files opts =>
            files == ["a.mo"] && opts.affine == true && opts.workspace == false && opts.verbose == false && opts.no_cache == false,
        _ => false,
    }

#[test]
def test_from_args_test : Bool :=
    match Command.from_args ["test", "a.mo", "b.mo", "-v"] {
        Command.test files verbose workspace =>
            files == ["a.mo", "b.mo"] && verbose == true && workspace == false,
        _ => false,
    }

#[test]
def test_from_args_test_workspace_flag : Bool :=
    match Command.from_args ["test", "--workspace"] {
        Command.test files verbose workspace =>
            List.is_empty files && workspace == true && verbose == false,
        _ => false,
    }

#[test]
def test_from_args_test_workspace_short_flag : Bool :=
    match Command.from_args ["test", "-w", "-v"] {
        Command.test files verbose workspace =>
            List.is_empty files && workspace == true && verbose == true,
        _ => false,
    }

// The flag must be PEELED, not left among the paths -- otherwise it is
// handed to the path expander as a filename.
#[test]
def test_from_args_test_workspace_flag_not_a_path : Bool :=
    match Command.from_args ["test", "--workspace", "a.mo"] {
        Command.test files verbose workspace =>
            files == ["a.mo"] && workspace == true,
        _ => false,
    }

// A bare `monad test` no longer means "print help": it means "test the
// mote containing the working directory" (and only falls back, at RUN
// time and with exit 1, to `no_target_diagnostic` when there is no such
// mote).
#[test]
def test_from_args_test_no_files_is_a_test_command : Bool :=
    match Command.from_args ["test"] {
        Command.test files verbose workspace =>
            List.is_empty files && workspace == false && verbose == false,
        _ => false,
    }

#[test]
def test_from_args_help_on_empty : Bool :=
    match Command.from_args [] {
        Command.help => true,
        _ => false,
    }

#[test]
def test_from_args_help_on_unknown : Bool :=
    match Command.from_args ["bogus"] {
        Command.help => true,
        _ => false,
    }

// ─── the IR path ───
//
// Not argv parsing, but the other pure rule in `main.mo`, and the one the
// artifact cache's correctness rests on: the file `llc` is pointed at must
// be named by the cache key rather than by the output, because `llc`
// records that name (its basename) in the object it emits, and an object
// that records the output name is an object that differs between two
// builds of one unchanged source. `Build.artifact_ir_path` supplies the
// keyed path; `resolve_ir_path` is what lets every caller with no key to
// name one by keep the output-derived path it always had.

/// A key is a key: the IR follows it and nothing else. There is no
/// output-name parameter to pass, and that is the fix stated as a type.
#[test]
def test_resolve_ir_path_prefers_the_keyed_path : Bool :=
    String.beq
        (Path.to_string (resolve_ir_path (Option.some (Path.path "target/store/abc.ll")) (Path.path "out") (Path.path "hello")))
        "target/store/abc.ll"

/// The no-key fallback: `run`, the test driver, and a build whose
/// compiler digest could not be taken. Unchanged behaviour for all of
/// them, which is why they did not have to change.
#[test]
def test_resolve_ir_path_falls_back_to_the_output : Bool :=
    String.beq
        (Path.to_string (resolve_ir_path Option.none (Path.path "out") (Path.path "hello")))
        "out/hello.ll"

/// ...and the fallback still honours `Path.join`'s absolute-name rule,
/// which is what every ladder script's absolute `-o` relies on.
#[test]
def test_resolve_ir_path_fallback_replaces_an_absolute_output : Bool :=
    String.beq
        (Path.to_string (resolve_ir_path Option.none (Path.path "out") (Path.path "/tmp/x/hello")))
        "/tmp/x/hello.ll"
