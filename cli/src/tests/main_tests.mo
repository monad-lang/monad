/// Smoke tests for `cli/src/main.mo`'s `Command.from_args` argv parser.
///
/// This used to say `cargo run -- run cli/src/main.mo ...` (actually
/// executing `main`) hit a separate, pre-existing `instance-Monad-IO
/// not found` failure — no longer reproduces (confirmed via many real
/// `compile`/`check`/`pretty`/`test` invocations, 2026-08-19); whatever
/// that was has since been fixed elsewhere, or this repro was itself
/// stale. Kept testing `Command.from_args` directly anyway (isolating
/// argv-parsing from everything downstream is still the more precise
/// unit of test coverage, real end-to-end runs notwithstanding).
use lib::main {*}

#[test]
def test_from_args_compile_positional_name : Bool :=
    match Command.from_args ["compile", "a.mo", "myname"] {
        Command.compile path out_name verbose debug =>
            Path.to_string path == "a.mo" && Path.to_string out_name == "myname" && verbose == false && debug == true,
        _ => false,
    }

#[test]
def test_from_args_compile_default_name : Bool :=
    match Command.from_args ["compile", "a.mo"] {
        Command.compile path out_name verbose debug =>
            Path.to_string path == "a.mo" && Path.to_string out_name == "source" && verbose == false && debug == true,
        _ => false,
    }

#[test]
def test_from_args_compile_output_flag : Bool :=
    match Command.from_args ["compile", "a.mo", "--output", "out", "--verbose"] {
        Command.compile path out_name verbose debug =>
            Path.to_string path == "a.mo" && Path.to_string out_name == "out" && verbose == true && debug == true,
        _ => false,
    }

#[test]
def test_from_args_compile_short_flags : Bool :=
    match Command.from_args ["compile", "a.mo", "-o", "out", "-v"] {
        Command.compile path out_name verbose debug =>
            Path.to_string path == "a.mo" && Path.to_string out_name == "out" && verbose == true && debug == true,
        _ => false,
    }

#[test]
def test_from_args_compile_debug_flag : Bool :=
    match Command.from_args ["compile", "a.mo", "--debug"] {
        Command.compile path out_name verbose debug =>
            Path.to_string path == "a.mo" && verbose == false && debug == true,
        _ => false,
    }

#[test]
def test_from_args_compile_debug_short_flag : Bool :=
    match Command.from_args ["compile", "a.mo", "-g", "-v"] {
        Command.compile path out_name verbose debug =>
            Path.to_string path == "a.mo" && verbose == true && debug == true,
        _ => false,
    }

/// Debug info is ON by default (rustc's own dev-profile default);
/// `--release` is how you opt out.
#[test]
def test_from_args_compile_release_opts_out_of_debug : Bool :=
    match Command.from_args ["compile", "a.mo", "--release"] {
        Command.compile path out_name verbose debug =>
            Path.to_string path == "a.mo" && verbose == false && debug == false,
        _ => false,
    }

/// An explicit `--debug` wins over `--release` -- asking twice, with
/// the more specific request, is not an error.
#[test]
def test_from_args_compile_debug_beats_release : Bool :=
    match Command.from_args ["compile", "a.mo", "--release", "--debug"] {
        Command.compile path out_name verbose debug =>
            Path.to_string path == "a.mo" && verbose == false && debug == true,
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
        Command.check files verbose =>
            files == ["a.mo", "b.mo"] && verbose == true,
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
// mote containing the working directory" (and only falls back to help,
// at RUN time, when there is no such mote).
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
