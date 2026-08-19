/// Smoke tests for `lang/main.mo`'s `Command.from_args` argv parser.
///
/// This used to say `cargo run -- run lang/main.mo ...` (actually
/// executing `main`) hit a separate, pre-existing `instance-Monad-IO
/// not found` failure — no longer reproduces (confirmed via many real
/// `compile`/`check`/`pretty`/`test` invocations, 2026-08-19); whatever
/// that was has since been fixed elsewhere, or this repro was itself
/// stale. Kept testing `Command.from_args` directly anyway (isolating
/// argv-parsing from everything downstream is still the more precise
/// unit of test coverage, real end-to-end runs notwithstanding).
use lang.main {*}

#[test]
def test_from_args_compile_positional_name : Bool :=
    match Command.from_args ["compile", "a.mo", "myname"] {
        Command.compile path out_name verbose =>
            path == "a.mo" && out_name == "myname" && verbose == false,
        _ => false,
    }

#[test]
def test_from_args_compile_default_name : Bool :=
    match Command.from_args ["compile", "a.mo"] {
        Command.compile path out_name verbose =>
            path == "a.mo" && out_name == "source" && verbose == false,
        _ => false,
    }

#[test]
def test_from_args_compile_output_flag : Bool :=
    match Command.from_args ["compile", "a.mo", "--output", "out", "--verbose"] {
        Command.compile path out_name verbose =>
            path == "a.mo" && out_name == "out" && verbose == true,
        _ => false,
    }

#[test]
def test_from_args_compile_short_flags : Bool :=
    match Command.from_args ["compile", "a.mo", "-o", "out", "-v"] {
        Command.compile path out_name verbose =>
            path == "a.mo" && out_name == "out" && verbose == true,
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
        Command.test files verbose =>
            files == ["a.mo", "b.mo"] && verbose == true,
        _ => false,
    }

#[test]
def test_from_args_test_help_on_no_files : Bool :=
    match Command.from_args ["test"] {
        Command.help => true,
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
