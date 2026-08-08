/// Smoke tests for `lang/main.mo`'s `Command.from_args` argv parser.
///
/// `cargo run -- run lang/main.mo ...` (actually executing `main`) hits a
/// separate, pre-existing `instance-Monad-IO not found` failure on this
/// branch, unrelated to this change — reproduces on a clean checkout with a
/// trivial `def main : IO I64 { ... }` too — so exercising the argv-parsing
/// logic directly here is the available signal.
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
