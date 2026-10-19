/// Attribute-string decoding tests: the canonical form the compiler's
/// reflection writes into `FieldInfo.attrs`.
use clap::args {*}

def opt_is (o : Option String) (v : String) : Bool :=
    match o {
        Option.some x => String.beq x v,
        Option.none => false,
    }

#[test]
def test_attr_name_bare : Bool :=
    String.beq (Cli.attr_name "arg") "arg"

#[test]
def test_attr_name_with_args : Bool :=
    String.beq (Cli.attr_name "arg(short:=\"v\")") "arg"

#[test]
def test_attr_has : Bool :=
    Cli.attr_has "arg" ["no_short", "arg(short:=\"v\")"] && Bool.not (Cli.attr_has "arg" ["pos"])

#[test]
def test_attr_arg_short : Bool :=
    opt_is (Cli.attr_arg "arg" "short" ["arg(short:=\"v\",help:=\"x\")"]) "v"

#[test]
def test_attr_arg_help_with_comma : Bool :=
    opt_is (Cli.attr_arg "arg" "help" ["arg(short:=\"v\",help:=\"a, b\")"]) "a, b"

#[test]
def test_attr_arg_escaped_quotes_and_backslashes : Bool :=
    opt_is (Cli.attr_arg "arg" "help" ["arg(help:=\"a\\\"b\\\\c\")"]) "a\"b\\c"

#[test]
def test_attr_arg_absent : Bool :=
    match Cli.attr_arg "arg" "short" ["arg"] {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_kebab_replaces_underscores : Bool :=
    String.beq (Cli.kebab "max_turns") "max-turns"

#[test]
def test_kebab_drops_trailing_underscore : Bool :=
    String.beq (Cli.kebab "use_") "use"
