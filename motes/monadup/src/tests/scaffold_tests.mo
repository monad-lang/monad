/// `monadup new`'s pure surface: name validation and the generated files.
use lib::scaffold {*}

#[test]
def test_name_accepts_identifiers : Bool :=
    match Scaffold.validate_name "hello_world" { Result.ok _ => true, Result.err _ => false }
        && match Scaffold.validate_name "a-b.c9" { Result.ok _ => true, Result.err _ => false }
        && match Scaffold.validate_name "A1" { Result.ok _ => true, Result.err _ => false }

#[test]
def test_name_rejects_unsafe_shapes : Bool :=
    match Scaffold.validate_name "" { Result.err _ => true, Result.ok _ => false }
        && match Scaffold.validate_name "." { Result.err _ => true, Result.ok _ => false }
        && match Scaffold.validate_name ".." { Result.err _ => true, Result.ok _ => false }
        && match Scaffold.validate_name "-x" { Result.err _ => true, Result.ok _ => false }
        && match Scaffold.validate_name "a b" { Result.err _ => true, Result.ok _ => false }
        && match Scaffold.validate_name "a/b" { Result.err _ => true, Result.ok _ => false }

#[test]
def test_name_rejects_quotes_and_newlines : Bool :=
    match Scaffold.validate_name "a\"b" { Result.err _ => true, Result.ok _ => false }
        && match Scaffold.validate_name "a\nb" { Result.err _ => true, Result.ok _ => false }
        && match Scaffold.validate_name "café" { Result.err _ => true, Result.ok _ => false }

#[test]
def test_manifest_is_well_formed : Bool :=
    let m : String := Scaffold.manifest "demo" in
    String.contains m "name = \"demo\""
        && String.contains m "[[bin]]"
        && String.contains m "path = \"src/main.mo\""

#[test]
def test_main_source_greets : Bool :=
    String.contains (Scaffold.main_source "demo") "Hello from demo!"

#[test]
def test_target_dir_respects_base : Bool :=
    String.beq (Scaffold.target_dir (Option.some "/tmp") "demo") "/tmp/demo"
        && String.beq (Scaffold.target_dir Option.none "demo") "demo"
