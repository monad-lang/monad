// Regression tests for std/path.mo -- most directly
// test_path_join_absolute_rhs_discards_lhs, exercising the exact bug
// this type was introduced to prevent (a naive `++`-joined output path
// silently doubling up when one half was already absolute).

#[test]
def test_path_join_absolute_rhs_discards_lhs : Bool :=
    match Path.of "/tmp" {
        err _ => false,
        ok a => match Path.of "/tmp/monad_v2" {
            err _ => false,
            ok b => String.beq (Path.to_string (Path.join a b)) "/tmp/monad_v2",
        },
    }

#[test]
def test_path_join_relative_rhs_concatenates : Bool :=
    match Path.of "/tmp" {
        err _ => false,
        ok a => match Path.of "monad_v2" {
            err _ => false,
            ok b => String.beq (Path.to_string (Path.join a b)) "/tmp/monad_v2",
        },
    }

#[test]
def test_path_is_absolute : Bool :=
    match Path.of "/tmp" {
        err _ => false,
        ok a => match Path.of "tmp" {
            err _ => false,
            ok b => Path.is_absolute a && not (Path.is_absolute b),
        },
    }

#[test]
def test_path_of_rejects_empty : Bool :=
    match Path.of "" { err _ => true, ok _ => false }

#[test]
def test_path_with_suffix : Bool :=
    match Path.of "/tmp/monad_v2" {
        err _ => false,
        ok p => String.beq (Path.to_string (Path.with_suffix p ".ll")) "/tmp/monad_v2.ll",
    }

#[test]
def test_path_beq : Bool :=
    match Path.of "/tmp" {
        err _ => false,
        ok a => match Path.of "/tmp" {
            err _ => false,
            ok b => a == b,
        },
    }
