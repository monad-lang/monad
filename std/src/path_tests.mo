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

// `raw_path_join` at the `String` level. The absolute-rhs rule used to
// live only in `Path.join`, so every direct caller of the raw join kept
// the bug the `Path` type exists to prevent -- most visibly
// `Mote.dep_dir_entries_go`, which joins a manifest `[dependencies.X]
// path` onto the mote's own directory. With a bare invocation that
// directory is ".", so an absolute path dep came out as "./<abs>" and
// the dependency silently did not resolve.

/// The exact shape the bare-invocation bug produced.
#[test]
def test_raw_path_join_absolute_rhs_discards_lhs : Bool :=
    String.beq (raw_path_join "." "/home/x/init") "/home/x/init"

#[test]
def test_raw_path_join_absolute_rhs_with_empty_lhs : Bool :=
    String.beq (raw_path_join "" "/home/x/init") "/home/x/init"

/// A relative rhs must still concatenate -- the fix must not make every
/// join absolute-ish.
#[test]
def test_raw_path_join_relative_rhs_concatenates : Bool :=
    String.beq (raw_path_join "." "init") "./init"

#[test]
def test_raw_path_join_relative_rhs_under_absolute_lhs : Bool :=
    String.beq (raw_path_join "/tmp" "monad_v2") "/tmp/monad_v2"

#[test]
def test_raw_path_join_empty_components_are_noop : Bool :=
    String.beq (raw_path_join "" "init") "init"
    && String.beq (raw_path_join "/tmp" "") "/tmp"
    && String.beq (raw_path_join "" "") ""

#[test]
def test_raw_path_join_trailing_slash_lhs : Bool :=
    String.beq (raw_path_join "a/" "b") "a/b"

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

// `Path.parent` -- the directory half, none when there is none (a
// `Path` is never empty, and callers must not `mkdir -p` nothing).

def parent_is (p : String) (want : Option String) : Bool :=
    String.beq (parent_text (Path.parent (Path.path p))) (want_text want)

def parent_text (d : Option Path) : String :=
    match d { Option.some p => Path.to_string p, Option.none => "<none>" }

def want_text (w : Option String) : String :=
    match w { Option.some s => s, Option.none => "<none>" }

#[test]
def test_path_parent_of_nested_path : Bool :=
    parent_is "/tmp/out/monad" (Option.some "/tmp/out")

#[test]
def test_path_parent_of_bare_filename_is_none : Bool :=
    parent_is "hello.mo" Option.none

#[test]
def test_path_parent_of_root_child_is_none : Bool :=
    parent_is "/monad" Option.none

#[test]
def test_path_parent_keeps_relative_prefix : Bool :=
    parent_is "out/bin/monad" (Option.some "out/bin")

// `Path.file_name` -- the last component.

#[test]
def test_path_file_name_of_nested_path : Bool :=
    String.beq (Path.file_name (Path.path "/tmp/out/monad.ll")) "monad.ll"

#[test]
def test_path_file_name_of_bare_name : Bool :=
    String.beq (Path.file_name (Path.path "hello.mo")) "hello.mo"

#[test]
def test_path_file_name_of_list_dir_entry : Bool :=
    String.beq (Path.file_name (Path.join (Path.path "lang/") (Path.path "src"))) "src"

// A trailing slash on the directory is not doubled -- `IO.list_dir`
// joins its entries this way, so `monad test lang/` reports
// `lang/src/...`, and the fix has to hold at every level of a walk.

#[test]
def test_path_join_strips_trailing_slash : Bool :=
    String.beq (Path.to_string (Path.join (Path.path "lang/") (Path.path "src"))) "lang/src"

#[test]
def test_path_join_nested_stays_single : Bool :=
    let a : Path := Path.join (Path.path "lang/") (Path.path "src") in
    String.beq (Path.to_string (Path.join a (Path.path "codegen"))) "lang/src/codegen"
