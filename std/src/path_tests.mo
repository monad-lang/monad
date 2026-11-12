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

// `Path.normalize` -- one file has one spelling. The `..` rules are the
// load-bearing part: a mote-relative join legitimately carries `..`, and
// codegen's per-file dedup compares the recorded spelling.

#[test]
def test_path_normalize_cancels_parent_segments : Bool :=
    String.beq (Path.to_string (Path.normalize (Path.path "a/../b"))) "b"

#[test]
def test_path_normalize_drops_current_and_repeated_separators : Bool :=
    String.beq (Path.to_string (Path.normalize (Path.path "./a//b"))) "a/b"

#[test]
def test_path_normalize_keeps_absolute_root : Bool :=
    String.beq (Path.to_string (Path.normalize (Path.path "/a/../b"))) "/b"

#[test]
def test_path_normalize_keeps_leading_parent : Bool :=
    String.beq (Path.to_string (Path.normalize (Path.path "../init/src"))) "../init/src"

#[test]
def test_path_normalize_empty_is_current_dir : Bool :=
    String.beq (Path.to_string (Path.normalize (Path.unsafe ""))) "."

// `Path.extension` / `Path.file_stem` / `Path.child`.

#[test]
def test_path_extension : Bool :=
    match Path.extension (Path.path "/a/b.mo") {
        Option.some e => String.beq e "mo",
        Option.none => false,
    }

#[test]
def test_path_extension_of_dotfile_is_none : Bool :=
    match Path.extension (Path.path "/a/.gitignore") {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_path_file_stem : Bool :=
    String.beq (Path.file_stem (Path.path "/a/b.mo")) "b"
        && String.beq (Path.file_stem (Path.path "/a/.gitignore")) ".gitignore"

#[test]
def test_path_child : Bool :=
    String.beq (Path.to_string (Path.child (Path.path "/tmp") "a")) "/tmp/a"
        && String.beq (Path.to_string (Path.child (Path.path "/tmp") "/abs")) "/abs"

/// A directory root spelled `.` contributes no prefix, which is what keeps
/// a working-directory mote's joins (`src/main.mo`, `mote.toml`) spelled the
/// way they were before the root became a `Path`. Any other root joins
/// normally and an absolute segment still replaces the root.
#[test]
def test_path_child_under_treats_the_cwd_root_as_empty : Bool :=
    String.beq (Path.to_string (Path.child_under (Path.unsafe_dir "") "src")) "src"
        && String.beq (Path.to_string (Path.child_under (Path.path ".") "src/main.mo")) "src/main.mo"
        && String.beq (Path.to_string (Path.child_under (Path.path "lang") "src/lib.mo")) "lang/src/lib.mo"
        && String.beq (Path.to_string (Path.child_under (Path.path "lang/../std") "src")) "lang/../std/src"
        && String.beq (Path.to_string (Path.child_under (Path.path "lang") "/abs")) "/abs"

/// `Path.unsafe_dir` is the boundary for a directory spelling: the empty
/// string (the CWD) becomes `.`, and nothing else is touched.
#[test]
def test_path_unsafe_dir_spells_the_cwd_as_dot : Bool :=
    String.beq (Path.to_string (Path.unsafe_dir "")) "."
        && String.beq (Path.to_string (Path.unsafe_dir "motes/x")) "motes/x"
        && String.beq (Path.to_string (Path.unsafe_dir ".")) "."

#[test]
def test_path_of_reports_structured_error : Bool :=
    match Path.of "" {
        err e => match e { PathError.empty => true },
        ok _ => false,
    }
