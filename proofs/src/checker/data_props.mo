/// Source-level pins for the data-type theorems and the sort-generic
/// `Sigma`/`Exists`.
///
/// The user's constraint for this work: do NOT add checker special cases for
/// proofs. Each rejection below therefore asserts that the EXISTING checker
/// refuses the source, and that the diagnostic's own text is a type mismatch
/// (not a parse or resolution failure). The acceptance controls use the same
/// names and types.
///
/// This goes through `check_file_cached_from_source_ranged`, the real
/// elaboration + per-declaration walk `monad check` uses, with the ambient
/// prelude included -- see `lang/src/tests/typecheck_negative_tests.mo`,
/// whose harness this mirrors. `PPath`/`prefl` are declared locally because
/// the fixture cannot import `proofs/` (renamed away from `Path`/`refl` so the
/// ambient std tier cannot collide with them).
use lang::module {
  Diagnostic, check_file_cached_from_source_ranged, diagnostic_message,
  module_info_cache_empty, ranged_file_diagnostics,
}
use std::path {Path}
use std::process {exec_cmd, process_id}
use std::test {Test.write_fixture}
open IO {println}

#[terminating]
def messages_of (ds : List Diagnostic) : List String :=
    match ds {
        List.empty => List.empty,
        List.cons d rest => List.cons (diagnostic_message d) (messages_of rest),
    }

#[terminating]
def joined (msgs : List String) : String :=
    match msgs {
        List.empty => "",
        List.cons m rest => String.concat m (String.concat "\n  " (joined rest)),
    }

#[terminating]
def message_named (name : String) (msgs : List String) : Option String :=
    match msgs {
        List.empty => Option.none,
        List.cons m rest =>
            if String.contains m (String.concat " in " name)
            then Option.some m
            else message_named name rest,
    }

def probe_dir : String := "/tmp/monad_data_props_" ++ I64.to_string process_id

def probe_path : String := probe_dir ++ "/probe.mo"

#[partial]
def diagnostics_for (src : String) : IO (List String) := do {
    let _mk <- exec_cmd "mkdir" ["-p", probe_dir];
    let _w <- Test.write_fixture (Path.path probe_path) src;
    let checked <- check_file_cached_from_source_ranged module_info_cache_empty probe_path src false;
    return (messages_of (ranged_file_diagnostics checked))
}

#[partial]
def rejected_with (name : String) (needle : String) (src : String) : IO Bool := do {
    let msgs <- diagnostics_for src;
    // `msgs` is read twice (the named lookup, then the full report), so share
    // it: `Shared.get`'s reads are borrowed and the affine rule exempts them.
    let shared : Shared (List String) := Shared.of msgs;
    match message_named name (Shared.get shared) {
        Option.none => do {
            println ("MISSING: expected a diagnostic naming " ++ name ++ "; got:\n  " ++ joined (Shared.get shared));
            return false
        },
        Option.some m =>
            if String.contains m needle
            then return true
            else do {
                println ("WRONG DIAGNOSTIC for " ++ name ++ " (expected text containing \"" ++ needle ++ "\")");
                return false
            },
    }
}

#[partial]
def accepted (src : String) : IO Bool := do {
    let msgs <- diagnostics_for src;
    match msgs {
        List.empty => return true,
        // Use the pattern binders rather than `msgs` again: the affine rule
        // counts the scrutinee as one use and a second mention as another.
        List.cons m rest => do {
            println ("UNEXPECTED diagnostics:\n  " ++ joined (List.cons m rest));
            return false
        },
    }
}

def mismatch : String := "type mismatch"

/// A wrong path ENDPOINT is refused by the path-boundary rule, whose own
/// message is "the path body's i1 boundary does not match the type's right
/// endpoint" -- the correct reason for that shape, not a generic mismatch.
def boundary_failure : String := "boundary"

/// The local path vocabulary the fixture needs (`proofs/src/equiv.mo` and
/// `paths.mo` are not importable from a source-buffer fixture).
///
/// MONOMORPHIC on purpose: the real `Path` is level-polymorphic, and in this
/// position its universe is left undetermined (`PPath Prop …`), which would
/// turn every acceptance control red for an unrelated reason. The pins are
/// about endpoint REJECTION, not universe inference. Bodies are path lambdas
/// for the same reason: `prefl`'s implicit element type is under-solved at a
/// def boundary, while the lambda is checked against the line type directly.
def path_prelude : String :=
    String.concat
        "pub def PPath (A : Type) (a : A) (b : A) : Type := Cubical.PathP (fn _ => A) a b\n"
        "pub def prefl {A : Type} (a : A) : PPath A a a := fn (i : Cubical.I) => a\n"

// ── Nat ────────────────────────────────────────────────────────────────

#[test]
def test_a_false_nat_path_is_rejected : IO Bool :=
    rejected_with "bad_nat" boundary_failure
        (String.concat path_prelude
            "def bad_nat : PPath Nat Nat.zero (Nat.succ Nat.zero) := fn (i : Cubical.I) => Nat.zero\n")

#[test]
def test_a_true_nat_path_is_accepted : IO Bool :=
    accepted (String.concat path_prelude
        "def ok_nat : PPath Nat Nat.zero Nat.zero := fn (i : Cubical.I) => Nat.zero\n")

// ── Bool ───────────────────────────────────────────────────────────────

#[test]
def test_a_false_bool_path_is_rejected : IO Bool :=
    rejected_with "bad_bool" boundary_failure
        (String.concat path_prelude
            "def bad_bool : PPath Bool Bool.true Bool.false := fn (i : Cubical.I) => Bool.true\n")

#[test]
def test_a_true_bool_path_is_accepted : IO Bool :=
    accepted (String.concat path_prelude
        "def ok_bool : PPath Bool Bool.true Bool.true := fn (i : Cubical.I) => Bool.true\n")

// ── List ───────────────────────────────────────────────────────────────

#[test]
def test_a_false_list_path_is_rejected : IO Bool :=
    rejected_with "bad_list" boundary_failure
        (String.concat path_prelude
            "def bad_list : PPath (List Nat) (List.cons Nat.zero List.empty) List.empty := fn (i : Cubical.I) => List.cons Nat.zero List.empty\n")

#[test]
def test_a_true_list_path_is_accepted : IO Bool :=
    accepted (String.concat path_prelude
        "def ok_list : PPath (List Nat) List.empty List.empty := fn (i : Cubical.I) => List.empty\n")

// ── Void / false ───────────────────────────────────────────────────────

#[test]
def test_a_void_value_is_rejected : IO Bool :=
    rejected_with "bad_void" mismatch "def bad_void : Void := 0i64\n"

// ── Sigma / Exists ─────────────────────────────────────────────────────

#[test]
def test_exists_is_a_prop : IO Bool :=
    accepted "def ok_exists : Prop := Exists Nat (fn _ => True)\n"

#[test]
def test_sigma_at_type_is_accepted : IO Bool :=
    accepted "def ok_sigma_type : Type := Sigma Nat (fn _ => Nat)\n"

#[test]
def test_sigma_at_prop_is_accepted : IO Bool :=
    accepted "def ok_sigma_prop : Prop := Sigma Nat (fn _ => Nat)\n"

// ── Monad law (the shape the LawfulMonad proofs must NOT use) ──────────

#[test]
def test_a_wrong_monad_law_is_rejected : IO Bool :=
    rejected_with "bad_right" mismatch
        (String.concat path_prelude
            "def bad_right {A : Type} (m : Id A) : PPath (Id A) (Monad.bind m Monad.pure) m := prefl m\n")
