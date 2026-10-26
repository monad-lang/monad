/// End-to-end tests for the /try engine's in-memory pipeline. Native: the
/// sources are read from `init/src` on disk -- the same files the site
/// serves -- so the normal `monad test motes/try_engine` sweep covers the
/// real path, and a module that stops parsing fails here first.

use lib::pipeline {run_source}
use lib::sources {SourceModule, identity_of_path}
use std::io {IO.list_dir, IO.read_file}
use std::path {Path, Path.to_string}

def init_dir : String := "init/src"

/// Every `.mo` under `init/src`, framed the way the page frames them: a
/// superset of the prelude closure, exactly like the `sources/` tree
/// `scripts/build-try.sh` stages. Test-only modules are harmless -- the
/// pipeline loads only what the program reaches.
#[terminating]
def load_sources : IO (List SourceModule) := do {
    let entries <- IO.list_dir (Path.path init_dir);
    collect_sources entries List.empty
}

#[terminating]
def collect_sources (paths : List Path) (acc : List SourceModule) : IO (List SourceModule) :=
    match paths {
        List.empty => IO.pure (List.reverse acc),
        List.cons p rest =>
            if String.ends_with (Path.to_string p) ".mo"
            then do {
                let loaded <- read_source p;
                match loaded {
                    Option.none => collect_sources rest acc,
                    Option.some m => collect_sources rest (List.cons m acc),
                }
            }
            else collect_sources rest acc,
    }

def read_source (p : Path) : IO (Option SourceModule) := do {
    let text <- IO.read_file p;
    match text {
        Result.err _e => IO.pure Option.none,
        Result.ok source =>
            match identity_of_path (Path.to_string p) {
                Result.err _e => IO.pure Option.none,
                Result.ok ident =>
                    match ident {
                        Pair.pair segments mote =>
                            let module_ : SourceModule :=
                                { segments := segments, mote := mote,
                                  file_path := Path.to_string p, source := source }
                            in
                            IO.pure (Option.some module_),
                    },
            },
    }
}

def outcome_is (sources : List SourceModule) (source : String) (status : I64)
    (value : String) (typ : String) : IO Bool := do {
    let o <- run_source sources source;
    return (I64.beq o.status status && String.beq o.value value && String.beq o.typ typ)
}

def status_is (sources : List SourceModule) (source : String) (want : I64) : IO Bool := do {
    let o <- run_source sources source;
    return (I64.beq o.status want)
}

#[test]
def test_arithmetic : IO Bool := do {
    let sources <- load_sources;
    outcome_is sources "def main : I64 := 2 + 3\n" 0 "5" "I64"
}

#[test]
def test_definition_then_use : IO Bool := do {
    let sources <- load_sources;
    outcome_is sources
        "def square (n : I64) : I64 := I64.mul n n\n\ndef main : I64 := square 12\n"
        0 "144" "I64"
}

#[test]
def test_string : IO Bool := do {
    let sources <- load_sources;
    outcome_is sources
        "def main : String := String.concat \"Hello, \" \"Monad!\"\n"
        0 "\"Hello, Monad!\"" "String"
}

#[test]
def test_list : IO Bool := do {
    let sources <- load_sources;
    outcome_is sources
        "def main : List I64 := List.map (fn (x : I64) => I64.mul x 2) [1, 2, 3]\n"
        0 "[2, 4, 6]" "(List I64)"
}

#[test]
def test_option_match : IO Bool := do {
    let sources <- load_sources;
    outcome_is sources
        "def describe (o : Option I64) : String :=\n    match o { some x => \"some\", none => \"none\" }\n\ndef main : String := describe (Option.some 3)\n"
        0 "\"some\"" "String"
}

/// A module that was never part of the old embedded nine still resolves:
/// the served tree is all of `init/src`, not a hand-picked closure.
#[test]
def test_module_outside_the_prelude_closure_resolves : IO Bool := do {
    let sources <- load_sources;
    outcome_is sources "use init::foldable {}\n\ndef main : I64 := 1\n" 0 "1" "I64"
}

#[test]
def test_parse_error_is_status_1 : IO Bool := do {
    let sources <- load_sources;
    status_is sources "def main : I64 := 2 +\n" 1
}

#[test]
def test_type_error_is_status_2 : IO Bool := do {
    let sources <- load_sources;
    status_is sources "def main : I64 := totally_unknown\n" 2
}

#[test]
def test_missing_main_is_status_2 : IO Bool := do {
    let sources <- load_sources;
    status_is sources "def helper : I64 := 1\n" 2
}

#[test]
def test_float_literal_is_a_lower_error : IO Bool := do {
    let sources <- load_sources;
    status_is sources "def main : F64 := 1.5\n" 3
}

#[test]
def test_std_use_is_rejected : IO Bool := do {
    let sources <- load_sources;
    status_is sources "use std::map\n\ndef main : I64 := 1\n" 2
}

#[test]
def test_ok_has_no_error_text : IO Bool := do {
    let sources <- load_sources;
    let o <- run_source sources "def main : I64 := 1\n";
    return (String.is_empty o.error)
}
