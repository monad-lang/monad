// `bootstrap-next`: the two-rung bootstrap for a feature-gated native.
//
//   monad script bootstrap-next -- [--features a,b] [--out DIR] [--debug]
//                                 [--fixpoint] [--test a,b] [--host BIN]
//
// Rung 1 compiles this tree with the CURRENT host, features OFF -- the
// two-step rollout's first half, and the thing it exists to prove: the last
// published nightly must still compile the tree.
//
// Rung 2 compiles the same source with rung 1 and `MONAD_FEATURES=<features>`
// on. Rung 1 carries the new natives' wiring, so the compiler-source surface
// may now USE them: a tree can exercise a brand-new native end to end before
// any nightly contains it.
//
// Default features come from `bootstrap/next-features.txt`, one per line
// (`#` starts a comment). That file is EMPTY when nothing is pending, which
// makes rung 2 a plain two-step fixpoint turn.
//
// `--fixpoint` builds a third rung with rung 2 and compares the two `.ll`
// files written beside their binaries -- the ladder's own bit-for-bit check.
//
// The command line is declared with `clap`'s spec API (`clap::spec` +
// `clap::parse`), not hand-rolled: `--help`/usage text come from the same
// table the parser checks, so a flag cannot exist in one and not the other.
//
// The script itself uses only `std` (`process`, `path`, `stream`), `clap`'s
// spec parser and `IO`, so the current nightly can compile it.
//
// A value bound from an `IO` action is matched only through a typed helper
// parameter (`read_text`/`report`, `start_with`, `compare_both`): the
// self-hosted checker cannot infer a scrutinee through a `do` bind, and a
// match on an unknown type is an error.

use clap::help {Cli.usage}
use clap::parse {Cli.parse}
use clap::spec {*}
use std::process {exec_cmd}
use std::stream {StreamError}

open IO {println, read_file}

struct Options {
    features : String,
    out : String,
    debug : Bool,
    fixpoint : Bool,
    tests : String,
    host : String
}

instance Copy Options {
    def copy (o : Options) : Pair Options Options := Pair.pair o o
}

def default_options : Options :=
    { features := "", out := "target-monad/bootstrap-next", debug := false, fixpoint := false, tests := "", host := "" }

// ─── Arguments ──────────────────────────────────────────────────────────

/// The command line, declared once through `clap`'s spec API. `monad script`
/// hands the script everything after `--`.
def cli_spec : Cli.CommandSpec :=
    Cli.with_args
        [Cli.option_optional "features" "" "a,b" "comma-separated feature list (default: bootstrap/next-features.txt)"
            , Cli.option_optional "out" "" "DIR" "output root (default: target-monad/bootstrap-next)"
            , Cli.option_optional "test" "" "a,b" "paths to run through rung 2"
            , Cli.option_optional "host" "" "BIN" "rung-1 host binary (default: monad, the nightly)"
            , Cli.flag "debug" "" "build the debug profile instead of --release"
            , Cli.flag "fixpoint" "" "build rung 3 with rung 2 and require identical IR"
        ]
        (Cli.command "bootstrap-next" "the two-rung bootstrap for a feature-gated native")

#[terminating]
def fold_options (xs : List Cli.ArgValue) (o : Options) : Options :=
    match xs {
        List.empty => o,
        List.cons x rest =>
            match x {
                { name, value } =>
                    if String.beq name "features" then fold_options rest { o with features := value }
                    else if String.beq name "out" then fold_options rest { o with out := value }
                    else if String.beq name "test" then fold_options rest { o with tests := value }
                    else if String.beq name "host" then fold_options rest { o with host := value }
                    else fold_options rest o,
            },
    }

#[terminating]
def fold_flags (xs : List String) (o : Options) : Options :=
    match xs {
        List.empty => o,
        List.cons x rest =>
            if String.beq x "debug" then fold_flags rest { o with debug := true }
            else if String.beq x "fixpoint" then fold_flags rest { o with fixpoint := true }
            else fold_flags rest o,
    }

/// `Cli.Parsed` is affine, so it is destructured ONCE and each list folded
/// once; `Cli.flag_set`/`Cli.option_value` would each consume it again.
def options_of (p : Cli.Parsed) : Options :=
    match p {
        { flags, options, .. } => fold_flags flags (fold_options options default_options)
    }

// ─── Feature lists ───────────────────────────────────────────────────────

#[terminating]
def split_pieces (s : String) (sep : U8) (i : I64) (start : I64) (acc : List String) : List String :=
    if I64.lt i (String.length s) then
        let got : Option U8 := String.get s i in
        match got {
            Option.some b =>
                if U8.beq b sep
                then split_pieces s sep (i + 1) (i + 1) (push_piece s start i acc)
                else split_pieces s sep (i + 1) start acc,
            Option.none => acc
        }
    else push_piece s start i acc

def push_piece (s : String) (start : I64) (stop : I64) (acc : List String) : List String :=
    let piece : String := String.trim (String.slice s start (stop - start)) in
    if String.is_empty piece then acc else List.cons piece acc

/// Drop blank pieces and `#` comments, keeping the order the file has.
#[terminating]
def clean_pieces (xs : List String) (acc : List String) : List String :=
    match xs {
        List.empty => List.reverse acc,
        List.cons x rest =>
            if String.is_empty x then clean_pieces rest acc
            else if String.starts_with "#" x then clean_pieces rest acc
            else clean_pieces rest (List.cons x acc)
    }

#[terminating]
def join_commas (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons x rest =>
            match rest {
                List.empty => x,
                List.cons _ _ => String.concat x (String.concat "," (join_commas rest))
            }
    }

def features_of_text (r : Result StreamError String) : Result String String :=
    match r {
        Result.ok text => Result.ok (join_commas (clean_pieces (split_pieces text 10u8 0 0 List.empty) List.empty)),
        Result.err e => Result.err (String.concat "bootstrap/next-features.txt: " e.message)
    }

def features_from_file : IO (Result String String) := do {
    let read <- read_file (Path.path "bootstrap/next-features.txt");
    IO.pure (features_of_text read)
}

def resolve_features (o : Options) : IO (Result String String) :=
    if String.is_empty o.features
    then features_from_file
    else IO.pure (Result.ok (join_commas (clean_pieces (split_pieces o.features 44u8 0 0 List.empty) List.empty)))

// ─── The rungs ───────────────────────────────────────────────────────────

def rung_one_bin (o : Options) : String := String.concat (String.concat o.out "/rung1") "/monad"

def rung_two_bin (o : Options) : String := String.concat (String.concat o.out "/rung2") "/monad"

/// `--release` unless `--debug` asked for the faster-to-build profile.
def mode_args (o : Options) : List String :=
    if o.debug then List.empty else ["--release"]

/// Rung 1: the current host compiles this tree with features OFF, so the
/// gate is exactly "does the last published nightly still read the tree".
def rung_one (o : Options) : IO I64 := do {
    let dir : String := String.concat o.out "/rung1";
    let _ <- exec_cmd "mkdir" ["-p", dir];
    let host : String := if String.is_empty o.host then "monad" else o.host;
    println (String.concat "bootstrap-next: rung 1 (host " (String.concat host ")"));
    exec_cmd "env" (List.append ["MONAD_HOST_BIN=" ++ host, "MONAD_FEATURES=", "bash", "scripts/build-self-hosted.sh", dir] (mode_args o))
}

/// Rung 2: the binary rung 1 produced compiles the tree again, with the
/// pending features ON.
def rung_two (o : Options) (feats : String) : IO I64 := do {
    let dir : String := String.concat o.out "/rung2";
    let _ <- exec_cmd "mkdir" ["-p", dir];
    println (String.concat "bootstrap-next: rung 2 -> " (rung_two_bin o));
    exec_cmd "env" (List.append ["MONAD_FEATURES=" ++ feats, rung_one_bin o, "build", "cli/src/main.mo", "-o", rung_two_bin o] (mode_args o))
}

def read_text (path : String) : IO (Result String String) := do {
    let r <- read_file (Path.path path);
    IO.pure (text_or_error path r)
}

def text_or_error (path : String) (r : Result StreamError String) : Result String String :=
    match r {
        Result.ok s => Result.ok s,
        Result.err e => Result.err (String.concat path (String.concat ": " e.message))
    }

/// The ladder's own check: rung 3 is built by rung 2 from the same source,
/// and its `.ll` must be byte-identical.
def compare_both (ra : Result String String) (rb : Result String String) : IO I64 :=
    match ra {
        Result.err e => do { println e; IO.pure 1 },
        Result.ok sa =>
            match rb {
                Result.err e => do { println e; IO.pure 1 },
                Result.ok sb =>
                    if String.beq sa sb
                    then do { println "bootstrap-next: fixpoint reached (IR identical)"; IO.pure 0 }
                    else do { println "bootstrap-next: IR differs between rung 2 and rung 3"; IO.pure 1 }
            }
    }

def compare_ir (a : String) (b : String) : IO I64 := do {
    let ra <- read_text a;
    let rb <- read_text b;
    compare_both ra rb
}

def fixpoint (o : Options) (feats : String) : IO I64 :=
    if Bool.not o.fixpoint then IO.pure 0
    else do {
        let dir : String := String.concat o.out "/rung3";
        let _ <- exec_cmd "mkdir" ["-p", dir];
        let bin : String := String.concat dir "/monad";
        println "bootstrap-next: rung 3 (fixpoint)";
        let rc <- exec_cmd "env" (List.append ["MONAD_FEATURES=" ++ feats, rung_two_bin o, "build", "cli/src/main.mo", "-o", bin] (mode_args o));
        if Bool.not (I64.beq rc 0)
        then do { println "bootstrap-next: rung 3 failed"; IO.pure 1 }
        else compare_ir (String.concat (rung_two_bin o) ".ll") (String.concat bin ".ll")
    }

def run_tests (o : Options) (feats : String) : IO I64 :=
    if String.is_empty o.tests then IO.pure 0
    else do {
        let paths : List String := clean_pieces (split_pieces o.tests 44u8 0 0 List.empty) List.empty;
        println (String.concat "bootstrap-next: test " o.tests);
        exec_cmd "env" (List.append ["MONAD_FEATURES=" ++ feats, rung_two_bin o, "test"] paths)
    }

def verify (o : Options) (feats : String) : IO I64 := do {
    println "bootstrap-next: checking cli/src/main.mo through rung 2";
    let rc <- exec_cmd "env" ["MONAD_FEATURES=" ++ feats, rung_two_bin o, "check", "cli/src/main.mo"];
    if Bool.not (I64.beq rc 0) then do { println "bootstrap-next: rung 2 cannot check the tree"; IO.pure 1 }
    else tests_then_fixpoint o feats
}

def tests_then_fixpoint (o : Options) (feats : String) : IO I64 := do {
    let rc <- run_tests o feats;
    if Bool.not (I64.beq rc 0) then do { println "bootstrap-next: tests failed"; IO.pure 1 }
    else fixpoint o feats
}

def after_rung_one (o : Options) (feats : String) : IO I64 := do {
    let rc <- rung_two o feats;
    if Bool.not (I64.beq rc 0) then do { println "bootstrap-next: rung 2 failed"; IO.pure 1 }
    else verify o feats
}

/// The feature list arrives as `Result` from an `IO` bind, so it is matched
/// through this typed parameter rather than at the call site.
def start_with (o : Options) (resolved : Result String String) : IO I64 :=
    match resolved {
        Result.err e => do { println (String.concat "bootstrap-next: " e); IO.pure 2 },
        Result.ok raw => do {
            let feats : String := raw;
            let shown : String := if String.is_empty feats then "(none)" else feats;
            println (String.concat "bootstrap-next: features " shown);
            let rc <- rung_one o;
            if Bool.not (I64.beq rc 0) then do { println "bootstrap-next: rung 1 failed"; IO.pure 1 }
            else after_rung_one o feats
        }
    }

def run_all (o : Options) : IO I64 := do {
    let resolved <- resolve_features o;
    start_with o resolved
}

def main (args : List String) : IO I64 :=
    match Cli.parse cli_spec args {
        Cli.parse_ok parsed => run_all (options_of parsed),
        Cli.parse_help text => do { println text; IO.pure 0 },
        Cli.parse_version text => do { println text; IO.pure 0 },
        Cli.parse_err message => do {
            println (String.concat "bootstrap-next: " message);
            println (Cli.usage cli_spec);
            IO.pure 2
        },
    }
