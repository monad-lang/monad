/// The level macros format through `fmt!` and respect the minimum level.
use log::macros {trace, debug, info, warn, error}
use log::level {LogLevel}
use log::logger {Logger, Logger.with_sink}
use std::ref {Ref, Ref.new, Ref.get, Ref.set}
use std::list {List.any}

/// A logger whose lines collect in `r`, newest first.
def capture (r : Ref (List String)) (min : LogLevel) : Logger :=
    Logger.with_sink min (fn (line : String) => do {
        let seen <- Ref.get r;
        Ref.set r (List.cons line seen)
    })

def has (lines : List String) (needle : String) : Bool :=
    List.any (fn (l : String) => String.contains l needle) lines

#[test]
def test_macros_format_their_template : IO Bool := do {
    let r <- Ref.new List.empty;
    let log : Logger := capture r LogLevel.trace;
    let n : I64 := 7;
    let who : String := "weaver";
    trace! log "t {n}";
    debug! log "d {who}";
    info! log "built {n} files";
    warn! log "w {n:>3}";
    error! log "e {{x}}";
    let lines <- Ref.get r;
    IO.pure (List.length lines == 5
        && has lines "TRACE t 7"
        && has lines "DEBUG d weaver"
        && has lines "INFO built 7 files"
        && has lines "WARN w   7"
        && has lines "ERROR e {x}")
}

#[test]
def test_macros_respect_the_minimum : IO Bool := do {
    let r <- Ref.new List.empty;
    let log : Logger := capture r LogLevel.warn;
    let n : I64 := 1;
    debug! log "dropped {n}";
    info! log "dropped {n}";
    warn! log "kept {n}";
    let lines <- Ref.get r;
    IO.pure (List.length lines == 1 && has lines "WARN kept 1")
}
