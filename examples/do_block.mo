// TODO: `IO`/`println` are used below (via the companion `open IO
// {println}`, which is unaffected) but deliberately NOT listed in THIS
// `use` — naming anything here (even just `IO`) breaks `do`-notation's
// implicit `Monad IO` instance lookup at runtime ("instance-Monad-IO not
// found", despite type-checking succeeding). A pre-existing latent bug in
// how the default checker's instance/dictionary resolution interacts with
// non-empty `use {...}` filtering — same family as the `std.map`/
// `BTreeMap` TODOs elsewhere. `open`'s own explicit filtering is
// unaffected; only `use`'s is. Restore an explicit list once fixed.
#![mote { name := "do_block", deps := [init] }]

use io {}
open IO {println}

// Do block syntax - simple expression
// Equivalent to: def say_hello : IO Unit := println "Hello from do block!"
def say_hello : IO Unit {
  println "Hello from do block!"
}

// Do block syntax - with parameters
// Equivalent to: def greet_io (name : String) : IO Unit := println name
//
// Named `greet_io` rather than `greet` deliberately: `examples/test_mote.mo`
// imports a `greet` from the `example` mote, and the Rust host's
// whole-program checker flattens EVERY loaded module's defs into one
// bare-name namespace, last registration winning — so two bare `greet`s
// resolve to whichever module happens to be registered later, not to the one
// the file asked for. That flattening is a known, documented gap in that
// checker; the self-hosted compiler resolves per module. The corpus has to
// check clean under both, so it cannot contain the ambiguity.
def greet_io (name : String) : IO Unit {
  println name
}

// Traditional syntax for comparison
def say_goodbye : IO Unit := println "Goodbye!"

def main (args: List String) : IO Unit :=
  say_hello >>= fn _ =>
  greet_io "World" >>= fn _ =>
  say_goodbye
