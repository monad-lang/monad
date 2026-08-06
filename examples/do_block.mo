// TODO: `IO`/`println` are used below (via the companion `open IO
// {println}`, which is unaffected) but deliberately NOT listed in THIS
// `use` — naming anything here (even just `IO`) breaks `do`-notation's
// implicit `Monad IO` instance lookup at runtime ("instance-Monad-IO not
// found", despite type-checking succeeding). A pre-existing latent bug in
// how the default checker's instance/dictionary resolution interacts with
// non-empty `use {...}` filtering — same family as the `std.map`/
// `BTreeMap` TODOs elsewhere. `open`'s own explicit filtering is
// unaffected; only `use`'s is. Restore an explicit list once fixed.
use io {}
open IO {println}

// Do block syntax - simple expression
// Equivalent to: def say_hello : IO Unit := println "Hello from do block!"
def say_hello : IO Unit {
  println "Hello from do block!"
}

// Do block syntax - with parameters
// Equivalent to: def greet (name : String) : IO Unit := println name
def greet (name : String) : IO Unit {
  println name
}

// Traditional syntax for comparison
def say_goodbye : IO Unit := println "Goodbye!"

def main (args: List String) : IO Unit :=
  say_hello >>= fn _ =>
  greet "World" >>= fn _ =>
  say_goodbye
