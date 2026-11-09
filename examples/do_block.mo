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

open IO {println}

// A one-field record for the unannotated-bind probes below.
struct Counter {
    count : I64,
}

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

// An UNANNOTATED bind, then a field read THROUGH its binder.
//
// Regression cover for `implementations/do-bind-binder-untyped.md`: `let q <- e`
// with no annotation used to leave `q` typed as a hole, so `q.count` -- which
// desugars to a bare `{ count, .. }` field pattern -- failed with "cannot
// resolve `{ .. }`: the matched value's type isn't known here". The read has to
// be through the binder AND on the binder's own type. Reading it through a
// named accessor def instead (`counter_count q`) does NOT discriminate and was
// tried first: `try_type_check_def_call` runs ahead of the hole-based path in
// `type_check_app` and checks the argument against the def's declared parameter
// type, so the binder gets a real type from there whatever the callee is.
// `IO.pure`/`Monad.bind` is a class method with no registered signature, so a
// real do-bind has no such rescue.
def count_through_bind (c : Counter) : IO I64 := do {
    let q <- IO.pure c;
    return q.count
}

// The annotated form the bug's workaround prescribed. Kept beside the above as
// the control: this one took `type_check_lam`'s correct branch all along, so it
// passed even with the defect.
def count_through_annotated_bind (c : Counter) : IO I64 := do {
    let q : Counter <- IO.pure c;
    return q.count
}

#[test]
def test_count_through_unannotated_bind : IO Bool := do {
    let c : Counter := { count := 7 };
    let n <- count_through_bind c;
    IO.pure (I64.beq n 7)
}

#[test]
def test_count_through_annotated_bind : IO Bool := do {
    let c : Counter := { count := 9 };
    let n <- count_through_annotated_bind c;
    IO.pure (I64.beq n 9)
}

def main (args : List String) : IO Unit :=
    say_hello >>= fn _ =>
    greet_io "World" >>= fn _ =>
    say_goodbye
