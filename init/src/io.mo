// IO module -- the pure, portable `IO` monad wrapper itself. All
// OS-specific native operations (println, file I/O, ...) live in
// std/io.mo instead -- see AGENTS.md's "init vs std" section.

// RawIO is the opaque low-level IO type. Its `io` constructor exists for
// the Rust runtime (which needs the tag to build `Value::Con` internally)
// but is never named in `.mo` source. Values are created via
// `RawIO.pure` (a native) and consumed via `RawIO.bind` (a native).
pub type RawIO A {
    io A
}

/// Construct a `RawIO` value wrapping a pure value.
#[native "io_pure"]
pub def RawIO.pure (a : A) : RawIO A

/// Unwrap a `RawIO` value and apply a continuation.
#[native "io_bind"]
pub def RawIO.bind (a : RawIO A) (f : A -> RawIO B) : RawIO B

pub instance Monad RawIO {
  def pure (a : A) : RawIO A :=
    RawIO.pure a
  def bind (a : RawIO A) (f : A -> RawIO B) : RawIO B :=
    RawIO.bind a f
}

/// IO is the user-facing IO type. It wraps `RawIO` and can be extended
/// with state, exceptions, and other capabilities. Today it is a thin
/// wrapper that delegates to `RawIO`.
pub type IO A {
    mk (raw : RawIO A)
}

/// Construct an `IO` value from a pure value.
pub def IO.pure (a : A) : IO A :=
    IO.mk (RawIO.pure a)

/// Unwrap an `IO` value and apply a continuation.
def IO.bind (a : IO A) (f : A -> IO B) : IO B :=
    match a {
        IO.mk raw => IO.mk (RawIO.bind raw (fn x => match f x { IO.mk r => r }))
    }

pub instance Monad IO {
  def pure (a : A) : IO A :=
    IO.pure a
  def bind (a : IO A) (f : A -> IO B) : IO B :=
    IO.bind a f
}

// TODO support constraints
// def IO.fprintln [ToString A] (a: A) : IO Unit :=
//   IO.println (ToString.to_string a)
