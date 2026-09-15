// IO module -- the pure, portable `IO` monad wrapper itself. All
// OS-specific native operations (println, file I/O, ...) live in
// std/io.mo instead -- see AGENTS.md's "init vs std" section.

// TODO make into indexed monad
type IO A {
 io A
}

/// IO construction wrapper — the public API for creating IO values.
/// Call sites use `IO.pure` instead of `IO.io` directly, so the
/// constructor can eventually be hidden without touching every use
/// site. Currently just wraps `IO.io`; will become a native once the
/// self-hosted codegen supports it.
def IO.pure (a : A) : IO A :=
    IO.io a

instance Monad IO {
  def pure (a : A) : IO A :=
    IO.pure a
  def bind (a : IO A) (f : A -> IO B) : IO B :=
    match a {
      io a => f a
    }
}

// TODO support constraints
// def IO.fprintln [ToString A] (a: A) : IO Unit :=
//   IO.println (ToString.to_string a)
