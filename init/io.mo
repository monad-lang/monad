// IO module

type IO A {
 io A
}


instance Monad IO {
  def pure (a: A) : IO A :=
    IO.io a
  def bind (a : IO A) (f : A -> IO B) : IO B :=
    match a {
      io a => f a
    }
}

@[native println]
def IO.println (s: String) : IO Unit

// TODO support constraints
// def IO.println [ToString A] (a: A) : IO Unit :=
//   IO.println_raw (ToString.to_string a)

