// IO module

// TODO make into indexed monad
type IO A {
 io A
}

instance Monad IO {
  def pure (a : A) : IO A :=
    IO.io a
  def bind (a : IO A) (f : A -> IO B) : IO B :=
    match a {
      io a => f a
    }
}

@[native print_str]
def IO.println (s: String) : IO Unit

@[native "write_file"]
def IO.write_file (path : String) (content : String) : IO Unit

@[native "read_file"]
def IO.read_file (path : String) : IO String

@[native "file_exists"]
def IO.file_exists (path : String) : IO Bool

@[native "get_env"]
def IO.get_env (s : String) : IO (Option String)


// TODO support constraints
// def IO.println [ToString A] (a: A) : IO Unit :=
//   IO.println_raw (ToString.to_string a)
