use io {IO, println}
open IO {println}

def say_hello (s : String) : IO Unit := println s

def main (args: List String) : IO Unit :=
  args
    |> List.last
    |> (Option.get_or_default "no arguments")
    |> say_hello
