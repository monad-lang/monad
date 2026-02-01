

def say_hello (s : String) : IO Unit := println s

def main (args: List String) : IO Unit :=
  args
    |> List.last
    |> (get_or_default "nothing")
    |> say_hello
