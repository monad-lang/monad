#![mote { name := "hello", deps := [init] }]

// The smallest thing a Windows build must get right: `IO.println` goes through
// `monad_print_str` (the CRT's text mode, so `\n` becomes `\r\n`) and `main`
// receives only its own extra arguments.
open IO {println}

def main (args : List String) : IO Unit :=
    match args {
        List.empty => println "hello from windows",
        List.cons first _ => println first,
    }
