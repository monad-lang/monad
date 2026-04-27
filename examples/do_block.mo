use io
open IO

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
