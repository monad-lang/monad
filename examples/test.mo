use io
use init
use math
open IO

def factorial (n : I64) : I64 :=
    if n == 0
    then 1
    else n * factorial (n - 1)

def main (args : List String) : IO Unit :=
    println <| ToString.to_string (factorial 5)
