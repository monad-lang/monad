use init

def factorial (n : I64) : I64 :=
match n with {
  zero => 1,
  succ pred => n * factorial pred
}

def main (args : List String) : I64 := factorial (succ (succ (succ (succ (succ zero)))))