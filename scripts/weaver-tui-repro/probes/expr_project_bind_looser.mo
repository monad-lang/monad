struct S { scroll : I64 }

def mk : S := { scroll := 1 }

#[test]
def test_proj : Bool :=
    (mk).scroll == 1
