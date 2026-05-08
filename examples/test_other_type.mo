type MyInt { mk Int }

def one_param (x : MyInt) : Bool :=
  match x {
    mk 42 => true,
    _ => false
  }

@[test]
def test_42 : Bool := one_param (mk 42)
