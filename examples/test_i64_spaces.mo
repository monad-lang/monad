def one_param (x : I64) : Bool :=
  match x {
    42 => true,
    _ => false
  }

@[test]
def test_42 : Bool := one_param 42
