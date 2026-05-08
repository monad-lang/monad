def one_param (x : I32) : Bool :=
  match x {
    true => true,
    false => false
  }

@[test]
def test_true : Bool := one_param true
