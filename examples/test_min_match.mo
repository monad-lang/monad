def one_param (x : Bool) : Bool :=
  match x {
    true => true,
    false => false
  }

@[test]
def test_true : Bool := one_param true
