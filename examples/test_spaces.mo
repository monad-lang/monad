def one_param (x : I64) : Bool :=
  match x {
    42 => true,
    _ => false
  }

def two_params (x : I64) (y : I64) : Bool :=
  match x {
    42 => true,
    _ => false
  }

@[test]
def test_one : Bool := one_param 42

@[test]
def test_two : Bool := two_params 42 0
