def my_fn (x : Bool) : Bool :=
  Bool.not x

@[test]
def test_true : Bool := my_fn false
