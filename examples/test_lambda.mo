/// Test lambda with match
def test_fn (x : I64) : I64 := \input =>
  match input {
    true => 1,
    false => 0
  }

@[test]
def test_lambda : Bool :=
  test_fn 42 true == 1
