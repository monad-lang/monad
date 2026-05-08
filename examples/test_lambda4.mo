/// Test match with simple identifier as scrutinee after lambda
def test_fn4 : I64 := \input =>
	match input {
		true => 1,
		false => 0
	}

@[test]
def test_simple : Bool := true
