def test_fn3 : I64 := \input =>
	match String.length input {
		5 => 1,
		_ => 0
	}

@[test]
def test_simple : Bool := true
