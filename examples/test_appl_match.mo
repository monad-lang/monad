def test_fn : I64 -> I64 := \input =>
	match I64.add input 1 {
		5 => 1,
		_ => 0
	}

@[test]
def test_dummy : Bool := true
