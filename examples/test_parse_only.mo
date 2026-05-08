def test_fn : I64 := \input =>
	match I64.add input 1 {
		true => 1,
		false => 0
	}
