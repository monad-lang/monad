def test_fn : I64 -> I64 := \input =>
	match String.length input {
		true => 1,
		false => 0
	}
