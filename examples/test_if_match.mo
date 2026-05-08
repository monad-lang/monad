def test_fn : I64 -> I64 := \input =>
	if String.is_empty input
	then 0
	else
		match String.length input {
			5 => 1,
			_ => 2
		}

@[test]
def test_dummy : Bool := true
