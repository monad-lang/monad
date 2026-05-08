/// Test match with application in scrutinee
def test_fn2 (x : I64) : I64 := \input =>
	match I64.add input 1 {
		true => 1,
		false => 0
	}

@[test]
def test_simple : Bool := true
