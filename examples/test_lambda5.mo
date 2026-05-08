/// Test match with let-bound scrutinee after lambda
def test_fn5 : I64 := \input =>
	let x := String.length input
	match x {
		5 => 1,
		_ => 0
	}

@[test]
def test_simple : Bool := true
