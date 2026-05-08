def apply_to_42 (f : I64 -> I64) : I64 :=
	match f 42 {
		42 => 1,
		_ => 0
	}

@[test]
def test_dummy : Bool := true
