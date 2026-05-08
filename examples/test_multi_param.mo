def mymatch (x : I64) (y : I64) : Bool :=
	match x {
		42 => true,
		_ => false
	}

@[test]
def test_42 : Bool := mymatch 42 0

@[test]
def test_0 : Bool := Bool.not (mymatch 0 0)
