def test_fn (x : Bool) (y : I64) : I64 :=
	match x {
		true => 42,
		false =>
			match I64.add y 1 {
				10 => 100,
				_ => 200
			}
	}

@[test]
def test_true : Bool := I64.beq (test_fn true 0) 42

@[test]
def test_false9 : Bool := I64.beq (test_fn false 9) 200

@[test]
def test_false9b : Bool := I64.beq (test_fn false 9) 200

@[test]
def test_false_but_true : Bool :=
	match true {
		true => true,
		false => false
	}
