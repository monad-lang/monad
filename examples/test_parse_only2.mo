def my_func : I64 := \x => x

def test_fn : I64 := \input =>
	match my_func input 1 {
		true => 1,
		false => 0
	}
