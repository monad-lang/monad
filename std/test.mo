// Test module

def Test.assert (condition : Bool) : Bool := condition

@[test]
def test_assert : Bool := Test.assert true

