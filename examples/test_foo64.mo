type Foo64 { foo }

def one_param (x : Foo64) : Bool :=
  match x {
    foo => true
  }

@[test]
def test_foo : Bool := one_param foo
