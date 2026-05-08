def one_param (x : List Bool) : Bool :=
  match x {
    empty => true,
    cons h t => false
  }

@[test]
def test_empty : Bool := one_param List.empty
