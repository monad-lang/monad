def mymatch (l : List A) : Bool :=
  match l {
    empty => true,
    cons h t => false
  }

@[test]
def test_empty : Bool := mymatch List.empty
