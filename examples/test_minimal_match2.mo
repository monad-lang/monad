def mymatch (l : List A) : Bool :=
  match l {
    empty => true,
    cons h t => false
  }

@[test]
def test_match : Bool := mymatch List.empty
