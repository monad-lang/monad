use init.parser
open init.parser.ParseResult

def list_is_empty (l : List A) : Bool :=
	match l {
		empty => true,
		cons _ _ => false
	}

@[test]
def test_empty : Bool := list_is_empty List.empty
