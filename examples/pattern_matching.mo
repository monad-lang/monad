
#[test]
def test_match_bool : Bool :=
  match true {
    true => true,
    false => false
  }

#[test]
def test_match_list_empty : Bool :=
  match List.empty {
    empty => true,
    cons h t => false
  }

#[test]
def test_match_list_nonempty : Bool :=
  match [1, 2, 3] {
    empty => false,
    cons h t => h == 1
  }

#[test]
def test_match_wildcard : Bool :=
  match [1, 2, 3] {
    empty => false,
    cons _ _ => true
  }

#[test]
def test_match_guard : Bool :=
  match [1, 2, 3] {
    empty => false,
    cons h t =>
      h == 1 && match t {
        empty => false,
        cons h2 _ => h2 == 2
      }
  }
