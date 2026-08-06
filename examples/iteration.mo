
def double (x : I64) : I64 := x * 2

def to_string (x : I64) : String := I64.to_string x

#[test]
def test_map : Bool :=
  let list := ([1, 2, 3, 4] : List I64) in
  let doubled : List I64 := List.map double list in
  match doubled {
    cons h t => h == 2,
    empty => false
  }

#[test]
def test_map_pipe : Bool :=
  let list := ([1, 2, 3, 4] : List I64) in
  let doubled : List I64 := list |> List.map double in
  let strings : List String := doubled |> List.map to_string in
  match strings {
    cons h t => h == "2",
    empty => false
  }

#[test]
def test_map_all : Bool :=
  let list := ([1, 2, 3] : List I64) in
  let doubled : List I64 := List.map double list in
  match doubled {
    cons h t =>
      h == 2 && match t {
        cons h2 t2 =>
          h2 == 4 && match t2 {
            cons h3 empty => h3 == 6,
            empty => false
          },
        empty => false
      },
    empty => false
  }
