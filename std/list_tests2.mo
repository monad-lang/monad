use std.list {list_show}

def double (x : I64) : I64 := x * 2

// Map + Pipe tests

#[test]
def test_map_pipe : Bool :=
    let xs : List I64 := [1, 2, 3] in
    let doubled : List I64 := xs |> List.map double in
    list_show I64.to_string doubled == "[2, 4, 6]"

#[test]
def test_map_pipe_chain : Bool :=
    let xs : List I64 := [1, 2, 3] in
    let result : List I64 := xs |> List.map double |> List.map double in
    list_show I64.to_string result == "[4, 8, 12]"

#[test]
def test_map_pipe_single : Bool :=
    let xs : List I64 := [5] in
    let doubled : List I64 := xs |> List.map double in
    list_show I64.to_string doubled == "[10]"

#[test]
def test_map_pipe_empty : Bool :=
    let xs : List I64 := [] in
    let doubled : List I64 := xs |> List.map double in
    list_show I64.to_string doubled == "[]"

// BEq tests - element-wise equality

#[test]
def test_list_beq_empty : Bool :=
    BEq.beq ([] : List I64) ([] : List I64)

#[test]
def test_list_beq_same : Bool :=
    BEq.beq [1, 2, 3] [1, 2, 3]

#[test]
def test_list_beq_diff_elements : Bool :=
    Bool.not (BEq.beq [1, 2, 3] [4, 5, 6])

#[test]
def test_list_beq_diff_length : Bool :=
    Bool.not (BEq.beq [1, 2] [1, 2, 3])

#[test]
def test_list_beq_singleton_same : Bool :=
    BEq.beq [42] [42]

#[test]
def test_list_beq_singleton_diff : Bool :=
    Bool.not (BEq.beq [42] [99])

#[test]
def test_list_beq_prefix_match : Bool :=
    Bool.not (BEq.beq [1, 2, 3] [1, 2, 4])

// Append tests

#[test]
def test_list_append : Bool :=
    let xs : List I64 := [1, 2] in
    let ys : List I64 := [3, 4] in
    let zs : List I64 := [1, 2, 3, 4] in
    BEq.beq (xs ++ ys) zs

#[test]
def test_list_append_empty_left : Bool :=
    let xs : List I64 := [] in
    let ys : List I64 := [1, 2] in
    BEq.beq (xs ++ ys) ys
