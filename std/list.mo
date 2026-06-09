// Standard library: List operations and instances not covered in init/
//
// Provides:
//   - Show class and instances (String, I64, Bool)
//   - Show (List A) instance — element-wise, uses runtime type dispatch
//   - Append (List A) instance
//   - BEq (List A) instance — full element-wise equality
//   - List.length, List.filter, List.sum
//   - list_show helper (explicit show function, for concrete call sites)

class Show A {
    def show : A -> String
}

instance Show String {
    def show (s: String) : String := s
}

instance Show I64 {
    def show (n: I64) : String := I64.to_string n
}

instance Show Bool {
    def show (b: Bool) : String :=
        if b then "true" else "false"
}

// list_show helper for explicit show functions (concrete call-site bypass)
def list_show (show_elem : A -> String) (xs : List A) : String :=
    match xs {
        empty => "[]",
        cons a tail =>
            let body := show_body show_elem tail in
            "[" ++ show_elem a ++ body ++ "]",
        _ => "[]"
    }

def show_body (show_elem : A -> String) (xs : List A) : String :=
    match xs {
        empty => "",
        cons a tail =>
            let rest : String := show_body show_elem tail in
            ", " ++ show_elem a ++ rest,
        _ => ""
    }

// Element-wise Show (List A) - dispatches via runtime type inference
instance [Show A] Show (List A) {
    def show (xs: List A) : String :=
        list_show (fn a => Show.show a) xs
}

// Element-wise BEq (List A) - dispatches via runtime type inference
instance [BEq A] BEq (List A) {
    def beq (xs ys : List A) : Bool :=
        match xs {
            empty => match ys {
                empty => true,
                cons _ _ => false,
                _ => false
            },
            cons x x_tail => match ys {
                empty => false,
                cons y y_tail =>
                    (x == y) && (BEq.beq x_tail y_tail),
                _ => false
            },
            _ => false
        }
}
instance {A : Type} Append (List A) {
    def append (a b : List A) : List A := List.append a b
}

def List.length {A : Type} (xs : List A) : I64 :=
    match xs {
        empty => 0,
        cons _ tail => 1 + List.length tail,
        _ => 0
    }

def List.filter {A : Type} (pred : A -> Bool) (xs : List A) : List A :=
    match xs {
        empty => List.empty,
        cons a tail =>
            if pred a
            then List.cons a (List.filter pred tail)
            else List.filter pred tail,
        _ => List.empty
    }

// TODO Fix instance resolution over constraint
// def List.contains [BEq A] {A : Type} (a : A) (xs : List A) : Bool :=
//     List.any (fn x => a == x) xs

def List.any {A : Type} (pred : A -> Bool) (xs : List A) : Bool :=
    match xs {
        empty => false,
        cons a tail =>
            if pred a
            then true
            else List.any pred tail,
        _ => false
    }

def List.all {A : Type} (pred : A -> Bool) (xs : List A) : Bool :=
    match xs {
        empty => true,
        cons a tail =>
            if pred a
            then List.all pred tail
            else false,
        _ => true
    }

def List.sum (xs : List I64) : I64 :=
    match xs {
        empty => 0,
        cons a tail => a + List.sum tail,
        _ => 0
    }

@[test]
def test_length : Bool :=
    [1, 2, 3, 4]
        |> List.length
        |> BEq.beq 4

@[test]
def test_sum : Bool :=
    [1, 2, 3, 4]
        |> List.sum
        |> BEq.beq 10
    
@[test]
def test_contains : Bool :=
    ["a", "b", "c"]
        // |> List.contains "c" // TODO fix instance resolution
        |> List.any (fn a => a == "c")

@[test]
def test_not_contains : Bool :=
    ["a", "b", "c"]
        |> List.all (fn a => not (a == "d"))
