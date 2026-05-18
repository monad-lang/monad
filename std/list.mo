// Standard library: List operations and instances not covered in init/
//
// Provides:
//   - Show class and instances (String, I64, Bool)
//   - Show (List A) instance (stub — element show blocked by BLOCKER #8)
//   - Append (List A) instance
//   - BEq (List A) instance (structural — element eq blocked by BLOCKER #8)
//   - List.length, List.filter, List.sum
//   - list_show helper (call with explicit show function, bypasses blocker)

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

// BLOCKER #8: Inside instance [Show A] Show (List A), calling Show.show on
// type variable A fails with "instance not found instance key for Show
// with args (A => A)". The constraint solver does not propagate instance-level
// constraints into method body resolution for type variables.
//
// Workaround: use the standalone list_show helper (below), passing
// Show.show explicitly from a concrete call site (not inside the instance).

def list_show (show_elem : A -> String) (xs : List A) : String :=
    match xs {
        empty => "[]",
        cons a tail =>
            let body := show_body show_elem tail in
            "[" ++ show_elem a ++ body ++ "]"
    }

def show_body (show_elem : A -> String) (xs : List A) : String :=
    match xs {
        empty => "",
        cons a tail =>
            let rest : String := show_body show_elem tail in
            ", " ++ show_elem a ++ rest
    }

instance [Show A] Show (List A) {
    def show (xs: List A) : String :=
        "[" ++ show_len xs ++ " element(s)]"
}

// Show the number of elements (stand-in until BLOCKER #8 is fixed)
def show_len {A : Type} (xs : List A) : String :=
    I64.to_string (List.length xs)

instance {A : Type} Append (List A) {
    def append (a b : List A) : List A := List.append a b
}

// BLOCKER #8: Same issue as Show — BEq.beq on type variable A inside the
// instance body cannot be resolved. The tail comparison (BEq.beq on List A)
// works, but element comparison does not.
//
// Current workaround: compare list structure (length + tail recursion) only.
// Full element-wise equality requires the constraint propagation fix.

instance [BEq A] BEq (List A) {
    def beq (xs ys : List A) : Bool :=
        match xs {
            empty => match ys {
                empty => true,
                cons _ _ => false
            },
            cons _ x_tail => match ys {
                empty => false,
                cons _ y_tail => BEq.beq x_tail y_tail
            }
        }
}

def List.length {A : Type} (xs : List A) : I64 :=
    match xs {
        empty => 0,
        cons _ tail => 1 + List.length tail
    }

def List.filter {A : Type} (pred : A -> Bool) (xs : List A) : List A :=
    match xs {
        empty => List.empty,
        cons a tail =>
            if pred a
            then List.cons a (List.filter pred tail)
            else List.filter pred tail
    }

def List.sum (xs : List I64) : I64 :=
    match xs {
        empty => 0,
        cons a tail => a + List.sum tail
    }
