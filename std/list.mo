/// Standard library: List operations and instances not covered in init/
///
/// Provides:
///   - Show class and instances (String, I64, Bool)
///   - Show (List A) instance — element-wise, uses runtime type dispatch
///   - Append (List A) instance
///   - BEq (List A) instance — full element-wise equality
///   - List.length, List.filter, List.sum
///   - list_show helper (explicit show function, for concrete call sites)

use std.show {Show}


class Show A {
    def show : A -> String
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

#[test]
def test_length : Bool :=
    [1, 2, 3, 4]
        |> List.length
        |> BEq.beq 4

#[test]
def test_sum : Bool :=
    [1, 2, 3, 4]
        |> List.sum
        |> BEq.beq 10
    
// TODO fix instance resolution, then use `|> List.contains "c"` here instead.
#[test]
def test_contains : Bool :=
    ["a", "b", "c"]
        |> List.any (fn a => a == "c")

#[test]
def test_not_contains : Bool :=
    ["a", "b", "c"]
        |> List.all (fn a => not (a == "d"))

// --- Generic combinators the compiler (lang/*.mo) re-rolled ad hoc ---
//
// Each takes its predicate/equality/ordering as an EXPLICIT function
// argument rather than a `[BEq A]`-style constraint. That is deliberate,
// not a style choice: `List.contains [BEq A]` above is commented out
// because constraint-based instance resolution doesn't dispatch reliably
// at runtime inside deeply-recursive self-hosted code paths (see this
// file's own TODO, and AGENTS.md "Known Type Checker Issues" #3). An
// explicit function value works today, everywhere.

/// First element satisfying `pred`, or `Option.none`.
/// Replaces ~20 hand-rolled `find_*` loops across `lang/`.
def List.find_by {A : Type} (pred : A -> Bool) (xs : List A) : Option A :=
    match xs {
        List.empty => Option.none,
        List.cons a tail =>
            if pred a then Option.some a else List.find_by pred tail,
        _ => Option.none
    }

/// Map + keep only the `some`s, in one pass.
/// Replaces `Toml.filter_some` and ~11 collect/filter defs in `lang/scope.mo`.
def List.filter_map {A : Type} {B : Type} (f : A -> Option B) (xs : List A) : List B :=
    match xs {
        List.empty => List.empty,
        List.cons a tail =>
            match f a {
                Option.some b => List.cons b (List.filter_map f tail),
                Option.none => List.filter_map f tail,
            },
        _ => List.empty
    }

/// Membership using an explicit equality function.
/// Replaces `id_member`/`ident_in_list`/`list_contains`/`str_list_contains`/...
def List.contains_by {A : Type} (eq : A -> A -> Bool) (target : A) (xs : List A) : Bool :=
    List.any (fn x => eq target x) xs

/// Join string pieces with a separator between them.
/// Replaces 28 hand-rolled `*_rest` joiner pairs across 9 `lang/` files.
def List.intercalate (sep : String) (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons head tail => String.concat head (List.intercalate_rest sep tail),
        _ => ""
    }

def List.intercalate_rest (sep : String) (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons head tail =>
            String.concat (String.concat sep head) (List.intercalate_rest sep tail),
        _ => ""
    }

/// Drop later duplicates, keeping the first occurrence (left-biased).
/// Replaces `union_ids`/`dedup_idents`/`dedup_funcs_by_name`.
def List.dedup_by {A : Type} (eq : A -> A -> Bool) (xs : List A) : List A :=
    List.dedup_by_go eq xs List.empty

def List.dedup_by_go {A : Type} (eq : A -> A -> Bool) (xs : List A) (seen : List A) : List A :=
    match xs {
        List.empty => List.empty,
        List.cons a tail =>
            if List.contains_by eq a seen
            then List.dedup_by_go eq tail seen
            else List.cons a (List.dedup_by_go eq tail (List.cons a seen)),
        _ => List.empty
    }

#[test]
def test_find_by_found : Bool :=
    match List.find_by (fn x => I64.beq x 3) [1, 2, 3, 4] {
        Option.some v => I64.beq v 3,
        Option.none => false,
    }

#[test]
def test_find_by_missing : Bool :=
    match List.find_by (fn x => I64.beq x 9) [1, 2, 3] {
        Option.some _ => false,
        Option.none => true,
    }

#[test]
def test_filter_map : Bool :=
    List.filter_map (fn x => if I64.gt x 2 then Option.some x else Option.none) [1, 2, 3, 4]
        |> List.sum
        |> BEq.beq 7

#[test]
def test_contains_by : Bool :=
    List.contains_by String.beq "c" ["a", "b", "c"]

#[test]
def test_not_contains_by : Bool :=
    not (List.contains_by String.beq "d" ["a", "b", "c"])

#[test]
def test_intercalate : Bool :=
    String.beq (List.intercalate ", " ["a", "b", "c"]) "a, b, c"

#[test]
def test_intercalate_single : Bool :=
    String.beq (List.intercalate ", " ["a"]) "a"

#[test]
def test_intercalate_empty : Bool :=
    String.beq (List.intercalate ", " []) ""

#[test]
def test_dedup_by : Bool :=
    String.beq (List.intercalate "," (List.dedup_by String.beq ["a", "b", "a", "c", "b"])) "a,b,c"
