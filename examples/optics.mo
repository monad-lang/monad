/// Optics Example — Lenses and Prisms in Monad
///
/// Demonstrates creating lenses for struct fields, using view/set/over,
/// and prisms for working with sum types.

use init.optics {Lens, Prism, lens, mkPrism, over, over_prism, preview, set, view}
open Lens {}
open Prism {mkPrism}

// --- Domain types ---

struct Address {
    street : String,
    city : String,
}

struct Person {
    name : String,
    age : I64,
    address : Address,
}

type Shape {
    circle (radius : F64),
    rectangle (w : F64) (h : F64),
}

open Shape {circle, rectangle}

// --- Lenses for Person ---

def get_name (p : Person) : String :=
    match p { mk name _ _ => name }

def set_name (n : String) (p : Person) : Person :=
    match p { mk _ age addr => { name := n, age := age, address := addr } }

def name_lens : Lens Person String :=
    lens get_name set_name

def get_age (p : Person) : I64 :=
    match p { mk _ age _ => age }

def set_age (a : I64) (p : Person) : Person :=
    match p { mk name _ addr => { name := name, age := a, address := addr } }

def age_lens : Lens Person I64 :=
    lens get_age set_age

def get_address (p : Person) : Address :=
    match p { mk _ _ addr => addr }

def set_address (a : Address) (p : Person) : Person :=
    match p { mk name age _ => { name := name, age := age, address := a } }

def address_lens : Lens Person Address :=
    lens get_address set_address

// --- Lenses for Address ---

def get_street (a : Address) : String :=
    match a { mk street _ => street }

def set_street (s : String) (a : Address) : Address :=
    match a { mk _ city => { street := s, city := city } }

def street_lens : Lens Address String :=
    lens get_street set_street

def get_city (a : Address) : String :=
    match a { mk _ city => city }

def set_city (c : String) (a : Address) : Address :=
    match a { mk street _ => { street := street, city := c } }

def city_lens : Lens Address String :=
    lens get_city set_city

// --- Prism for Shape ---

def shape_circle_preview (s : Shape) : Option F64 :=
    match s {
        circle r => some r,
        rectangle _ _ => none
    }

def circle_prism : Prism Shape F64 :=
    Prism.mkPrism shape_circle_preview (fn r => circle r)

def shape_rectangle_preview (s : Shape) : Option (Pair F64 F64) :=
    match s {
        circle _ => none,
        rectangle w h => some (Pair.pair w h)
    }

def shape_rectangle_review (dims : Pair F64 F64) : Shape :=
    match dims {
        Pair.pair w h => rectangle w h
    }

def rectangle_prism : Prism Shape (Pair F64 F64) :=
    Prism.mkPrism shape_rectangle_preview shape_rectangle_review

// --- Arithmetic helpers ---

def add_one (x : I64) : I64 := x + 1

def double_f (x : F64) : F64 := x * 2.0

// --- Tests ---

#[test]
def test_basic_lens_view : Bool :=
    let addr : Address := { street := "Main St", city := "Springfield" } in
    let p : Person := { name := "Alice", age := 30, address := addr } in
    let n_val : String := view name_lens p in
    n_val == "Alice"

#[test]
def test_basic_lens_set_age : Bool :=
    let addr : Address := { street := "Main St", city := "Springfield" } in
    let p : Person := { name := "Alice", age := 30, address := addr } in
    let p2 : Person := set age_lens 31 p in
    let a_val : I64 := view age_lens p2 in
    a_val == 31

#[test]
def test_lens_over_age_keeps_name : Bool :=
    let addr : Address := { street := "Main St", city := "Springfield" } in
    let p : Person := { name := "Alice", age := 30, address := addr } in
    let p2 : Person := over age_lens add_one p in
    let n_val : String := view name_lens p2 in
    let a_val : I64 := view age_lens p2 in
    n_val == "Alice" && a_val == 31

#[test]
def test_lens_chained_set : Bool :=
    let addr : Address := { street := "Main St", city := "Springfield" } in
    let p : Person := { name := "Alice", age := 30, address := addr } in
    let p2 : Person := set name_lens "Bob" p in
    let p3 : Person := set age_lens 25 p2 in
    let n_val : String := view name_lens p3 in
    let a_val : I64 := view age_lens p3 in
    n_val == "Bob" && a_val == 25

#[test]
def test_lens_nested_address_street : Bool :=
    let addr : Address := { street := "Main St", city := "Springfield" } in
    let p : Person := { name := "Alice", age := 30, address := addr } in
    let p_addr : Address := view address_lens p in
    let s_val : String := view street_lens p_addr in
    s_val == "Main St"

#[test]
def test_lens_nested_address_update : Bool :=
    let addr : Address := { street := "Main St", city := "Springfield" } in
    let p : Person := { name := "Alice", age := 30, address := addr } in
    let p_addr : Address := view address_lens p in
    let new_addr : Address := set street_lens "Oak Ave" p_addr in
    let p2 : Person := set address_lens new_addr p in
    let final_addr : Address := view address_lens p2 in
    let s_val : String := view street_lens final_addr in
    s_val == "Oak Ave"

#[test]
def test_prism_circle_double_radius : Bool :=
    let s : Shape := circle 5.0 in
    let s2 : Shape := over_prism circle_prism double_f s in
    let val : Option F64 := preview circle_prism s2 in
    match val {
        none => false,
        some r => let r_val : F64 := r in r_val == 10.0
    }

#[test]
def test_prism_rectangle_unchanged_by_circle_prism : Bool :=
    let s : Shape := rectangle 10.0 20.0 in
    let s2 : Shape := over_prism circle_prism double_f s in
    match s2 {
        circle _ => false,
        rectangle w h => let w_val : F64 := w in let h_val : F64 := h in w_val == 10.0 && h_val == 20.0
    }

#[test]
def test_prism_rectangle_preview_dimensions : Bool :=
    let s : Shape := rectangle 4.0 7.0 in
    let val : Option (Pair F64 F64) := preview rectangle_prism s in
    match val {
        none => false,
        some dims => match dims {
            Pair.pair w h => let w_val : F64 := w in let h_val : F64 := h in w_val == 4.0 && h_val == 7.0
        }
    }
