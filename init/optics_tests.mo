use std.test {}
use init.optics {Lens, Prism, lens, mkPrism, over, over_prism, preview, review, set, set_prism, view}
open Lens {}
open Prism {mkPrism}

// Test structures

struct Point {
    x : I64,
    y : I64,
}

/// Getter for x field.
def get_x (pt : Point) : I64 :=
    match pt { mk x _ => x }

/// Setter for x field.
def set_x (new_x : I64) (pt : Point) : Point :=
    match pt { mk _ y => { x := new_x, y := y } }

/// Lens focusing on the x field of Point.
def x_lens : Lens Point I64 :=
    lens get_x set_x

/// Getter for y field.
def get_y (pt : Point) : I64 :=
    match pt { mk _ y => y }

/// Setter for y field.
def set_y (new_y : I64) (pt : Point) : Point :=
    match pt { mk x _ => { x := x, y := new_y } }

/// Lens focusing on the y field of Point.
def y_lens : Lens Point I64 :=
    lens get_y set_y

/// Helper: add 1 to I64.
def inc (x : I64) : I64 := x + 1

/// Helper: multiply I64 by 2.
def double (x : I64) : I64 := x * 2

// -- Lens tests --

#[test]
def test_lens_view : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    let x_val : I64 := view x_lens pt in
    x_val == 3

#[test]
def test_lens_view_y : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    let y_val : I64 := view y_lens pt in
    y_val == 5

#[test]
def test_lens_set : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    let pt2 : Point := set x_lens 10 pt in
    let x_val : I64 := view x_lens pt2 in
    let y_val : I64 := view y_lens pt2 in
    x_val == 10 && y_val == 5

#[test]
def test_lens_set_y : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    let pt2 : Point := set y_lens 20 pt in
    let x_val : I64 := view x_lens pt2 in
    let y_val : I64 := view y_lens pt2 in
    x_val == 3 && y_val == 20

#[test]
def test_lens_over : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    let pt2 : Point := over x_lens inc pt in
    let x_val : I64 := view x_lens pt2 in
    let y_val : I64 := view y_lens pt2 in
    x_val == 4 && y_val == 5

#[test]
def test_lens_over_y : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    let pt2 : Point := over y_lens double pt in
    let x_val : I64 := view x_lens pt2 in
    let y_val : I64 := view y_lens pt2 in
    x_val == 3 && y_val == 10

#[test]
def test_lens_set_idempotent : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    let pt2 : Point := set x_lens 10 pt in
    let pt3 : Point := set x_lens 10 pt2 in
    let x_val : I64 := view x_lens pt3 in
    x_val == 10

#[test]
def test_lens_over_compose : Bool :=
    let pt : Point := { x := 3, y := 5 } in
    let pt2 : Point := over x_lens inc pt in
    let pt3 : Point := over x_lens inc pt2 in
    let x_val : I64 := view x_lens pt3 in
    x_val == 5

// -- Prism definitions --

type Shape {
    circle (radius : F64),
    rectangle (w : F64) (h : F64),
}

open Shape {circle, rectangle}

/// Helper: preview for circle prism.
def preview_circle (s : Shape) : Option F64 :=
    match s {
        circle r => some r,
        rectangle _ _ => none
    }

def circle_prism : Prism Shape F64 :=
    Prism.mkPrism preview_circle (fn r => circle r)

/// Helper: preview for rectangle prism.
def preview_rectangle (s : Shape) : Option (Pair F64 F64) :=
    match s {
        circle _ => none,
        rectangle w h => some (Pair.pair w h)
    }

/// Helper: review for rectangle prism.
def review_rectangle (dims : Pair F64 F64) : Shape :=
    match dims {
        Pair.pair w h => rectangle w h
    }

def rectangle_prism : Prism Shape (Pair F64 F64) :=
    Prism.mkPrism preview_rectangle review_rectangle

/// Helper: multiply F64 by 2.0.
def double_f (x : F64) : F64 := x * 2.0

// -- Prism tests --

#[test]
def test_prism_preview_match : Bool :=
    let c : Shape := circle 3.0 in
    let val : Option F64 := preview circle_prism c in
    match val {
        none => false,
        some r => let r_val : F64 := r in r_val == 3.0
    }

#[test]
def test_prism_preview_nomatch : Bool :=
    let r : Shape := rectangle 2.0 4.0 in
    let val : Option F64 := preview circle_prism r in
    match val {
        none => true,
        some _ => false
    }

#[test]
def test_prism_review : Bool :=
    let c : Shape := review circle_prism 5.0 in
    let val : Option F64 := preview circle_prism c in
    match val {
        none => false,
        some r => let r_val : F64 := r in r_val == 5.0
    }

#[test]
def test_prism_over : Bool :=
    let c : Shape := circle 3.0 in
    let c2 : Shape := over_prism circle_prism double_f c in
    let val : Option F64 := preview circle_prism c2 in
    match val {
        none => false,
        some r => let r_val : F64 := r in r_val == 6.0
    }

#[test]
def test_prism_over_nomatch : Bool :=
    let r : Shape := rectangle 2.0 4.0 in
    let r2 : Shape := over_prism circle_prism double_f r in
    match r2 {
        circle _ => false,
        rectangle w h => let w_val : F64 := w in let h_val : F64 := h in w_val == 2.0 && h_val == 4.0
    }

#[test]
def test_prism_set : Bool :=
    let c : Shape := circle 3.0 in
    let c2 : Shape := set_prism circle_prism 7.0 c in
    let val : Option F64 := preview circle_prism c2 in
    match val {
        none => false,
        some r => let r_val : F64 := r in r_val == 7.0
    }

#[test]
def test_prism_rectangle_preview : Bool :=
    let r : Shape := rectangle 3.0 5.0 in
    let val : Option (Pair F64 F64) := preview rectangle_prism r in
    match val {
        none => false,
        some dims => match dims {
            Pair.pair w h => let w_val : F64 := w in let h_val : F64 := h in w_val == 3.0 && h_val == 5.0
        }
    }
