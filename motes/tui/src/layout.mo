// Terminal UI Library - Layout
//
// Divides a `Rect` among children according to `LayoutSize` constraints
// (defined in `core.mo`). v1 supports `fixed n` (exact reservation) and
// `fill w` (weighted share of the leftover space, distributed so the last
// fill absorbs integer-division remainder). `min n` is treated as a fixed
// reservation of `n`; `max n` is treated as `fill` with weight 1 (the cap
// is not enforced in this v1 — the design doc leaves the full algorithm as
// `…`, and these two simplifications are documented here, not silently
// assumed). No native bindings, no I/O — pure layout math.

use lib::types { Rect, LayoutSize }
use lib::core { mk_rect, clamp }

/// Sum of the space reserved by `fixed`/`min` sizes — the part of `total`
/// that is NOT available for `fill`/`max` distribution.
#[terminating]
def layout_reserved (sizes : List LayoutSize) : I64 :=
    match sizes {
        empty => 0,
        cons s rest =>
            let here := match s { fixed n => n, min n => n, _ => 0 } in
            here + layout_reserved rest
    }

/// Total weight of the flexible sizes: `fill w` contributes `w`, `max n`
/// contributes `1` (v1 treats `max` as a weight-1 fill).
#[terminating]
def layout_fill_weight (sizes : List LayoutSize) : I64 :=
    match sizes {
        empty => 0,
        cons s rest =>
            let here := match s { fill w => w, max _ => 1, _ => 0 } in
            here + layout_fill_weight rest
    }

/// One flexible (`fill`/`max`) step of `layout_walk`, for a size of `weight`:
/// take this size's cumulative share of `remaining`, hand the rest of the walk
/// the new cumulative totals, and prepend the length. Shared by both flexible
/// arms so the proportional-distribution arithmetic exists exactly once.
#[terminating]
def layout_walk_flex
        (rest : List LayoutSize) (remaining : I64) (total_weight : I64)
        (fill_allocated : I64) (cum_weight : I64) (weight : I64) : List I64 :=
    let next_cum := cum_weight + weight in
    let target := if total_weight < 1 then 0 else I64.div (I64.mul remaining next_cum) total_weight in
    List.cons (target - fill_allocated) (layout_walk rest remaining total_weight target next_cum)

/// Walk `sizes` and return the length each child gets along the split axis.
/// `remaining` is the space left after reserved sizes; `total_weight` is
/// `layout_fill_weight`. The cumulative-weight trick (`target - allocated`)
/// distributes `remaining` across `fill`/`max` proportionally and leaves any
/// integer-division remainder on the LAST flexible size, so the lengths
/// always sum to `reserved + remaining` (= `total` when `reserved <= total`).
#[terminating]
def layout_walk
        (sizes : List LayoutSize) (remaining : I64) (total_weight : I64)
        (fill_allocated : I64) (cum_weight : I64) : List I64 :=
    match sizes {
        empty => List.empty,
        cons s rest =>
            match s {
                fixed n =>
                    List.cons n (layout_walk rest remaining total_weight fill_allocated cum_weight),
                min n =>
                    List.cons n (layout_walk rest remaining total_weight fill_allocated cum_weight),
                fill w => layout_walk_flex rest remaining total_weight fill_allocated cum_weight w,
                // v1 treats `max` as a weight-1 fill (the cap is not enforced).
                max _ => layout_walk_flex rest remaining total_weight fill_allocated cum_weight 1
            }
    }

/// Turn a list of widths (one per child) into a list of `Rect`s laid out
/// left-to-right inside `area`.
#[terminating]
def layout_rects_x (widths : List I64) (offset : I64) (y : I64) (height : I64) : List Rect :=
    match widths {
        empty => List.empty,
        cons w rest => List.cons (mk_rect offset y w height) (layout_rects_x rest (offset + w) y height)
    }

/// Turn a list of heights (one per child) into a list of `Rect`s laid out
/// top-to-bottom inside `area`.
#[terminating]
def layout_rects_y (heights : List I64) (offset : I64) (x : I64) (width : I64) : List Rect :=
    match heights {
        empty => List.empty,
        cons h rest => List.cons (mk_rect x offset width h) (layout_rects_y rest (offset + h) x width)
    }

/// Split `area` horizontally: each child gets a vertical strip whose width is
/// determined by its `LayoutSize`. Children tile left-to-right.
pub def layout_row (area : Rect) (sizes : List LayoutSize) : List Rect :=
    let reserved := layout_reserved sizes in
    let weight := layout_fill_weight sizes in
    let remaining := clamp (area.width - reserved) 0 area.width in
    let widths := layout_walk sizes remaining weight 0 0 in
    layout_rects_x widths area.x area.y area.height

/// Split `area` vertically: each child gets a horizontal strip whose height
/// is determined by its `LayoutSize`. Children tile top-to-bottom.
pub def layout_column (area : Rect) (sizes : List LayoutSize) : List Rect :=
    let reserved := layout_reserved sizes in
    let weight := layout_fill_weight sizes in
    let remaining := clamp (area.height - reserved) 0 area.height in
    let heights := layout_walk sizes remaining weight 0 0 in
    layout_rects_y heights area.x area.y area.width

/// Shrink `rect` by the given insets on each side. The result is always
/// inside `rect`: dimensions clamp at 0 so heavy padding cannot go negative,
/// and the origin clamps at the far edge so it cannot step past it either --
/// padding a 5x5 rect by 10 gives an empty rect at its corner, not one whose
/// origin is outside the input.
pub def pad_rect (rect : Rect) (left : I64) (top : I64) (right : I64) (bottom : I64) : Rect :=
    mk_rect (rect.x + clamp left 0 rect.width) (rect.y + clamp top 0 rect.height)
        (clamp (rect.width - left - right) 0 rect.width)
        (clamp (rect.height - top - bottom) 0 rect.height)

/// A `w`x`h` rectangle centered inside `area`.
pub def center_rect_in (area : Rect) (w : I64) (h : I64) : Rect :=
    let dx := I64.div (clamp (area.width - w) 0 area.width) 2 in
    let dy := I64.div (clamp (area.height - h) 0 area.height) 2 in
    mk_rect (area.x + dx) (area.y + dy) w h

// ==================== Tests ====================

#[test]
def test_layout_row_fixed_then_two_equal_fills : Bool :=
    let rects := layout_row (mk_rect 0 0 100 10) [LayoutSize.fixed 10, LayoutSize.fill 1, LayoutSize.fill 1] in
    // exactly three children
    (match List.get 3 rects { some _ => false, none => true })
    && (match List.get 0 rects { some r => r == mk_rect 0 0 10 10, none => false })
    && (match List.get 1 rects { some r => r == mk_rect 10 0 45 10, none => false })
    && (match List.get 2 rects { some r => r == mk_rect 55 0 45 10, none => false })

#[test]
def test_layout_row_remainder_on_last : Bool :=
    let rects := layout_row (mk_rect 0 0 101 8) [LayoutSize.fixed 10, LayoutSize.fill 1, LayoutSize.fill 1] in
    let r1 := match List.get 1 rects { some r => r, none => mk_rect 0 0 0 0 } in
    let r2 := match List.get 2 rects { some r => r, none => mk_rect 0 0 0 0 } in
    // 101-10=91; 91/2=45 each by floor; remainder 1 lands on the last fill -> 45 + 46
    r1 == mk_rect 10 0 45 8 && r2 == mk_rect 55 0 46 8

#[test]
def test_layout_row_weighted_fills : Bool :=
    // fixed 0, fill 1 : fill 3 over 80 -> 20 + 60
    let rects := layout_row (mk_rect 0 0 80 5) [LayoutSize.fill 1, LayoutSize.fill 3] in
    (match List.get 0 rects { some r => r == mk_rect 0 0 20 5, none => false })
    && (match List.get 1 rects { some r => r == mk_rect 20 0 60 5, none => false })

#[test]
def test_layout_column_splits_vertically : Bool :=
    let rects := layout_column (mk_rect 0 0 30 50) [LayoutSize.fixed 10, LayoutSize.fill 1, LayoutSize.fill 1] in
    (match List.get 0 rects { some r => r == mk_rect 0 0 30 10, none => false })
    && (match List.get 1 rects { some r => r == mk_rect 0 10 30 20, none => false })
    && (match List.get 2 rects { some r => r == mk_rect 0 30 30 20, none => false })

#[test]
def test_layout_row_preserves_origin : Bool :=
    let rects := layout_row (mk_rect 5 7 100 10) [LayoutSize.fill 1, LayoutSize.fill 1] in
    (match List.get 0 rects { some r => r == mk_rect 5 7 50 10, none => false })
    && (match List.get 1 rects { some r => r == mk_rect 55 7 50 10, none => false })

#[test]
def test_layout_row_empty_sizes_is_empty : Bool :=
    match layout_row (mk_rect 0 0 100 10) ([] : List LayoutSize) {
        empty => true,
        _ => false
    }

#[test]
def test_layout_min_treated_as_fixed : Bool :=
    let rects := layout_row (mk_rect 0 0 100 10) [LayoutSize.min 20, LayoutSize.fill 1] in
    // min 20 reserves 20; 80 left for the fill
    (match List.get 0 rects { some r => r == mk_rect 0 0 20 10, none => false })
    && (match List.get 1 rects { some r => r == mk_rect 20 0 80 10, none => false })

#[test]
def test_pad_rect_shrinks_by_insets : Bool :=
    pad_rect (mk_rect 10 10 20 20) 1 2 3 4 == mk_rect 11 12 16 14

#[test]
def test_pad_rect_clamps_at_zero : Bool :=
    pad_rect (mk_rect 0 0 5 5) 10 10 10 10 == mk_rect 5 5 0 0

#[test]
def test_pad_rect_keeps_origin_inside : Bool :=
    // Insets past the far edge collapse onto it rather than stepping over.
    let r := pad_rect (mk_rect 10 20 4 6) 99 99 0 0 in
    r == mk_rect 14 26 0 0

#[test]
def test_center_rect_in_centers : Bool :=
    // 4x2 centered in 10x10 -> x=(10-4)/2=3, y=(10-2)/2=4
    center_rect_in (mk_rect 0 0 10 10) 4 2 == mk_rect 3 4 4 2

#[test]
def test_center_rect_in_origin_offset : Bool :=
    center_rect_in (mk_rect 100 200 10 10) 4 2 == mk_rect 103 204 4 2
