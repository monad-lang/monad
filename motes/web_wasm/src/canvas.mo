/// Canvas sizing. A canvas has two sizes: its CSS layout size
/// (`clientWidth`/`clientHeight`) and its drawing-buffer size (the `width`/
/// `height` attributes). Sharp rendering needs the drawing buffer to be the
/// layout size times `devicePixelRatio`; `Canvas.fit` makes it so.
///
/// An oak view that calls `fit` should not also set `width`/`height` in its
/// attributes: the next patch would put the view's numbers back.

use lib::types {Node}
use lib::ffi {canvas_fit_raw, dom_metric_raw}

/// The layout size in CSS pixels.
pub def Canvas.client_size (canvas : Node) : IO (Pair F64 F64) := do {
    let w <- IO.mk (dom_metric_raw canvas 0);
    let h <- IO.mk (dom_metric_raw canvas 1);
    IO.pure (Pair.pair w h)
}

/// The drawing-buffer size (`canvas.width`, `canvas.height`).
pub def Canvas.buffer_size (canvas : Node) : IO (Pair F64 F64) := do {
    let w <- IO.mk (dom_metric_raw canvas 3);
    let h <- IO.mk (dom_metric_raw canvas 4);
    IO.pure (Pair.pair w h)
}

/// Resize the drawing buffer to `round(client size × devicePixelRatio)`
/// (at least 1×1). True when the size changed, so the caller knows to
/// update its viewport and projection.
pub def Canvas.fit (canvas : Node) : IO Bool := do {
    let changed <- IO.mk (canvas_fit_raw canvas);
    IO.pure (I64.beq changed 1)
}

/// `window.devicePixelRatio` (1.0 when the host has none). It takes the
/// canvas only because the metric import is node-addressed; the ratio is
/// the window's.
pub def Canvas.pixel_ratio (canvas : Node) : IO F64 := IO.mk (dom_metric_raw canvas 2)
