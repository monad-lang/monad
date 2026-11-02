/// The launch banner: a framed shuttle sweeping once across a warp, the
/// `w e a v e r` wordmark, and a tagline naming the provider and model. A
/// component -- `BannerModel`, `BannerMsg`, `Banner.update`, `Banner.view`
/// and `Banner.subscriptions` (the sweep's frames, until it ends). It
/// shows until the first submit.
use weaver::theme {theme_banner_style_with, BannerPart}
use tui::types {LayoutSize, TextStyle}
use tui::component {Subs}
use tui::widget {Widget, SizedWidget, label, sized, with_style}
use tui::text {Text.width}

pub struct BannerModel {
    shown : Bool,
    /// The sweep's frame: the shuttle moves one cell per frame.
    frame : I64,
}

pub type BannerMsg {
    tick,
    hide,
}

pub def Banner.shown : BannerModel :=
    let b : BannerModel := { shown := true, frame := 0 } in
    b

pub def Banner.hidden : BannerModel :=
    let b : BannerModel := { shown := false, frame := 0 } in
    b

/// The frames the sweep runs for.
pub def Banner.sweep_frames : I64 := 12

pub def Banner.update (b : BannerModel) (msg : BannerMsg) : BannerModel :=
    match msg {
        BannerMsg.tick => if Banner.animating b then { b with frame := b.frame + 1 } else b,
        BannerMsg.hide => { b with shown := false },
    }

pub def Banner.animating (b : BannerModel) : Bool :=
    Bool.and b.shown (b.frame < Banner.sweep_frames)

pub def Banner.subscriptions (b : BannerModel) : Subs BannerMsg :=
    if Banner.animating b then Subs.every 1 BannerMsg.tick else Subs.none

/// The rows the banner takes: four while shown.
pub def Banner.rows : I64 := 4

pub def Banner.height (b : BannerModel) : I64 :=
    if b.shown then Banner.rows else 0

pub struct BannerView {
    colors : Bool,
    cols : I64,
    provider : String,
    model : String,
}

def seg (style : TextStyle) (text : String) : SizedWidget :=
    sized (LayoutSize.fixed (Text.width text)) (with_style style (label text))

/// `w e a v e r`, each letter in a cyan -> blue -> magenta gradient.
#[partial]
def word_go (colors : Bool) (letters : List String) (i : I64) (acc : List SizedWidget) : List SizedWidget :=
    match letters {
        List.empty => List.reverse acc,
        List.cons l rest =>
            let part : BannerPart :=
                if i < 2 then BannerPart.word_cyan
                else if i < 4 then BannerPart.word_blue
                else BannerPart.word_magenta in
            // The separator belongs BETWEEN letters: in the reversed
            // accumulator it is pushed before the newer letter.
            let acc1 : List SizedWidget :=
                if i < 1 then acc
                else List.cons (seg (theme_banner_style_with colors BannerPart.warp) " ") acc in
            word_go colors rest (i + 1) (List.cons (seg (theme_banner_style_with colors part) l) acc1),
    }

def word (colors : Bool) : SizedWidget :=
    sized (LayoutSize.fixed 11) (Widget.row (word_go colors ["w", "e", "a", "v", "e", "r"] 0 List.empty))

/// The shuttle row: frame + 14-cell warp, the shuttle one cell further
/// right per frame, frame.
def art_mid (colors : Bool) (b : BannerModel) : List SizedWidget :=
    let frame := theme_banner_style_with colors BannerPart.frame in
    let warp := theme_banner_style_with colors BannerPart.warp in
    let shuttle := theme_banner_style_with colors BannerPart.shuttle in
    let p : I64 := if b.frame < 14 then b.frame else 13 in
    [
        seg frame "│ ",
        seg warp (String.repeat "─" p),
        seg shuttle "▸",
        seg warp (String.repeat "─" (13 - p)),
        seg frame " │",
    ]

pub def Banner.view (v : BannerView) (b : BannerModel) : Widget :=
    let colors : Bool := v.colors in
    let frame := theme_banner_style_with colors BannerPart.frame in
    let tagline : String := String.concat "coding agent · "
        (String.concat v.provider (String.concat "/" (String.concat v.model " · /help"))) in
    let tag_w : I64 := Text.width tagline in
    let right_w : I64 := if tag_w < 11 then 11 else tag_w in
    let room : I64 := v.cols - (18 + 3 + right_w) in
    let pad : I64 := if room < 1 then 0 else room / 2 in
    let top : String := String.concat "╭" (String.concat (String.repeat "─" 16) "╮") in
    let bot : String := String.concat "╰" (String.concat (String.repeat "─" 16) "╯") in
    let lead : SizedWidget := sized (LayoutSize.fixed pad) (label "") in
    let gap : SizedWidget := sized (LayoutSize.fixed 3) (label "") in
    let row0 : SizedWidget := sized (LayoutSize.fixed 1) (Widget.row [lead, seg frame top]) in
    let mid : List SizedWidget := List.append [lead] (List.append (art_mid colors b) [gap, word colors]) in
    let row1 : SizedWidget := sized (LayoutSize.fixed 1) (Widget.row mid) in
    let row2 : SizedWidget := sized (LayoutSize.fixed 1)
        (Widget.row [lead, seg frame bot, gap, seg (theme_banner_style_with colors BannerPart.tagline) tagline]) in
    let row3 : SizedWidget := sized (LayoutSize.fixed 1) (label "") in
    Widget.column [row0, row1, row2, row3]
