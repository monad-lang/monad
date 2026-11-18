// Exact-string goldens for the SVG builders: an SVG element serializes as an
// ordinary element, numbers render as integers, and the composite attributes
// (`viewBox`, `translate`, `marker-end`) keep their exact spelling.

use lib::svg {
    Svg.svg, Svg.g, Svg.path, Svg.rect, Svg.text_, Svg.title, Svg.defs, Svg.marker,
    Svg.view_box, Svg.d, Svg.x, Svg.y, Svg.width, Svg.height, Svg.rx,
    Svg.translate, Svg.fill, Svg.stroke, Svg.stroke_width, Svg.marker_end,
    Svg.text_anchor, Svg.points, Svg.polyline
}
use lib::elements {Html.text}
use lib::typed {Oak.Node, Oak.to_html}
use xml_html::html {Html.to_string}

def svg_renders (n : Oak.Node Unit) (want : String) : Bool :=
    String.beq (Html.to_string (Oak.to_html n)) want

#[test]
def test_svg_root_view_box : Bool :=
    svg_renders (Svg.svg [Svg.view_box 0 (0 - 10) 200 100] List.empty)
        "<svg viewBox=\"0 -10 200 100\"></svg>"

#[test]
def test_rect_attrs : Bool :=
    svg_renders (Svg.rect [Svg.x 1, Svg.y 2, Svg.width 30, Svg.height 40, Svg.rx 4] List.empty)
        "<rect x=\"1\" y=\"2\" width=\"30\" height=\"40\" rx=\"4\"></rect>"

#[test]
def test_group_translate : Bool :=
    svg_renders (Svg.g [Svg.translate 5 (0 - 7)] List.empty)
        "<g transform=\"translate(5 -7)\"></g>"

#[test]
def test_path_marker_end : Bool :=
    svg_renders (Svg.path [Svg.d "M 0 0 L 10 10", Svg.stroke "red", Svg.stroke_width 2, Svg.fill "none",
        Svg.marker_end "arrow"] List.empty)
        "<path d=\"M 0 0 L 10 10\" stroke=\"red\" stroke-width=\"2\" fill=\"none\" marker-end=\"url(#arrow)\"></path>"

#[test]
def test_text_and_title : Bool :=
    svg_renders (Svg.text_ [Svg.text_anchor "middle"] [Svg.title [Html.text "tip"], Html.text "a<b"])
        "<text text-anchor=\"middle\"><title>tip</title>a&lt;b</text>"

#[test]
def test_defs_marker : Bool :=
    svg_renders (Svg.defs [Svg.marker [Svg.width 6] List.empty])
        "<defs><marker width=\"6\"></marker></defs>"

#[test]
def test_polyline_points : Bool :=
    svg_renders (Svg.polyline [Svg.points [0, 0, 5, 10]] List.empty)
        "<polyline points=\"0 0 5 10\"></polyline>"
