// Serializer and equality tests for the shared `Html.Node` type.
//
// These are the shared-core acceptance tests: Oak's builder tests reuse
// the exact strings pinned here. `renders` compares through
// `String.beq`; `Html.beq` is the hand-rolled element-wise walk (generic
// `BEq (List A)` dispatch is not relied on).
//
// Constructors referenced across modules go through the type
// (`Html.Node.node_text`, `Html.Attr.attr`); the `with Html` block only
// prefixes the type names, not the constructors.

use lib::html {
    Html.Attr, Html.Node, Html.RenderOpts, Html.beq, Html.default_opts,
    Html.to_string, Html.to_string_with,
}
use lib::html {}

def renders (n : Html.Node) (want : String) : Bool :=
    String.beq (Html.to_string n) want

// ─── Elements, void elements, fragments ───

#[test]
def test_text : Bool :=
    renders (Html.Node.node_text "hello") "hello"

#[test]
def test_element_no_attrs : Bool :=
    renders
        (Html.Node.node_element "div" List.empty [Html.Node.node_text "hi"])
        "<div>hi</div>"

#[test]
def test_element_attrs : Bool :=
    renders
        (Html.Node.node_element "a" [Html.Attr.attr "href" "/x"] [Html.Node.node_text "t"])
        "<a href=\"/x\">t</a>"

#[test]
def test_void_element : Bool :=
    renders (Html.Node.node_void "br" List.empty) "<br>"

#[test]
def test_void_element_with_bool_attr : Bool :=
    renders (Html.Node.node_void "input" [Html.Attr.bool_attr "disabled"]) "<input disabled>"

#[test]
def test_fragment : Bool :=
    renders
        (Html.Node.node_fragment
            [ Html.Node.node_text "a",
              Html.Node.node_element "span" List.empty [Html.Node.node_text "b"] ])
        "a<span>b</span>"

// ─── Escaping ───

#[test]
def test_text_escapes_markup : Bool :=
    renders (Html.Node.node_text "a & b < c > d") "a &amp; b &lt; c &gt; d"

#[test]
def test_attr_escapes_quotes_and_markup : Bool :=
    renders
        (Html.Node.node_element "a" [Html.Attr.attr "title" "x & y < z > \"q\""] List.empty)
        "<a title=\"x &amp; y &lt; z &gt; &quot;q&quot;\"></a>"

#[test]
def test_text_preserves_utf8 : Bool :=
    renders (Html.Node.node_text "héllo & 世界") "héllo &amp; 世界"

// ─── Raw text, comment, doctype ───

#[test]
def test_raw_text_is_not_escaped : Bool :=
    renders
        (Html.Node.node_raw_text "script" List.empty "if (a < b) {}")
        "<script>if (a < b) {}</script>"

#[test]
def test_raw_text_with_attrs : Bool :=
    renders
        (Html.Node.node_raw_text "script"
            (List.cons (Html.Attr.attr "type" "module")
                (List.cons (Html.Attr.attr "src" "/app.js") List.empty))
            "")
        "<script type=\"module\" src=\"/app.js\"></script>"

#[test]
def test_raw_html_is_verbatim : Bool :=
    renders
        (Html.Node.node_raw_html "<div class=\"note\">\n<p>hi</p>\n</div>")
        "<div class=\"note\">\n<p>hi</p>\n</div>"

#[test]
def test_raw_html_in_a_fragment : Bool :=
    renders
        (Html.Node.node_fragment
            [ Html.Node.node_text "a",
              Html.Node.node_raw_html "<b>",
              Html.Node.node_text "c" ])
        "a<b>c"

#[test]
def test_raw_html_is_not_annotated : Bool :=
    let node :=
        Html.Node.node_element "div" List.empty
            (List.cons (Html.Node.node_raw_html "<i>x</i>") List.empty) in
    let opts : Html.RenderOpts := { charset := false, annotate := true, xhtml_void := false } in
    String.beq (Html.to_string_with opts node)
        "<div data-oak=\"0\"><i>x</i></div>"

#[test]
def test_to_string_with_annotates_elements : Bool :=
    let node :=
        Html.Node.node_element "div" List.empty
            (List.cons (Html.Node.node_element "span" List.empty
                (List.cons (Html.Node.node_text "hi") List.empty)) List.empty) in
    let opts : Html.RenderOpts := { charset := false, annotate := true, xhtml_void := false } in
    String.beq (Html.to_string_with opts node)
        "<div data-oak=\"0\"><span data-oak=\"0.0\">hi</span></div>"

// ─── XHTML void spelling ───

#[test]
def test_xhtml_void_br : Bool :=
    let opts : Html.RenderOpts := { charset := false, annotate := false, xhtml_void := true } in
    String.beq (Html.to_string_with opts (Html.Node.node_void "br" List.empty)) "<br />"

#[test]
def test_xhtml_void_hr_and_attrs : Bool :=
    let opts : Html.RenderOpts := { charset := false, annotate := false, xhtml_void := true } in
    Bool.and
        (String.beq (Html.to_string_with opts (Html.Node.node_void "hr" List.empty)) "<hr />")
        (String.beq
            (Html.to_string_with opts
                (Html.Node.node_void "img"
                    [ Html.Attr.attr "src" "/x.png", Html.Attr.attr "alt" "x" ]))
            "<img src=\"/x.png\" alt=\"x\" />")

#[test]
def test_xhtml_void_default_is_html5 : Bool :=
    renders (Html.Node.node_void "hr" List.empty) "<hr>"

// ─── Linear serializer ───
//
// The old serializer was `concat child (siblings)`, which re-copied every
// remaining sibling per child: 100k flat siblings is ~5e9 character copies.

#[terminating]
def repeat_text (n : I64) (i : I64) (acc : List Html.Node) : List Html.Node :=
    if I64.beq i n
    then List.reverse acc
    else repeat_text n (I64.add i 1) (List.cons (Html.Node.node_text "x") acc)

#[test]
def test_flat_siblings_serialize_linearly : Bool :=
    let children := repeat_text 100000 0 List.empty in
    I64.beq (String.length (Html.to_string (Html.Node.node_fragment children))) 100000i64

#[test]
def test_to_string_with_default_matches : Bool :=
    let node :=
        Html.Node.node_element "p" List.empty
            (List.cons (Html.Node.node_text "x") List.empty) in
    String.beq (Html.to_string_with Html.default_opts node) (Html.to_string node)

#[test]
def test_comment : Bool :=
    renders (Html.Node.node_comment " note ") "<!-- note -->"

#[test]
def test_doctype : Bool :=
    renders (Html.Node.node_doctype "html") "<!DOCTYPE html>"

// ─── Equality ───

#[test]
def test_beq_structural : Bool :=
    Html.beq
        (Html.Node.node_element "div" [Html.Attr.attr "id" "x"] [Html.Node.node_text "hi"])
        (Html.Node.node_element "div" [Html.Attr.attr "id" "x"] [Html.Node.node_text "hi"])

#[test]
def test_beq_distinguishes : Bool :=
    Bool.not (Html.beq (Html.Node.node_text "a") (Html.Node.node_text "b"))
