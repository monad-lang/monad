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
def test_to_string_with_annotates_elements : Bool :=
    let node :=
        Html.Node.node_element "div" List.empty
            (List.cons (Html.Node.node_element "span" List.empty
                (List.cons (Html.Node.node_text "hi") List.empty)) List.empty) in
    let opts : Html.RenderOpts := { charset := false, annotate := true } in
    String.beq (Html.to_string_with opts node)
        "<div data-oak=\"0\"><span data-oak=\"0.0\">hi</span></div>"

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
