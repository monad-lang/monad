// Serializer and equality tests for the shared `Xml.Node` type.
//
// Constructors referenced across modules go through the type
// (`Xml.Node.node_text`, `Xml.Attr.attr`).

use lib::xml {Xml.Node, Xml.to_string, Xml.beq}
use lib::xml {}

def renders (n : Xml.Node) (want : String) : Bool :=
    String.beq (Xml.to_string n) want

#[test]
def test_text : Bool :=
    renders (Xml.Node.node_text "hello") "hello"

#[test]
def test_element : Bool :=
    renders
        (Xml.Node.node_element "note" [Xml.Attr.attr "id" "1"] [Xml.Node.node_text "hello"])
        "<note id=\"1\">hello</note>"

#[test]
def test_nested_elements : Bool :=
    renders
        (Xml.Node.node_element "a" List.empty
            [Xml.Node.node_element "b" List.empty [Xml.Node.node_text "x"]])
        "<a><b>x</b></a>"

#[test]
def test_text_escapes_markup : Bool :=
    renders (Xml.Node.node_text "a & b < c > d") "a &amp; b &lt; c &gt; d"

#[test]
def test_attr_escapes_quotes_and_markup : Bool :=
    renders
        (Xml.Node.node_element "x" [Xml.Attr.attr "v" "a & \"b\" <c>"] List.empty)
        "<x v=\"a &amp; &quot;b&quot; &lt;c&gt;\"></x>"

#[test]
def test_text_preserves_utf8 : Bool :=
    renders (Xml.Node.node_text "héllo 世界") "héllo 世界"

#[test]
def test_comment : Bool :=
    renders (Xml.Node.node_comment " note ") "<!-- note -->"

#[test]
def test_beq_structural : Bool :=
    Xml.beq
        (Xml.Node.node_element "a" [Xml.Attr.attr "id" "1"] [Xml.Node.node_text "x"])
        (Xml.Node.node_element "a" [Xml.Attr.attr "id" "1"] [Xml.Node.node_text "x"])

#[test]
def test_beq_distinguishes : Bool :=
    Bool.not (Xml.beq (Xml.Node.node_text "a") (Xml.Node.node_text "b"))
