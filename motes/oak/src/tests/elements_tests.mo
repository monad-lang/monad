// Exact-string acceptance tests for the pure builder surface: one golden
// per constructor family, plus the reserved-keyword renames and the two
// components. These strings are the contract Oak's later phases reuse.

use lib::elements {
    Html.id_, Html.class_, Html.href, Html.src, Html.alt, Html.type_, Html.value_,
    Html.placeholder, Html.name_, Html.for_, Html.open_, Html.data, Html.style_attr,
    Html.disabled, Html.checked, Html.required, Html.readonly, Html.selected,
    Html.attr, Html.bool_attr, Html.role, Html.aria, Html.method_, Html.action,
    Html.enctype, Html.enctype_multipart, Html.charset,
    Html.div, Html.span, Html.p, Html.a, Html.ul, Html.li,
    Html.h1, Html.h2, Html.h3, Html.h4, Html.h5, Html.h6,
    Html.header, Html.footer, Html.nav, Html.main_, Html.section, Html.article, Html.aside,
    Html.table, Html.thead, Html.tbody, Html.tr, Html.th, Html.td,
    Html.form, Html.label, Html.select, Html.option, Html.button,
    Html.input, Html.img, Html.br, Html.hr, Html.meta, Html.link,
    Html.script, Html.style, Html.title,
    Html.node, Html.void, Html.text, Html.raw, Html.comment, Html.doctype,
    Html.fragment, Html.document, Html.document_with, Html.document_utf8,
    Html.navbar, Html.card
}
use xml_html::html {Html.Node, Html.to_string}

def element_renders (n : Html.Node) (want : String) : Bool :=
    String.beq (Html.to_string n) want

// ─── Attributes ───

#[test]
def test_id : Bool :=
    element_renders (Html.div [Html.id_ "x"] List.empty) "<div id=\"x\"></div>"

#[test]
def test_class_joins : Bool :=
    element_renders (Html.div [Html.class_ ["a", "b"]] List.empty) "<div class=\"a b\"></div>"

#[test]
def test_class_empty : Bool :=
    element_renders (Html.div [Html.class_ List.empty] List.empty) "<div class=\"\"></div>"

#[test]
def test_href : Bool :=
    element_renders (Html.a [Html.href "/x"] [Html.text "t"]) "<a href=\"/x\">t</a>"

#[test]
def test_img_attrs : Bool :=
    element_renders (Html.img [Html.src "/i.png", Html.alt "pic"]) "<img src=\"/i.png\" alt=\"pic\">"

#[test]
def test_input_attrs : Bool :=
    element_renders
        (Html.input [Html.type_ "text", Html.value_ "v", Html.placeholder "p", Html.name_ "n", Html.required])
        "<input type=\"text\" value=\"v\" placeholder=\"p\" name=\"n\" required>"

#[test]
def test_label_for : Bool :=
    element_renders (Html.label [Html.for_ "f"] [Html.text "L"]) "<label for=\"f\">L</label>"

#[test]
def test_open_bool : Bool :=
    element_renders (Html.node "details" [Html.open_] List.empty) "<details open></details>"

#[test]
def test_data_attr : Bool :=
    element_renders (Html.div [Html.data "id" "42"] List.empty) "<div data-id=\"42\"></div>"

#[test]
def test_style_attr : Bool :=
    element_renders (Html.div [Html.style_attr "color: red"] List.empty) "<div style=\"color: red\"></div>"

#[test]
def test_boolean_attrs : Bool :=
    element_renders
        (Html.input [Html.disabled, Html.checked, Html.readonly, Html.selected])
        "<input disabled checked readonly selected>"

// ─── Text and escape hatches ───

#[test]
def test_text_escapes : Bool :=
    element_renders (Html.text "a & b < c") "a &amp; b &lt; c"

#[test]
def test_node_escape_hatch : Bool :=
    element_renders (Html.node "x-foo" [Html.id_ "a"] [Html.text "b"]) "<x-foo id=\"a\">b</x-foo>"

#[test]
def test_void_escape_hatch : Bool :=
    element_renders (Html.void "x-void" [Html.id_ "v"]) "<x-void id=\"v\">"

#[test]
def test_script_raw : Bool :=
    element_renders (Html.script List.empty "if (a < b) {}") "<script>if (a < b) {}</script>"

#[test]
def test_style_raw : Bool :=
    element_renders (Html.style List.empty "a > b {}") "<style>a > b {}</style>"

#[test]
def test_raw_escape_hatch : Bool :=
    element_renders (Html.raw "script" List.empty "x < y") "<script>x < y</script>"

#[test]
def test_script_module_src : Bool :=
    element_renders
        (Html.script [Html.type_ "module", Html.src "/app.js"] "")
        "<script type=\"module\" src=\"/app.js\"></script>"

#[test]
def test_generic_and_aria_attrs : Bool :=
    element_renders
        (Html.div [Html.attr "data-x" "1", Html.role "main", Html.aria "label" "Main"] List.empty)
        "<div data-x=\"1\" role=\"main\" aria-label=\"Main\"></div>"

#[test]
def test_form_attrs : Bool :=
    element_renders
        (Html.form [Html.method_ "post", Html.action "/todos", Html.enctype Html.enctype_multipart] List.empty)
        "<form method=\"post\" action=\"/todos\" enctype=\"multipart/form-data\"></form>"

#[test]
def test_document_with_attrs : Bool :=
    element_renders
        (Html.document_with [Html.attr "lang" "en"] List.empty [Html.class_ ["home"]] List.empty List.empty)
        "<!DOCTYPE html><html lang=\"en\"><head></head><body class=\"home\"></body></html>"

#[test]
def test_document_utf8 : Bool :=
    element_renders (Html.document_utf8 List.empty List.empty)
        "<!DOCTYPE html><html><head><meta charset=\"utf-8\"></head><body></body></html>"

#[test]
def test_comment_doctype_fragment : Bool :=
    element_renders (Html.fragment [Html.doctype "html", Html.comment " c "]) "<!DOCTYPE html><!-- c -->"

// ─── Documents and components ───

#[test]
def test_document_empty : Bool :=
    element_renders (Html.document List.empty List.empty) "<!DOCTYPE html><html><head></head><body></body></html>"

#[test]
def test_document : Bool :=
    element_renders
        (Html.document [Html.title List.empty [Html.text "T"]] [Html.p List.empty [Html.text "B"]])
        "<!DOCTYPE html><html><head><title>T</title></head><body><p>B</p></body></html>"

#[test]
def test_navbar : Bool :=
    element_renders
        (Html.navbar [Pair.pair "/" "Home", Pair.pair "/docs" "Docs"])
        "<nav class=\"navbar\"><ul><li><a href=\"/\">Home</a></li><li><a href=\"/docs\">Docs</a></li></ul></nav>"

#[test]
def test_card : Bool :=
    element_renders (Html.card "Hi" "Body") "<div class=\"card\"><h2>Hi</h2><p>Body</p></div>"

// ─── Element families ───

#[test]
def test_main_ : Bool :=
    element_renders (Html.main_ List.empty [Html.text "m"]) "<main>m</main>"

#[test]
def test_headings : Bool :=
    element_renders (Html.h1 List.empty [Html.text "1"]) "<h1>1</h1>"
    && element_renders (Html.h2 List.empty [Html.text "2"]) "<h2>2</h2>"
    && element_renders (Html.h3 List.empty [Html.text "3"]) "<h3>3</h3>"
    && element_renders (Html.h4 List.empty [Html.text "4"]) "<h4>4</h4>"
    && element_renders (Html.h5 List.empty [Html.text "5"]) "<h5>5</h5>"
    && element_renders (Html.h6 List.empty [Html.text "6"]) "<h6>6</h6>"

#[test]
def test_semantic_elements : Bool :=
    element_renders (Html.header List.empty List.empty) "<header></header>"
    && element_renders (Html.footer List.empty List.empty) "<footer></footer>"
    && element_renders (Html.nav List.empty List.empty) "<nav></nav>"
    && element_renders (Html.aside List.empty List.empty) "<aside></aside>"
    && element_renders (Html.section List.empty List.empty) "<section></section>"
    && element_renders (Html.article List.empty List.empty) "<article></article>"

#[test]
def test_list_elements : Bool :=
    element_renders
        (Html.ul List.empty [Html.li List.empty [Html.text "a"]])
        "<ul><li>a</li></ul>"
    && element_renders
        (Html.span List.empty [Html.text "s"])
        "<span>s</span>"

#[test]
def test_table : Bool :=
    element_renders
        (Html.table List.empty
            [ Html.thead List.empty
                  [Html.tr List.empty [Html.th List.empty [Html.text "H"]]],
              Html.tbody List.empty
                  [Html.tr List.empty [Html.td List.empty [Html.text "D"]]] ])
        "<table><thead><tr><th>H</th></tr></thead><tbody><tr><td>D</td></tr></tbody></table>"

#[test]
def test_form : Bool :=
    element_renders
        (Html.form [Html.id_ "f"]
            [ Html.label [Html.for_ "n"] [Html.text "Name"],
              Html.input [Html.name_ "n"] ])
        "<form id=\"f\"><label for=\"n\">Name</label><input name=\"n\"></form>"

#[test]
def test_form_controls : Bool :=
    element_renders
        (Html.select List.empty [Html.option List.empty [Html.text "o"]])
        "<select><option>o</option></select>"
    && element_renders
        (Html.button List.empty [Html.text "b"])
        "<button>b</button>"

#[test]
def test_voids : Bool :=
    element_renders (Html.br List.empty) "<br>"
    && element_renders (Html.hr List.empty) "<hr>"
    && element_renders (Html.meta List.empty) "<meta>"
    && element_renders (Html.link List.empty) "<link>"

#[test]
def test_reserved_renames : Bool :=
    element_renders (Html.div [Html.type_ "x"] List.empty) "<div type=\"x\"></div>"
    && element_renders (Html.div [Html.class_ ["c"]] List.empty) "<div class=\"c\"></div>"
    && element_renders (Html.label [Html.for_ "f"] List.empty) "<label for=\"f\"></label>"
    && element_renders (Html.node "details" [Html.open_] List.empty) "<details open></details>"
