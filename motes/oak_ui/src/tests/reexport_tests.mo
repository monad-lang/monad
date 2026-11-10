/// `oak/src/lib.mo` re-exports `Html.to_string` (and the raw markup types)
/// from `xml_html::html`. Naming it through `oak` is what `todo-app` wanted:
/// before this fix the brace-item check said "`oak` declares no
/// `Html.to_string`", and completeness then asked for the owner module.
use oak {Html.to_string, Oak.to_html}
use oak::elements {Html.div, Html.text}

#[test]
def test_oak_reexports_html_to_string : Bool :=
    String.beq (Html.to_string (Oak.to_html (Html.div List.empty [Html.text "x"])))
        "<div>x</div>"
