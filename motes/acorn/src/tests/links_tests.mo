/// The broken-link gate: target resolution and the cross-page check.
use std::list {List.intercalate}
use xml_html::html {Html.Node, Html.Attr}
use lib::links {PageLinks, Links.of_page, Links.target, Links.broken}

def target_text (page : String) (href : String) : String :=
    match Links.target page href {
        Option.none => "-",
        Option.some t => match t { Pair.pair path frag => String.concat path (String.concat "#" frag) },
    }

#[test]
def test_target_resolves_relative_to_the_page : Bool :=
    String.beq (target_text "docs/a.html" "./b.html#x") "docs/b.html#x"
        && String.beq (target_text "docs/a.html" "../index.html") "index.html#"
        && String.beq (target_text "docs/a.html" "#here") "docs/a.html#here"

#[test]
def test_unchecked_links : Bool :=
    String.beq (target_text "docs/a.html" "https://x.org/b.html") "-"
        && String.beq (target_text "docs/a.html" "../try/") "-"
        && String.beq (target_text "docs/a.html" "img/logo.svg") "-"

def link (href : String) : Html.Node :=
    Html.Node.node_element "a" [Html.Attr.attr "href" href] [Html.Node.node_text "x"]

def heading (id : String) : Html.Node :=
    Html.Node.node_element "h2" [Html.Attr.attr "id" id] [Html.Node.node_text "H"]

def site : List PageLinks :=
    [Links.of_page "docs/a.html" [heading "top", link "./b.html#there", link "#top", link "./b.html#nowhere", link "./c.html"],
        Links.of_page "docs/b.html" [Html.Node.node_element "div" List.empty [heading "there"]]]

#[test]
def test_broken_reports_missing_pages_and_anchors : Bool :=
    String.beq (List.intercalate "|" (Links.broken site))
        "docs/a.html: ./b.html#nowhere (no such anchor)|docs/a.html: ./c.html (no such page)"
