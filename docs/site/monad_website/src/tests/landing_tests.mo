/// The landing page document.
use xml_html::html {Html.to_string}
use oak::typed {Oak.to_html}
use acorn::config {SiteConfig}
use lib::landing {Landing.page}

def cfg : SiteConfig :=
    { title := "Monad language", base_url := "/", book_src := "docs/src",
        book_dir := "docs", out_dir := "out" }

def html : String :=
    Html.to_string (Oak.to_html (Landing.page cfg))

#[test]
def test_landing_links_the_book_and_try : Bool :=
    let h : String := html in
    String.contains h "<h1>Monad</h1>"
        && String.contains h "href=\"docs/introduction.html\""
        && String.contains h "href=\"docs/maturity.html\""
        && String.contains h "href=\"try/\""
        && String.contains h "<link rel=\"stylesheet\" href=\"landing.css\">"

#[test]
def test_landing_icons_use_the_sprite : Bool :=
    String.contains html "<svg width=\"24\" height=\"24\"><use href=\"icons.svg#icon-zap\"></use></svg>"
        && String.contains html "<svg><use href=\"icons.svg#icon-discord\"></use></svg>Discord"

#[test]
def test_landing_example_is_highlighted : Bool :=
    String.contains html "<span class=\"kw\">def</span> <span class=\"fn\">factorial</span>"
