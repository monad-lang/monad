// Doc comments in the detail panel: a declaration's or module's `///`
// markdown, rendered with the markdown mote straight to `Html.Node` (so no
// HTML string ever reaches the DOM), then embedded with `Oak.of_html`.
//
// Raw HTML in a doc comment is not passed through and unsafe link schemes
// are dropped: `Markdown.default_html_options`.

use xml_html::html {Html.Node}
use markdown::parse {Markdown.parse_with}
use markdown::html {Markdown.to_html_nodes_with}
use markdown::options {Markdown.default_options, Markdown.default_html_options}

/// `markdown` rendered to HTML nodes; empty for empty text. The app renders
/// once per selection and caches the nodes (a drag re-renders every move).
pub def Trellis.render_docs (markdown : String) : List Html.Node :=
    if String.is_empty (String.trim markdown) then List.empty
    else Markdown.to_html_nodes_with Markdown.default_html_options
        (Markdown.parse_with Markdown.default_options markdown)
