// Shared render helper for tests and the conformance harness: CommonMark
// options in, XHTML void spelling out, HTML compared as text.
use xml_html::html {Html.RenderOpts, Html.to_string_with}
use lib::options {
    Markdown.HtmlOptions, Markdown.commonmark_options, Markdown.conformance_html_options,
    Markdown.default_html_options,
}
use lib::parse {Markdown.parse, Markdown.parse_with}
use lib::html {Markdown.to_html_with}

pub def Markdown.conformance_render_opts : Html.RenderOpts :=
    { charset := false, annotate := false, xhtml_void := true }

/// Render a document with the conformance options (verbatim HTML, no URL
/// filtering), the way the spec's expected output is written.
pub def Markdown.render_with (opts : Markdown.HtmlOptions) (src : String) : String :=
    Html.to_string_with Markdown.conformance_render_opts
        (Markdown.to_html_with opts (Markdown.parse_with Markdown.commonmark_options src))

pub def Markdown.render (src : String) : String :=
    Markdown.render_with Markdown.conformance_html_options src

/// Render with the library defaults (raw HTML escaped, safe URLs on).
pub def Markdown.render_default (src : String) : String :=
    Markdown.render_with Markdown.default_html_options src
