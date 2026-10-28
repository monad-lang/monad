// Shared render helper for tests and the conformance harness.
use xml_html::html {Html.RenderOpts, Html.to_string_with}
use lib::options {
    Markdown.HtmlOptions, Markdown.Options, Markdown.commonmark_options,
    Markdown.conformance_html_options, Markdown.default_html_options,
    Markdown.default_options,
}
use lib::parse {Markdown.parse_with}
use lib::html {Markdown.to_html_with}

pub def Markdown.conformance_render_opts : Html.RenderOpts :=
    { charset := false, annotate := false, xhtml_void := true }

/// Render with explicit parser and renderer options.
pub def Markdown.render_full
    (parse : Markdown.Options) (html : Markdown.HtmlOptions) (src : String) : String :=
    Html.to_string_with Markdown.conformance_render_opts
        (Markdown.to_html_with html (Markdown.parse_with parse src))

/// Strict CommonMark with the conformance renderer: what the spec fixture
/// expects.
pub def Markdown.render (src : String) : String :=
    Markdown.render_full Markdown.commonmark_options Markdown.conformance_html_options src

/// The GFM-on parser with the library's default renderer.
pub def Markdown.render_gfm (src : String) : String :=
    Markdown.render_full Markdown.default_options Markdown.default_html_options src

/// CommonMark parsing, default renderer (raw HTML escaped, safe URLs).
pub def Markdown.render_default (src : String) : String :=
    Markdown.render_full Markdown.commonmark_options Markdown.default_html_options src
