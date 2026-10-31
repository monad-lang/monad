// The markdown mote's library root -- bare `use markdown` resolves here.
//
// The AST and its equality, the parser options, and the parser/renderer
// entry points. No `{*}` globs: every name is spelled, so the mote's public
// surface is this list.
//
// Consumers reach constructors through the dotted type
// (`Markdown.Block.block_paragraph`), which is why every type is re-exported.

pub use lib::types {
    Markdown.Document, Markdown.Frontmatter, Markdown.FrontFormat, Markdown.FrontSplit,
    Markdown.Block, Markdown.Inline, Markdown.ListKind, Markdown.ListItem,
    Markdown.TableRow, Markdown.Align,
    Markdown.beq, Markdown.block_beq, Markdown.inline_beq,
    Markdown.list_item_beq, Markdown.table_row_beq,
}

pub use lib::parse {
    Markdown.parse, Markdown.parse_with, Markdown.split_frontmatter,
}

pub use lib::html {
    Markdown.to_html, Markdown.to_html_with,
    Markdown.to_html_nodes, Markdown.to_html_nodes_with,
}

/// The semantic styled-text renderer (see `render.mo`). Consumers map the
/// `SpanStyle` values to their own colors; `to_plain_lines` is the
/// persistence/copy form.
pub use lib::render {
    Markdown.SpanStyle, Markdown.StyledSpan, Markdown.StyledLine,
    Markdown.to_lines, Markdown.to_plain_lines, Markdown.line_text,
    Markdown.style_name,
}

pub use lib::options {
    Markdown.Options, Markdown.HtmlOptions,
    Markdown.default_options, Markdown.commonmark_options, Markdown.site_options,
    Markdown.default_html_options, Markdown.conformance_html_options,
}
