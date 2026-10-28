// The markdown mote's library root -- bare `use markdown` resolves here.
//
// The AST and its equality, the parser options, and (as later phases land)
// `parse`, `to_html*`. No `{*}` globs: every name is spelled, so the mote's
// public surface is this list.
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

pub use lib::options {
    Markdown.Options, Markdown.HtmlOptions,
    Markdown.default_options, Markdown.commonmark_options, Markdown.site_options,
    Markdown.default_html_options, Markdown.conformance_html_options,
}
