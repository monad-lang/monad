/// The fmt mote's library root -- bare `use fmt` resolves here.
///
/// Small on purpose (`lang/src/lib.mo`'s doctrine): types and the entry
/// points a consumer needs, not a mirror of every module. A tool that wants
/// only the tokenizer names `fmt::lexer` for it; a tool that wants the
/// formatter can use these re-exports directly.

pub use lib::config {FmtConfig, LineEnding}

pub use lib::lexer {
    Gap, LexError, TokKind, Token,
    Lex.gap_tight, Lex.kind_tag, Lex.lex, Lex.lines, Lex.same_token,
}

pub use lib::highlight {
    HlClass, Span, Highlight.css_class, Highlight.is_keyword, Highlight.spans,
}

pub use lib::fmt {
    Fmt.default_config, Fmt.format_source, Fmt.is_formatted, FmtError,
}

pub use lib::diff {Diff.unified}
