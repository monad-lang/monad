// The regex mote's library root -- bare `use regex` resolves here.
//
// Explicit re-exports of the public surface only; the engine modules
// (parser, hir, nfa, pikevm, ...) are internal.
pub use lib::error {
    RegexSpan,
    RegexSpan.at,
    RegexError,
    RegexError.message,
    RegexError.span,
    RegexError.render,
}
pub use lib::regex {
    Regex,
    RegexBuilder,
    Match,
    Captures,
    Match.as_str,
    Match.len,
    Regex.new,
    RegexBuilder.new,
    RegexBuilder.build,
    Regex.as_str,
    Regex.captures_len,
    Regex.is_match,
    Regex.find,
    Regex.find_at,
    Regex.find_all,
    Regex.captures,
    Regex.captures_all,
    Regex.replace,
    Regex.replace_all,
    Regex.replace_all_with,
    Regex.split,
    Regex.splitn,
    Regex.escape,
    Captures.len,
    Captures.get,
    Captures.name,
    Captures.expand,
}
