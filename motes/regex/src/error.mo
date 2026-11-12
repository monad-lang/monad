/// Spans and errors for the regex front end.
///
/// Every syntax error carries the byte span of the offending piece of the
/// pattern, so `RegexError.render` can print the pattern with a caret line
/// under it.
use std::list {}

/// A byte range `[start, end)` within the pattern.
pub struct RegexSpan {
    start : I64,
    end : I64,
}

pub def RegexSpan.at (start : I64) (stop : I64) : RegexSpan :=
    let s : RegexSpan := { start := start, end := stop } in s

/// Why `Regex.new` refused a pattern.
pub type RegexError {
    /// Malformed syntax.
    syntax (msg : String) (span : RegexSpan),
    /// Well-formed syntax this engine rejects by design (backreferences,
    /// lookaround, possessive repetition, ...): it cannot be matched in
    /// linear time. `hint` says what to write instead.
    unsupported (feature : String) (span : RegexSpan) (hint : String),
    /// The compiled program would exceed the builder's `size_limit`.
    too_big (limit : I64),
    /// Groups, classes or repetitions nest deeper than `nest_limit`.
    nest_limit (limit : I64),
}

/// The one-line message, without the pattern.
pub def RegexError.message (e : RegexError) : String :=
    match e {
        RegexError.syntax msg _ => msg,
        RegexError.unsupported feature _ hint =>
            String.concat_list [feature, " is not supported: ", hint],
        RegexError.too_big limit =>
            String.concat "compiled regex exceeds the size limit of " (I64.to_string limit),
        RegexError.nest_limit limit =>
            String.concat "pattern nests deeper than the limit of " (I64.to_string limit),
    }

pub def RegexError.span (e : RegexError) : Option RegexSpan :=
    match e {
        RegexError.syntax _ span => Option.some span,
        RegexError.unsupported _ span _ => Option.some span,
        RegexError.too_big _ => Option.none,
        RegexError.nest_limit _ => Option.none,
    }

/// The message, then the pattern with `^` under the span (one column per
/// scalar, so text before the span may be non-ASCII):
///
/// ```text
/// regex parse error: backreferences is not supported: ...
///     (a)\1
///        ^^
/// ```
pub def RegexError.render (e : RegexError) (pattern : String) : String :=
    match RegexError.span e {
        Option.none => String.concat "regex error: " (RegexError.message e),
        Option.some sp =>
            String.concat_list ["regex parse error: ", RegexError.message e, "\n    ",
                pattern, "\n    ", String.repeat " " (scalars_in pattern 0 sp.start),
                String.repeat "^" (caret_width pattern sp)],
    }

def caret_width (pattern : String) (sp : RegexSpan) : I64 :=
    let w : I64 := scalars_in pattern sp.start sp.end in
    if I64.lt 0 w then w else 1

/// How many scalars start in `pattern[start, stop)`.
def scalars_in (pattern : String) (start : I64) (stop : I64) : I64 :=
    count_leads (String.to_list (String.slice pattern start (stop - start))) 0

#[terminating]
def count_leads (xs : List U8) (n : I64) : I64 :=
    match xs {
        List.empty => n,
        List.cons b rest =>
            let c : I64 := U8.to_i64 b in
            count_leads rest (if I64.lt 127 c && I64.lt c 192 then n else n + 1),
    }
