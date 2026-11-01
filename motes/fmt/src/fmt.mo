/// The pure formatting facade. The CLI, the LSP server, and tests all call
/// `Fmt.format_source`; nothing here touches the filesystem.
///
/// `format_source` is also a safety gate. The formatted text is re-lexed and
/// compared with the input's token stream: every token must have the same
/// kind and verbatim text, and every parser-sensitive tight pair must keep its
/// 0-vs-positive gap relation (`Rules.tokens_match`). If that fails -- which
/// would be a bug in the lexer or renderer -- formatting returns an error and
/// the caller must not write the result. The gate also makes `a - 1` vs `a -1`
/// impossible to corrupt silently.

use lib::config { FmtConfig }
use lib::lexer { Lex.lex }
use lib::render { Render.render }
use lib::rules { Rules.tokens_match }

pub struct FmtError {
    offset : I64,
    message : String,
}

def result_err (offset : I64) (message : String) : Result FmtError String :=
    let e : FmtError := { offset := offset, message := message } in
    Result.err e

pub def Fmt.default_config : FmtConfig := FmtConfig.default

/// Format a whole module. An empty input stays empty; every non-empty output
/// ends in exactly one line terminator.
pub def Fmt.format_source (cfg : FmtConfig) (src : String) : Result FmtError String :=
    match Lex.lex src {
        Result.err e => result_err e.offset e.message,
        Result.ok tokens =>
            let out : String := Render.render cfg tokens in
            match Lex.lex out {
                Result.err e =>
                    result_err e.offset
                        ("internal: formatted output does not re-lex: " ++ e.message),
                Result.ok out_tokens =>
                    match Lex.lex src {
                        Result.err e => result_err e.offset e.message,
                        Result.ok in_tokens =>
                            if Rules.tokens_match in_tokens out_tokens
                            then Result.ok out
                            else result_err 0 "internal: formatting changed the token stream",
                    },
            },
    }

/// Whether `src` is already in canonical form.
pub def Fmt.is_formatted (cfg : FmtConfig) (src : String) : Result FmtError Bool :=
    match Fmt.format_source cfg src {
        Result.err e => Result.err e,
        Result.ok out => Result.ok (String.beq out src),
    }
