/// Weaver's error type -- weaver.md Phase 9 (Design 7): errors were bare
/// `String`s at every seam, so a recoverable wire hiccup and a fatal
/// config error were indistinguishable, and every UI invented its own
/// `error: ...` prose. This file is the type, the ONE render point, the
/// ONE classification point, and the ONE boundary wrap.
///
/// **Shuttle keeps `String`** (Design 7's rejected-alternative record):
/// parameterizing its seams over an error type is churn in an embeddable
/// harness with no second consumer; Weaver wraps at the boundary with
/// `WeaverError.of_shuttle`, and tool failures already arrive as error
/// `tool_result`s the model reacts to.
///
/// Variants, matched to Weaver's actual failure sites: `config` -- the
/// run was misconfigured before it started (a bad flag, an unknown
/// provider); `settings` -- a settings file could not be parsed or read
/// (a warning at startup, never a refusal); `provider` -- the wire, the
/// model, the key; `io` -- a file the user asked for (`/save`, `/resume`)
/// could not be written or read; `mcp` -- a mount failed; `usage` -- the
/// turn budget; `internal` -- an invariant broke, a bug. Each carries its
/// own `detail : String` verbatim.
pub type WeaverError {
    config (detail : String),
    settings (detail : String),
    provider (detail : String),
    io (detail : String),
    mcp (detail : String),
    usage (detail : String),
    internal (detail : String),
}

/// The ONE render point: the message a human reads. No color -- coloring
/// is the UI's job (Phase 11's palette), and this string is also what
/// tests pin. The prefix is the variant's own name, so `error: <show>`
/// reads `error: provider: wire down`.
pub def WeaverError.show (e : WeaverError) : String :=
    match e {
        WeaverError.config d => String.concat "config: " d,
        WeaverError.settings d => String.concat "settings: " d,
        WeaverError.provider d => String.concat "provider: " d,
        WeaverError.io d => String.concat "io: " d,
        WeaverError.mcp d => String.concat "mcp: " d,
        WeaverError.usage d => String.concat "usage: " d,
        WeaverError.internal d => String.concat "internal: " d,
    }

/// The ONE classification point: recoverable keeps the session and the
/// loop continues (the wire-hiccup class -- provider, io, usage -- plus
/// settings, which never refuses an interactive start); fatal ends the
/// run with exit code 1 (config: the run cannot be retried into shape;
/// mcp: a failed mount cannot be re-mounted from inside the loop;
/// internal: a bug, and continuing past one compounds it).
pub def WeaverError.recoverable (e : WeaverError) : Bool :=
    match e {
        WeaverError.provider _ => true,
        WeaverError.io _ => true,
        WeaverError.usage _ => true,
        WeaverError.settings _ => true,
        _ => false,
    }

/// The ONE boundary wrap: shuttle's `String` errors arrive
/// unclassified, and the seam they cross at is the drive path -- so the
/// wrap tags them `provider`, detail verbatim. Non-drive wraps name
/// their own variant at the call site.
pub def WeaverError.of_shuttle (s : String) : WeaverError :=
    WeaverError.provider s
