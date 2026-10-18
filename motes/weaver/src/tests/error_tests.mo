/// The WeaverError tests -- weaver.md Phase 9 (Design 7): `show` is the
/// ONE render point (what a human reads, no color -- coloring is the
/// UI's job, Phase 11's), `recoverable` is the ONE classification point
/// (continue the session vs. exit 1), and `of_shuttle` is the ONE
/// boundary wrap (shuttle stays `String`; the drive path wraps as
/// `provider`). All pure -- the whole point of the type is that these
/// decisions are data, testable without I/O.
use weaver::error {WeaverError, WeaverError.show, WeaverError.recoverable, WeaverError.of_shuttle}

/// Structural equality, detail included -- `show` and `recoverable` are
/// both total over this shape, so a variant test that ignores the detail
/// would not catch a dropped payload.
def error_eq (a : WeaverError) (b : WeaverError) : Bool :=
    match a {
        WeaverError.config d => match b { WeaverError.config d2 => d == d2, _ => false },
        WeaverError.settings d => match b { WeaverError.settings d2 => d == d2, _ => false },
        WeaverError.provider d => match b { WeaverError.provider d2 => d == d2, _ => false },
        WeaverError.io d => match b { WeaverError.io d2 => d == d2, _ => false },
        WeaverError.mcp d => match b { WeaverError.mcp d2 => d == d2, _ => false },
        WeaverError.usage d => match b { WeaverError.usage d2 => d == d2, _ => false },
        WeaverError.internal d => match b { WeaverError.internal d2 => d == d2, _ => false },
    }

// ── show: the one render point ──────────────────────────────────────────

/// Every variant's exact rendered line, pinned -- the UIs print
/// `error: <show>` and nothing else composes prose from an error.
#[test]
def test_show_per_variant : Bool :=
    WeaverError.show (WeaverError.config "bad flag")
        == "config: bad flag"
        && WeaverError.show (WeaverError.settings "unparsable file")
        == "settings: unparsable file"
        && WeaverError.show (WeaverError.provider "wire down")
        == "provider: wire down"
        && WeaverError.show (WeaverError.io "no such file")
        == "io: no such file"
        && WeaverError.show (WeaverError.mcp "connect failed")
        == "mcp: connect failed"
        && WeaverError.show (WeaverError.usage "budget gone")
        == "usage: budget gone"
        && WeaverError.show (WeaverError.internal "invariant broke")
        == "internal: invariant broke"

// ── recoverable: the one classification point ───────────────────────────

/// Recoverable (session kept, the loop continues): the wire hiccup class
/// -- provider, io, usage -- plus settings, whose failures are warnings
/// an interactive tool starts anyway (Phase 9's settings contract).
#[test]
def test_recoverable_variants : Bool :=
    WeaverError.recoverable (WeaverError.provider "x")
        && WeaverError.recoverable (WeaverError.io "x")
        && WeaverError.recoverable (WeaverError.usage "x")
        && WeaverError.recoverable (WeaverError.settings "x")

/// Fatal (exit 1): config -- the run was misconfigured before it started
/// -- and mcp -- a failed mount cannot be retried from inside the loop.
#[test]
def test_fatal_variants : Bool :=
    Bool.not (WeaverError.recoverable (WeaverError.config "x"))
        && Bool.not (WeaverError.recoverable (WeaverError.mcp "x"))
        && Bool.not (WeaverError.recoverable (WeaverError.internal "x"))

// ── of_shuttle: the one boundary wrap ───────────────────────────────────

/// Shuttle's `String` errors arrive with no classification, and the only
/// place they cross into Weaver's typed world en masse is the drive path
/// -- so the wrap tags them `provider`, detail verbatim.
#[test]
def test_of_shuttle_tags_provider : Bool :=
    error_eq (WeaverError.of_shuttle "send failed: connection reset")
        (WeaverError.provider "send failed: connection reset")
