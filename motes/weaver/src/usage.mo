/// Per-turn usage tracking.
///
/// shuttle's `on_usage` hook receives the CUMULATIVE session spend
/// (`Loop.send` adds each response once). That number is billing: a
/// tool-using turn makes several model calls, each re-sending the whole
/// prompt, so the cumulative input jumps by the context size per call
/// and is useless as a context gauge.
///
/// The tracker keeps three snapshots: where the turn began (the live
/// row's turn-to-date delta), the previous report (one model call's
/// usage), and the last call (the request size the next autocompact
/// decision needs). It owns no display; both UIs read it.
use shuttle::message {Usage}
use shuttle::context {usage_zero}
use std::ref {Ref}

pub struct UsageTracker {
    turn_start : Usage,
    prev : Usage,
    last : Usage,
}

/// Seed the tracker with the session's spend BEFORE the turn starts.
pub def UsageTracker.start (base : Usage) : IO (Ref UsageTracker) :=
    let t : UsageTracker := { turn_start := base, prev := base, last := usage_zero } in
    Ref.new t

/// Field-wise, clamped at zero: a malformed report (or a provider whose
/// counters move backwards) must not render a negative count.
pub def Usage.delta (now : Usage) (before : Usage) : Usage :=
    { input_tokens := clamp_sub now.input_tokens before.input_tokens,
      output_tokens := clamp_sub now.output_tokens before.output_tokens,
      cached_tokens := clamp_sub now.cached_tokens before.cached_tokens }

def clamp_sub (a : I64) (b : I64) : I64 :=
    if I64.lt a b then 0 else a - b

/// Record one cumulative report; returns the turn-to-date usage (what
/// the live row shows).
pub def UsageTracker.note (r : Ref UsageTracker) (cum : Usage) : IO Usage := do {
    let t <- Ref.get r;
    let call : Usage := Usage.delta cum t.prev;
    let since : Usage := Usage.delta cum t.turn_start;
    let t2 : UsageTracker :=
        { turn_start := t.turn_start, prev := cum, last := call };
    let _ <- Ref.set r t2;
    IO.pure since
}

/// The last model call's usage: the prompt size of the most recent
/// request, cached tokens included (the wires normalize that).
pub def UsageTracker.last (r : Ref UsageTracker) : IO Usage := do {
    let t <- Ref.get r;
    IO.pure t.last
}

/// `on_usage` for a caller that only wants the tracker updated.
pub def UsageTracker.silent (r : Ref UsageTracker) (u : Usage) : IO Unit := do {
    let _ <- UsageTracker.note r u;
    IO.pure unit
}
