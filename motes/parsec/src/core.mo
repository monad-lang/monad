/// Parser core: the result and error types every parser in this tree
/// returns, and the predicates they use.
///
/// Deliberately knows nothing about MONAD. The operator table and the keyword
/// list -- the two things here that encoded this language's grammar rather
/// than parsing in general -- live in `lang/src/parser/`, so a generic parser
/// substrate can take this file as-is. Nothing here imports `lang::types`,
/// and nothing here should.

use std::list {}
pub use lib::input {Input, Text}

/// Every `fail` value carries not just a message but the input remaining
/// right at the point of failure (`remaining` below) — this is what lets a
/// text diagnostic recover a real line:column, and what lets the few
/// error-recovery sites in `lang/src/parser.mo` resume parsing there.
///
/// The remainder is a `Text` cursor, and `Text.offset` is its **absolute
/// byte offset**, so comparing two failures for "which got further" is a
/// field read. That is the fixed cost of what used to be two `strlen`s of the
/// whole remaining file per failed alternative (see
/// `combinators.mo`'s `furthest_error` note).
///
/// The identity `Copy` instance is manual rather than `#[derive Copy]`: this
/// mote sits in the Rust bootstrap host's meta-evaluation closure, and the
/// host's capture re-checks a re-read module's declarations, expanding a
/// `#[derive]` a second time outside whole-program qualification (the
/// generated instance's constructor references then come back unbound). The
/// self-hosted compiler handles the derive; the host must keep accepting the
/// compiler-source surface.
pub type ParseError {
    tag (expected : String) (remaining : Text),
    custom (msg : String) (remaining : Text),
}

pub instance Copy ParseError {
    def copy (e : ParseError) : Pair ParseError ParseError := Pair.pair e e
}

/// Pull the cursor back out of a failed `ParseError` — for the handful of
/// call sites that want to re-describe a failure with a more helpful message
/// (e.g. "expected ] after class constraint" instead of a bare "tag ]") but
/// don't have a conveniently-in-scope `orig`/`rem` local to attach; the
/// wrapped error's own `remaining` is exactly the right position to reuse,
/// since it's the same failure being re-described, not a new one.
#[partial]
pub def parse_error_remaining (e : ParseError) : Text :=
    match e {
        tag _ remaining => remaining,
        custom _ remaining => remaining,
    }

/// Where the failure happened, as an absolute byte offset. O(1).
pub def ParseError.error_offset (e : ParseError) : I64 :=
    Text.offset (parse_error_remaining e)

/// The error a GENERIC combinator builds when it has a cursor but no
/// `ParseError` of its own to re-describe (`many1`'s "expected at least one",
/// `alt_fold`'s empty list). The offset is exact; the cursor stored in the
/// error has no bytes behind it, so a diagnostic is right and *resuming* from
/// such an error would restart at end-of-input. Text combinators hand a real
/// cursor to `ParseError.tag`/`custom` instead, so the recovery sites in
/// `lang/src/parser.mo` (which consume `tag` failures) are unaffected.
pub def parse_error_at [Input S] {S : Type} (msg : String) (s : S) : ParseError :=
    ParseError.custom msg (Text.at_offset (Input.input_offset s))

/// What every parser answers: the input left after the parse (as the same
/// cursor type it consumed) and either the output or the failure.
///
/// `S` is the cursor: `Text` for text, `Bytes` for binary. Structural
/// combinators are generic over it; primitives name the concrete one.
pub type ParseResult S O {
    success (remaining : S) (output : O),
    fail (error : ParseError)
}

// O(1) on both sides: `String.get s 0` reads one byte (the native's
// `i == 0` fast path skips the length call entirely in compiled
// binaries), while `String.length s == 0` ran a full `strlen`
// of the whole remaining input -- called once per scan step by every
// `take_while`-style loop, that made a native parse O(n^2) in pure
// byte-scans (an empty-check costing more than the scan itself).
// `get` returns `Option.none` exactly when the index is out of range,
// and index 0 is in range exactly when the string is non-empty, so
// this is semantics-preserving (including the NULL case: length is 0,
// `get` yields none).
//
// Kept as a `String` helper: callers that hold a plain string (the
// markdown/html scanners) use it, and parser code uses
// `Input.at_end` on its cursor instead.
pub def is_empty (s : String) : Bool :=
    match String.get s 0 {
        Option.some _ => false,
        Option.none => true
    }
