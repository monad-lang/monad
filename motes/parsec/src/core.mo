/// Parser core: the result and error types every parser in this tree
/// returns, and the two predicates they all use.
///
/// Deliberately knows nothing about MONAD. The operator table and the keyword
/// list -- the two things here that encoded this language's grammar rather
/// than parsing in general -- moved to `op_table.mo` and `keywords.mo`, so
/// that a generic parser substrate can take this file as-is. Nothing here
/// imports `lang::types`, and nothing here should.

use std::list {}


/// Every `fail` value carries not just a message but the input
/// remaining right at the point of failure (`remaining` below) — this
/// is what lets `lang/parser/position.mo`'s `location_of_remaining`
/// recover a real line:column for a diagnostic (by diffing `remaining`
/// against the original full source text) without needing to thread a
/// `LocatedSpan` through every one of this parser's ~450 grammar
/// functions the way the Rust reference does (nom-locate,
/// core/src/parser/locate.rs) — `ParseError` is the only type that
/// needed to change, not `ParseResult` itself. See
/// `location_of_remaining`'s own doc comment for the full rationale.
pub type ParseError {
	tag (expected: String) (remaining: String),
	custom (msg: String) (remaining: String),
	}

/// Pull `remaining` back out of an already-failed `ParseError` — for the
/// handful of call sites that want to re-describe a failure with a more
/// helpful message (e.g. "expected ] after class constraint" instead of
/// a bare "tag ]") but don't have a conveniently-in-scope `orig`/`rem`
/// local to attach; the wrapped error's own `remaining` is exactly the
/// right position to reuse, since it's the same failure being
/// re-described, not a new one.
#[partial]
pub def parse_error_remaining (e : ParseError) : String :=
	match e {
		tag _ remaining => remaining,
		custom _ remaining => remaining,
	}


pub type ParseResult O {
	success (remaining: String) (output: O),
	fail (error: ParseError)
	}

// O(1) on both sides: `String.get s 0` reads one byte (the native's
// `i == 0` fast path skips the length call entirely in compiled
// binaries), while the old `String.length s == 0` ran a full `strlen`
// of the whole remaining input -- called once per scan step by every
// `take_while`-style loop, that made a native parse O(n^2) in pure
// byte-scans (an empty-check costing more than the scan itself).
// `get` returns `Option.none` exactly when the index is out of range,
// and index 0 is in range exactly when the string is non-empty, so
// this is semantics-preserving (including the NULL case: length is 0,
// `get` yields none).
pub def is_empty (s : String) : Bool :=
	match String.get s 0 {
		Option.some _ => false,
		Option.none => true
	}
