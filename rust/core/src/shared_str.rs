//! `SharedStr` — a cheaply-clonable, cheaply-sliceable string value.
//!
//! Backs `IrLit::Str` (`core_ir.rs`), the runtime representation of a
//! Monad `String`. Before this type existed, `IrLit::Str` was a plain
//! owned `String`, and the natives implementing `String.slice`/
//! `String.drop` (`core_native.rs`) each did a full byte-copy of their
//! result on every call. The self-hosted parser (`lang/parser.mo`,
//! `lang/parser/combinators.mo`) threads "the rest of the source file"
//! through essentially every grammar function this way, consuming it a
//! character (or a few bytes) at a time — so parsing a file of length N
//! cost `O(N) + O(N-1) + O(N-2) + ... = O(N^2)` in wall time, independent
//! of grammar complexity. See `plans/implementations/shared-str-and-
//! typecheck-optimization.md` for the full writeup and measurements.
//!
//! `SharedStr` fixes this by separating "the backing allocation" from
//! "the currently-visible window into it": `slice`/`drop` become O(1) —
//! bump an `Arc` refcount, adjust two `usize`s — instead of copying
//! bytes. `read_file` (the natural entry point for parser input) wraps
//! the whole file's content in ONE `SharedStr`; every subsequent
//! `slice`/`drop` during parsing shares that single backing allocation.
//!
//! `Arc`, not `Rc`: the evaluator runs on real OS threads
//! (`run_tests_parallel`, `force_global_with_timeout`'s per-call thread
//! spawn, `std/concurrent`'s real-thread runtime — see `core_value.rs`'s
//! own `Env`/`Arc` doc comment for the identical, already-made tradeoff),
//! and `Value` is asserted `Send + Sync` at compile time
//! (`core_value.rs`'s `_assert_send_sync`) — `Rc` would fail that
//! assertion the moment it's embedded here.

use std::fmt;
use std::sync::Arc;

/// A view into a shared, immutable string allocation.
///
/// Invariant: `start <= end <= backing.len()`, and both `start` and
/// `end` always land on a UTF-8 character boundary of `backing` — so
/// `as_str` never panics and never needs to re-validate on every call.
#[derive(Clone)]
pub struct SharedStr {
  backing: Arc<str>,
  start: usize,
  end: usize,
}

impl SharedStr {
  /// Wrap a freshly-owned `String` as a new backing allocation, visible
  /// in full. Every construction site that produces genuinely new string
  /// content (`String.concat`, `read_file`, `string_from_list`, ...)
  /// goes through this.
  pub fn owned(s: String) -> Self {
    let backing: Arc<str> = Arc::from(s);
    let end = backing.len();
    SharedStr {
      backing,
      start: 0,
      end,
    }
  }

  /// The currently-visible content, as a plain `&str`. O(1) — no copy.
  pub fn as_str(&self) -> &str {
    // Safety of the unchecked indexing: `start`/`end` are maintained as
    // valid char boundaries into `backing` by construction (`owned`
    // starts at `(0, len)`; `subslice` validates any new bound before
    // accepting it) — this is exactly the invariant that makes slicing
    // safe without re-checking boundaries on every access.
    &self.backing[self.start..self.end]
  }

  /// Byte length of the currently-visible content.
  pub fn len(&self) -> usize {
    self.end - self.start
  }

  pub fn is_empty(&self) -> bool {
    self.start == self.end
  }

  /// The O(1) core operation: a new `SharedStr` sharing this one's
  /// backing allocation, visible from byte offset `rel_start` to
  /// `rel_end` *relative to the current visible window* (i.e. in the
  /// same coordinate space `as_str()`'s byte offsets use, not
  /// `backing`'s).
  ///
  /// Matches `string_slice`/`string_drop`'s pre-existing, documented
  /// behavior exactly: falls back to an **empty** `SharedStr` — never
  /// panics — if `rel_start > rel_end`, either bound is out of range, or
  /// either bound doesn't land on a UTF-8 character boundary (reachable
  /// any time a scanner steps into the middle of a multi-byte codepoint;
  /// see `core_native.rs`'s own comment on `string_slice` for a
  /// confirmed-real example, not just a theoretical case).
  pub fn subslice(&self, rel_start: usize, rel_end: usize) -> Self {
    if rel_start > rel_end || rel_end > self.len() {
      return SharedStr::owned(String::new());
    }
    let new_start = self.start + rel_start;
    let new_end = self.start + rel_end;
    if !self.backing.is_char_boundary(new_start) || !self.backing.is_char_boundary(new_end) {
      return SharedStr::owned(String::new());
    }
    SharedStr {
      backing: self.backing.clone(),
      start: new_start,
      end: new_end,
    }
  }

  /// `drop n` — everything from byte offset `n` (relative to the current
  /// visible window) to the end. Same fallback-to-empty behavior as
  /// `subslice` for an out-of-range or non-boundary `n`.
  pub fn drop_prefix(&self, n: usize) -> Self {
    self.subslice(n, self.len())
  }
}

impl From<String> for SharedStr {
  fn from(s: String) -> Self {
    SharedStr::owned(s)
  }
}

impl From<&str> for SharedStr {
  fn from(s: &str) -> Self {
    SharedStr::owned(s.to_string())
  }
}

impl Default for SharedStr {
  fn default() -> Self {
    SharedStr::owned(String::new())
  }
}

/// Content-based, not offset-based: two `SharedStr`s with equal visible
/// content are equal regardless of which backing allocation or offsets
/// produced them. This is what every existing consumer (`string_eq` and
/// friends, `IrLit`'s derived `PartialEq`) already assumes.
impl PartialEq for SharedStr {
  fn eq(&self, other: &Self) -> bool {
    self.as_str() == other.as_str()
  }
}

impl Eq for SharedStr {}

/// Ergonomic content comparison against a plain `&str`/`str`, e.g.
/// `matches!(v, Value::Lit(IrLit::Str(ref s)) if s == "foobar")` — used
/// throughout `core_native.rs`'s existing test assertions.
impl PartialEq<str> for SharedStr {
  fn eq(&self, other: &str) -> bool {
    self.as_str() == other
  }
}

impl PartialEq<&str> for SharedStr {
  fn eq(&self, other: &&str) -> bool {
    self.as_str() == *other
  }
}

/// Delegates to `str`'s own `Debug` (quoted, escaped) so `IrLit::Str`'s
/// `write!(f, "{s:?}")` (`core_ir.rs`) keeps producing identical output.
impl fmt::Debug for SharedStr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.as_str().fmt(f)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn owned_is_visible_in_full() {
    let s = SharedStr::owned("hello".to_string());
    assert_eq!(s.as_str(), "hello");
    assert_eq!(s.len(), 5);
  }

  #[test]
  fn subslice_is_content_correct() {
    let s = SharedStr::owned("hello world".to_string());
    assert_eq!(s.subslice(0, 5).as_str(), "hello");
    assert_eq!(s.subslice(6, 11).as_str(), "world");
    assert_eq!(s.subslice(0, 0).as_str(), "");
  }

  #[test]
  fn subslice_shares_backing_allocation() {
    let s = SharedStr::owned("hello world".to_string());
    let a = s.subslice(0, 5);
    let b = s.subslice(6, 11);
    // Both derived slices point at the same Arc allocation as `s`.
    assert!(Arc::ptr_eq(&a.backing, &s.backing));
    assert!(Arc::ptr_eq(&b.backing, &s.backing));
  }

  #[test]
  fn drop_prefix_matches_slice_to_end() {
    let s = SharedStr::owned("hello world".to_string());
    assert_eq!(s.drop_prefix(6).as_str(), "world");
    assert_eq!(s.drop_prefix(0).as_str(), "hello world");
    assert_eq!(s.drop_prefix(11).as_str(), "");
  }

  #[test]
  fn out_of_range_falls_back_to_empty_not_panic() {
    let s = SharedStr::owned("hi".to_string());
    assert_eq!(s.subslice(0, 100).as_str(), "");
    assert_eq!(s.subslice(5, 6).as_str(), "");
    assert_eq!(s.drop_prefix(100).as_str(), "");
  }

  #[test]
  fn non_char_boundary_falls_back_to_empty_not_panic() {
    // "é" is 2 bytes (0xC3 0xA9) — byte offset 1 is mid-character.
    let s = SharedStr::owned("é".to_string());
    assert_eq!(s.subslice(0, 1).as_str(), "");
    assert_eq!(s.drop_prefix(1).as_str(), "");
    // Full-width slice/drop still work.
    assert_eq!(s.subslice(0, 2).as_str(), "é");
    assert_eq!(s.drop_prefix(0).as_str(), "é");
  }

  #[test]
  fn chained_slicing_from_repeated_drops_stays_correct() {
    // Mirrors the parser's own usage pattern: repeatedly drop a prefix
    // and re-slice from the shrinking remainder.
    let mut rest = SharedStr::owned("abcdefgh".to_string());
    let mut collected = String::new();
    while !rest.is_empty() {
      collected.push_str(rest.subslice(0, 1).as_str());
      rest = rest.drop_prefix(1);
    }
    assert_eq!(collected, "abcdefgh");
  }

  #[test]
  fn equality_is_content_based_across_different_offsets() {
    let a = SharedStr::owned("xxhelloxx".to_string()).subslice(2, 7);
    let b = SharedStr::owned("hello".to_string());
    assert_eq!(a.as_str(), "hello");
    assert_eq!(a, b);
  }

  #[test]
  fn debug_format_matches_str_debug() {
    let s = SharedStr::owned("hi\n\"there\"".to_string());
    assert_eq!(format!("{s:?}"), format!("{:?}", "hi\n\"there\""));
  }
}
