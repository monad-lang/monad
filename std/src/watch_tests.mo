/// Tests for `std/src/watch.mo`'s pure decoder and predicates.
///
/// A separate file for the reason `stream_tests.mo` gives, and no
/// filesystem: `Watch.decode` takes bytes, so the wire format is pinned
/// here with hand-built `inotify_event` records. The descriptor itself is
/// covered end to end (compiled) by
/// `slow_tests/src/watch_e2e_tests.mo`.
use std::list {List.length}
use std::watch {
  Watch.decode, WatchEvent, WatchEvent.closed_for_write, WatchEvent.created,
  WatchEvent.deleted,
  WatchEvent.has, WatchEvent.ignored, WatchEvent.is_dir, WatchEvent.moved_from,
  WatchEvent.moved_to, WatchEvent.overflowed, WatchEvent.removed_self,
}

// ── building the wire form ───────────────────────────────────────────────
//
// `inotify_event`: watch descriptor (i32 LE), mask (u32 LE), cookie (u32
// LE), name length INCLUDING the NUL padding (u32 LE), then the padded
// name. `len` makes the record a multiple of 16.

#[terminating]
def wt_two_pow (k : I64) : I64 :=
  if I64.lt k 1 then 1 else 2 * wt_two_pow (k - 1)

/// Byte `k` of `n`, little-endian order.
def wt_byte (n : I64) (k : I64) : U8 :=
  U32.to_u8 (I64.to_u32 (I64.div n (wt_two_pow (I64.mul 8 k))))

def wt_u32 (n : I64) : List U8 :=
  [wt_byte n 0, wt_byte n 1, wt_byte n 2, wt_byte n 3]

#[terminating]
def wt_zeros (n : I64) : List U8 :=
  if I64.lt n 1 then List.empty else List.cons 0u8 (wt_zeros (n - 1))

/// The padded name length for a name of `n` bytes (`n + 1` NUL, rounded up
/// to 16).
def wt_pad_len (n : I64) : I64 :=
  let raw := n + 1 in
  I64.mul 16 (I64.div (raw + 15) 16)

def wt_event (watch : I64) (mask : I64) (cookie : I64) (name : String) : List U8 :=
  let name_len := List.length (String.to_list name) in
  let padded := wt_pad_len name_len in
  let pad := I64.sub padded name_len in
  let header := List.append (wt_u32 watch)
    (List.append (wt_u32 mask) (List.append (wt_u32 cookie) (wt_u32 padded))) in
  List.append header
    (List.append (String.to_list name) (wt_zeros pad))

/// A header claiming a 32-byte name with only two bytes behind it: the
/// incomplete tail the decoder must drop.
def wt_truncated_tail (watch : I64) (mask : I64) : List U8 :=
  List.append (wt_u32 watch)
    (List.append (wt_u32 mask)
      (List.append (wt_u32 0) (List.append (wt_u32 32) (String.to_list "ab"))))

// ── reading a decoded event ──────────────────────────────────────────────

def wt_first_name (evs : List WatchEvent) : String :=
  match evs {
    List.cons e _ => e.name,
    List.empty => "<none>"
  }

def wt_first_watch (evs : List WatchEvent) : I64 :=
  match evs {
    List.cons e _ => e.watch,
    List.empty => 0 - 1
  }

def wt_first_mask (evs : List WatchEvent) : I64 :=
  match evs {
    List.cons e _ => e.mask,
    List.empty => 0 - 1
  }

def wt_first_cookie (evs : List WatchEvent) : I64 :=
  match evs {
    List.cons e _ => e.cookie,
    List.empty => 0 - 1
  }

def wt_count (evs : List WatchEvent) : I64 := List.length evs

/// Whether the FIRST event satisfies `check` (false for an empty list).
def wt_first_ok (evs : List WatchEvent) (check : WatchEvent -> Bool) : Bool :=
  match evs {
    List.cons e _ => check e,
    List.empty => false
  }

// ── the tests ────────────────────────────────────────────────────────────

#[test]
def test_watch_decode_one : Bool :=
  let evs := Watch.decode (wt_event 5 0x100 0 "a.mo") in
  let fields_ok := I64.beq (wt_first_watch evs) 5
    && I64.beq (wt_first_mask evs) 0x100
    && I64.beq (wt_first_cookie evs) 0 in
  I64.beq (wt_count evs) 1 && fields_ok && String.beq (wt_first_name evs) "a.mo"

/// A name of exactly 16 bytes gets one NUL and no padding beyond the block;
/// the next event must still start at the right offset.
#[test]
def test_watch_decode_exact_block_name : Bool :=
  let name := "0123456789abcdef" in
  let bytes := List.append (wt_event 1 0x2 0 name) (wt_event 2 0x200 0 "b") in
  let evs := Watch.decode bytes in
  I64.beq (wt_count evs) 2 && String.beq (wt_first_name evs) name

/// Two records back to back, the second about the watched directory itself
/// (a zero-length name).
#[test]
def test_watch_decode_two_and_zero_name : Bool :=
  let bytes := List.append (wt_event 1 0x2 0 "x.mo") (wt_event 1 0x400 0 "") in
  let evs := Watch.decode bytes in
  let second := match evs {
    List.cons _ rest => wt_first_name rest,
    List.empty => "<none>"
  } in
  I64.beq (wt_count evs) 2 && String.beq (wt_first_name evs) "x.mo"
    && String.beq second ""

/// An incomplete tail is dropped, not guessed at: the kernel refuses to
/// split an event into a 4 KiB read, but a short hand-built buffer can.
#[test]
def test_watch_decode_truncated_tail : Bool :=
  let bytes := List.append (wt_event 1 0x2 0 "ok") (wt_truncated_tail 1 0x2) in
  let evs := Watch.decode bytes in
  I64.beq (wt_count evs) 1 && String.beq (wt_first_name evs) "ok"

#[test]
def test_watch_decode_empty_is_empty : Bool :=
  I64.beq (wt_count (Watch.decode List.empty)) 0

// One predicate per named def: a lambda calling the accessors is the
// constrained-call-in-a-lambda shape the codegen bug lives in, and these
// tests run compiled too.

def wt_is_created_dir (e : WatchEvent) : Bool :=
  WatchEvent.created e && WatchEvent.is_dir e && Bool.not (WatchEvent.deleted e)

/// The predicates read the mask the way the mask bits name it.
#[test]
def test_watch_event_predicates : Bool :=
  wt_first_ok (Watch.decode (wt_event 1 0x40000100 0 "dir")) wt_is_created_dir

def wt_is_moved_to (e : WatchEvent) : Bool :=
  WatchEvent.moved_to e && Bool.not (WatchEvent.created e)
    && Bool.not (WatchEvent.moved_from e)

def wt_is_closed (e : WatchEvent) : Bool := WatchEvent.closed_for_write e

def wt_is_removed_self (e : WatchEvent) : Bool := WatchEvent.removed_self e

def wt_is_ignored (e : WatchEvent) : Bool :=
  WatchEvent.ignored e && Bool.not (WatchEvent.overflowed e)

/// `IN_MOVED_TO` is the atomic-save signal; `IN_CLOSE_WRITE` the plain one.
#[test]
def test_watch_event_move_and_close : Bool :=
  let moved := Watch.decode (wt_event 1 0x80 9 "new.mo") in
  let closed := Watch.decode (wt_event 1 0x8 0 "edit.mo") in
  wt_first_ok moved wt_is_moved_to && wt_first_ok closed wt_is_closed

/// A closed watch reports `IN_IGNORED`; nothing else arrives on that handle.
#[test]
def test_watch_event_ignored_is_not_overflow : Bool :=
  let dropped := Watch.decode (wt_event 1 0x8000 0 "") in
  wt_first_ok dropped wt_is_ignored

/// The watched directory going away.
#[test]
def test_watch_event_removed_self : Bool :=
  wt_first_ok (Watch.decode (wt_event 1 0x400 0 "")) wt_is_removed_self

def wt_has_modify_not_create (e : WatchEvent) : Bool :=
  WatchEvent.has e 0x2 && Bool.not (WatchEvent.has e 0x100)

/// `has` is bit membership, not equality: a combined mask answers yes to
/// each of its bits.
#[test]
def test_watch_event_has_is_membership : Bool :=
  let evs := Watch.decode (wt_event 1 0x402 0 "") in
  wt_first_ok evs wt_has_modify_not_create && wt_first_ok evs wt_is_removed_self
