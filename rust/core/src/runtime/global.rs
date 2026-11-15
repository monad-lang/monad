// The evaluator's handle table: opaque ids for values the Monad side must
// not see into (fiber/scope handles over `FiberHandle`, byte buffers, TLS
// streams, ...).
//
// ## Why this is not a `Mutex<HashMap>`
//
// It used to be, and that shape had two recorded defects that made the
// Rust host's fiber story worse than its documented "lazy" degradation:
//
//   1. **Non-reentrant.** `with` held the lock across the closure, so an
//      action that touched the table from inside one deadlocked. The lock
//      was still safe only because `fork_io` did not run its action --
//      which is exactly the property the host is meant to keep, so the
//      latent bug sat one refactor away from a hang.
//   2. **Leaked every cancelled handle.** `cancel_fiber` used `with`
//      (not `take`), because a later `await_fiber` had to still find the
//      handle and answer `err cancelled`. A cancel never followed by an
//      await left the entry in the table forever, so the map grew
//      monotonically.
//
// What changed (P3 of `monad-fiber-scheduler.md`):
//
//   * `take` and `drop_handle` remove the entry under the lock and DROP the
//     value outside it, so a `Drop` impl that registers something cannot
//     deadlock. That is the only place a `Drop` can run here, so it is the
//     only place the reentrancy hazard existed.
//   * `with`/`with_mut` still hold the lock across the closure -- they hand
//     out `&T`, so there is no alternative -- and their contract is stated
//     explicitly: the closure must not re-enter this table. No present
//     caller does, and the two that could (`fork_io`'s action, and
//     `cancel_fiber`, which deliberately leaves the handle for a later
//     await) are documented at their own sites.
//   * The counter saturates instead of wrapping, so an id is never reused
//     and a stale id cannot alias a fresh handle.
//
// Full reentrancy would need `Rc<RefCell<_>>` per entry or a lock-free map
// of `Arc`s, which buys nothing while `fork_io` stays lazy -- the host never
// runs a fiber action from inside a table call. Recorded as P3 scope in the
// plan rather than done speculatively.
//
// ## Why an id and not a pointer
//
// Handles are `u64` ids, never addresses: a Monad value is one machine
// word, and handing out a raw pointer would let Monad code forge one. The
// counter is monotonic and never reused, so a stale id can never alias a
// fresh handle -- `with` on a consumed id answers `None` rather than
// reaching a different object.

use std::any::Any;
use std::collections::HashMap;
use std::sync::{LazyLock, Mutex};

static HANDLE_TABLE: LazyLock<Mutex<HandleTable>> = LazyLock::new(Default::default);

#[derive(Default)]
struct HandleTable {
  next_id: u64,
  objects: HashMap<u64, Box<dyn Any + Send>>,
}

pub fn register<T: Send + 'static>(obj: T) -> u64 {
  let mut table = HANDLE_TABLE.lock().expect("handle table poisoned");
  let id = table.next_id;
  // Saturating: an id is never reused, so wrapping would alias a live
  // handle. 2^64 registrations is not reachable in a test process, but a
  // saturating counter that stops handing out new ids is the honest
  // failure rather than a silent collision.
  table.next_id = table.next_id.saturating_add(1);
  table.objects.insert(id, Box::new(obj));
  id
}

/// Run `f` on the object registered under `id`.
///
/// The lock is held for the whole call because `f` gets `&T`: there is no
/// way to hand out a reference and release the lock. That is safe for
/// every present caller -- none of them calls back into this table -- and
/// the contract is therefore explicit: **`f` must not register, take or
/// otherwise re-enter this table.** A closure that needs to do so should
/// `take` the object first, do the work, and `register` the result back.
pub fn with<T: 'static, R>(id: u64, f: impl FnOnce(&T) -> R) -> Option<R> {
  let table = HANDLE_TABLE.lock().expect("handle table poisoned");
  table
    .objects
    .get(&id)
    .and_then(|obj| obj.downcast_ref::<T>().map(f))
}

/// `with_mut`'s contract is `with`'s: the closure must not re-enter.
pub fn with_mut<T: 'static, R>(id: u64, f: impl FnOnce(&mut T) -> R) -> Option<R> {
  let mut table = HANDLE_TABLE.lock().expect("handle table poisoned");
  table
    .objects
    .get_mut(&id)
    .and_then(|obj| obj.downcast_mut::<T>().map(f))
}

/// Remove the object and hand it over. The removal happens under the lock
/// and the value is dropped OUTSIDE it, so a `Drop` impl that registers
/// something cannot deadlock.
pub fn take<T: 'static>(id: u64) -> Option<T> {
  let removed = {
    let mut table = HANDLE_TABLE.lock().expect("handle table poisoned");
    table.objects.remove(&id)
  };
  removed.and_then(|obj| obj.downcast::<T>().ok().map(|b| *b))
}

/// How many objects are registered -- a leak probe for tests (a
/// `ByteBuf` read and never freed stays here for the process's life).
pub fn live_count() -> usize {
  let table = HANDLE_TABLE.lock().expect("handle table poisoned");
  table.objects.len()
}

pub fn drop_handle(id: u64) {
  // Same "drop outside the lock" rule as `take`.
  let removed = {
    let mut table = HANDLE_TABLE.lock().expect("handle table poisoned");
    table.objects.remove(&id)
  };
  drop(removed);
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_register_and_with() {
    let id = register(42i64);
    let result = with::<i64, _>(id, |v| *v);
    assert_eq!(result, Some(42));
  }

  #[test]
  fn test_register_unique_ids() {
    let a = register("hello".to_string());
    let b = register("world".to_string());
    assert_ne!(a, b);
  }

  #[test]
  fn test_with_wrong_type() {
    let id = register(42i64);
    let result = with::<String, _>(id, |s| s.clone());
    assert_eq!(result, None);
  }

  #[test]
  fn test_with_nonexistent_id() {
    let result = with::<i64, _>(999, |v| *v);
    assert_eq!(result, None);
  }

  #[test]
  fn test_with_mut_updates_in_place() {
    let id = register(vec![1u8, 2, 3]);
    with_mut::<Vec<u8>, _>(id, |v| v.truncate(1));
    assert_eq!(with::<Vec<u8>, _>(id, |v| v.clone()), Some(vec![1u8]));
  }

  #[test]
  fn test_take_removes_object() {
    let id = register(99i64);
    let taken = take::<i64>(id);
    assert_eq!(taken, Some(99));
    let result = with::<i64, _>(id, |v| *v);
    assert_eq!(result, None);
  }

  #[test]
  fn test_drop_handle() {
    let id = register(7i64);
    drop_handle(id);
    let result = with::<i64, _>(id, |v| *v);
    assert_eq!(result, None);
  }

  #[test]
  fn test_register_custom_type() {
    #[derive(Debug, PartialEq)]
    struct Foo {
      x: i64,
      y: String,
    }
    let id = register(Foo {
      x: 10,
      y: "bar".to_string(),
    });
    let result = with::<Foo, _>(id, |f| f.x);
    assert_eq!(result, Some(10));
  }

  /// P3's reentrancy fix, at the one point it can be proven: a value whose
  /// `Drop` registers a NEW handle. `take` and `drop_handle` remove under
  /// the lock and drop outside it, so this completes; the old
  /// `Mutex<HashMap>` shape dropped the removed `Box` while the table lock
  /// was still held only by luck of where `remove`'s temporary ended, and
  /// any code path that ran a `Drop` under the lock would have hung.
  #[test]
  fn test_take_drops_outside_the_lock() {
    struct RegistersOnDrop;
    impl Drop for RegistersOnDrop {
      fn drop(&mut self) {
        // Re-entering the table from a Drop must not deadlock.
        let id = register(1i64);
        assert_eq!(take::<i64>(id), Some(1));
      }
    }
    let id = register(RegistersOnDrop);
    assert!(take::<RegistersOnDrop>(id).is_some());
    let id2 = register(RegistersOnDrop);
    drop_handle(id2);
  }

  /// A cancelled fiber's handle is consumed by the await that follows it:
  /// after the pair, the id resolves to nothing.
  ///
  /// `live_count` is NOT asserted against a delta here: `HANDLE_TABLE` is a
  /// process-wide singleton and cargo runs these tests in parallel, so any
  /// other test's registrations land in the same count. The per-id
  /// observable is what is actually this test's subject.
  /// (`core_native.rs`'s `cancel_fiber` deliberately keeps the handle so a
  /// later await can answer `err cancelled`; that await is the consumer.)
  #[test]
  fn test_cancel_then_take_leaves_no_entry() {
    let id = register(7i64);
    // `cancel_fiber` uses `with`, so the entry survives the cancel ...
    assert_eq!(with::<i64, _>(id, |v| *v), Some(7));
    // ... and the await that follows is what consumes it.
    assert_eq!(take::<i64>(id), Some(7));
    // Nothing answers for the id afterwards.
    assert_eq!(with::<i64, _>(id, |v| *v), None);
    assert_eq!(take::<i64>(id), None);
  }
}
