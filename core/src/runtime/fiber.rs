use std::sync::{Arc, Condvar, Mutex};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FiberState {
  Pending,
  Running,
  Completed,
  Failed,
  Cancelled,
}

struct Inner<T: Send> {
  state: Mutex<FiberState>,
  result: Mutex<Option<T>>,
  done: Condvar,
}

pub struct Fiber<T: Send + 'static> {
  inner: Arc<Inner<T>>,
}

impl<T: Send> Fiber<T> {
  pub fn new() -> Fiber<T> {
    Fiber {
      inner: Arc::new(Inner {
        state: Mutex::new(FiberState::Pending),
        result: Mutex::new(None),
        done: Condvar::new(),
      }),
    }
  }

  pub fn state(&self) -> FiberState {
    *self.inner.state.lock().unwrap()
  }

  pub fn set_state(&self, s: FiberState) {
    *self.inner.state.lock().unwrap() = s;
    self.inner.done.notify_all();
  }

  pub fn set_result(&self, r: T) {
    *self.inner.result.lock().unwrap() = Some(r);
  }

  pub fn cancel(&self) {
    let mut state = self.inner.state.lock().unwrap();
    if *state == FiberState::Pending {
      *state = FiberState::Cancelled;
      self.inner.done.notify_all();
    }
  }

  /// Atomically transition `Pending -> Running`, but only if the fiber is
  /// still `Pending`. Returns `false` (leaving state untouched) if `cancel`
  /// already won the race and moved it to `Cancelled` — unlike `set_state`,
  /// which overwrites unconditionally and would otherwise clobber a
  /// `Cancelled` fiber back to `Running`.
  pub fn try_start(&self) -> bool {
    let mut state = self.inner.state.lock().unwrap();
    if *state == FiberState::Pending {
      *state = FiberState::Running;
      self.inner.done.notify_all();
      true
    } else {
      false
    }
  }

  pub fn is_cancelled(&self) -> bool {
    *self.inner.state.lock().unwrap() == FiberState::Cancelled
  }

  pub fn is_done(&self) -> bool {
    matches!(
      *self.inner.state.lock().unwrap(),
      FiberState::Completed | FiberState::Failed | FiberState::Cancelled
    )
  }

  pub fn wait(self) -> T {
    let mut state = self.inner.state.lock().unwrap();
    loop {
      match *state {
        FiberState::Completed | FiberState::Failed | FiberState::Cancelled => {
          break;
        }
        _ => {
          state = self.inner.done.wait(state).unwrap();
        }
      }
    }
    self.inner.result.lock().unwrap().take().unwrap()
  }
}

impl<T: Send> Clone for Fiber<T> {
  fn clone(&self) -> Fiber<T> {
    Fiber {
      inner: Arc::clone(&self.inner),
    }
  }
}

impl<T: Send> std::fmt::Debug for Fiber<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("Fiber")
      .field("state", &self.state())
      .finish()
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_fiber_starts_pending() {
    let fiber = Fiber::<i32>::new();
    assert_eq!(fiber.state(), FiberState::Pending);
  }

  #[test]
  fn test_fiber_state_transition_to_completed() {
    let fiber = Fiber::<i32>::new();
    fiber.set_state(FiberState::Running);
    assert_eq!(fiber.state(), FiberState::Running);
    fiber.set_result(42);
    fiber.set_state(FiberState::Completed);
    assert_eq!(fiber.state(), FiberState::Completed);
    assert_eq!(fiber.wait(), 42);
  }

  #[test]
  fn test_fiber_cancellation() {
    let fiber = Fiber::<i32>::new();
    assert_eq!(fiber.state(), FiberState::Pending);
    fiber.cancel();
    assert_eq!(fiber.state(), FiberState::Cancelled);
    assert!(fiber.is_cancelled());
  }

  #[test]
  fn test_fiber_clone_shares_state() {
    let fiber = Fiber::<i32>::new();
    let clone = fiber.clone();
    fiber.set_state(FiberState::Running);
    assert_eq!(clone.state(), FiberState::Running);
  }
}
