use std::sync::{Arc, Mutex as StdMutex, MutexGuard};

pub struct Mutex<T> {
  inner: Arc<StdMutex<T>>,
}

impl<T> Clone for Mutex<T> {
  fn clone(&self) -> Self {
    Mutex {
      inner: Arc::clone(&self.inner),
    }
  }
}

impl<T> Mutex<T> {
  pub fn new(value: T) -> Self {
    Mutex {
      inner: Arc::new(StdMutex::new(value)),
    }
  }

  pub fn lock(&self) -> MutexGuard<'_, T> {
    self.inner.lock().unwrap()
  }

  pub fn try_lock(&self) -> Option<MutexGuard<'_, T>> {
    self.inner.try_lock().ok()
  }
}

impl<T: std::fmt::Debug> std::fmt::Debug for Mutex<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("Mutex").finish()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::sync::{Arc, Barrier};
  use std::thread;

  #[test]
  fn test_mutex_lock_unlock() {
    let m = Mutex::new(42);
    {
      let guard = m.lock();
      assert_eq!(*guard, 42);
    }
    {
      let guard = m.lock();
      assert_eq!(*guard, 42);
    }
  }

  #[test]
  fn test_mutex_mutation() {
    let m = Mutex::new(0);
    {
      let mut guard = m.lock();
      *guard += 1;
    }
    {
      let guard = m.lock();
      assert_eq!(*guard, 1);
    }
  }

  #[test]
  fn test_mutex_try_lock() {
    let m = Mutex::new(0);
    {
      let guard = m.try_lock().unwrap();
      assert_eq!(*guard, 0);
      assert!(m.try_lock().is_none());
    }
    assert!(m.try_lock().is_some());
  }

  #[test]
  fn test_mutex_concurrent() {
    let m = Mutex::new(0usize);
    let n_threads = 8;
    let n_incs = 1000;
    let barrier = Arc::new(Barrier::new(n_threads));

    let mut handles = Vec::new();
    for _ in 0..n_threads {
      let m_clone = m.clone();
      let b = Arc::clone(&barrier);
      handles.push(thread::spawn(move || {
        b.wait();
        for _ in 0..n_incs {
          *m_clone.lock() += 1;
        }
      }));
    }

    for h in handles {
      h.join().unwrap();
    }

    assert_eq!(*m.lock(), n_threads * n_incs);
  }

  #[test]
  fn test_mutex_clone_shares_state() {
    let m1 = Mutex::new(0);
    let m2 = m1.clone();
    *m2.lock() = 42;
    assert_eq!(*m1.lock(), 42);
  }
}
