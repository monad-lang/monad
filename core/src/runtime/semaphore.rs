use std::sync::{Arc, Condvar, Mutex};

pub struct Semaphore {
  inner: Arc<Inner>,
}

struct Inner {
  permits: Mutex<isize>,
  condvar: Condvar,
}

impl Clone for Semaphore {
  fn clone(&self) -> Self {
    Semaphore {
      inner: Arc::clone(&self.inner),
    }
  }
}

impl Semaphore {
  pub fn new(permits: isize) -> Self {
    Semaphore {
      inner: Arc::new(Inner {
        permits: Mutex::new(permits),
        condvar: Condvar::new(),
      }),
    }
  }

  pub fn acquire(&self) {
    let mut permits = self.inner.permits.lock().unwrap();
    loop {
      if *permits > 0 {
        *permits -= 1;
        return;
      }
      permits = self.inner.condvar.wait(permits).unwrap();
    }
  }

  pub fn release(&self) {
    let mut permits = self.inner.permits.lock().unwrap();
    *permits += 1;
    self.inner.condvar.notify_one();
  }

  pub fn try_acquire(&self) -> bool {
    let mut permits = self.inner.permits.lock().unwrap();
    if *permits > 0 {
      *permits -= 1;
      true
    } else {
      false
    }
  }

  pub fn available(&self) -> isize {
    *self.inner.permits.lock().unwrap()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::sync::{Arc, Barrier};
  use std::thread;

  #[test]
  fn test_semaphore_acquire_release() {
    let s = Semaphore::new(2);
    s.acquire();
    s.acquire();
    assert_eq!(s.available(), 0);
    s.release();
    assert_eq!(s.available(), 1);
  }

  #[test]
  fn test_semaphore_blocks_when_zero() {
    let s = Semaphore::new(1);
    s.acquire();

    let s_clone = s.clone();
    let barrier = Arc::new(Barrier::new(2));
    let b = Arc::clone(&barrier);

    let handle = thread::spawn(move || {
      b.wait();
      s_clone.acquire();
      assert_eq!(s_clone.available(), 0);
    });

    barrier.wait();
    thread::sleep(std::time::Duration::from_millis(20));
    s.release();
    handle.join().unwrap();
    assert_eq!(s.available(), 0);
  }

  #[test]
  fn test_semaphore_try_acquire() {
    let s = Semaphore::new(1);
    assert!(s.try_acquire());
    assert!(!s.try_acquire());
    s.release();
    assert!(s.try_acquire());
  }

  #[test]
  fn test_semaphore_concurrent() {
    let s = Semaphore::new(4);
    let n_threads = 8;
    let counter = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let barrier = Arc::new(Barrier::new(n_threads));

    let mut handles = Vec::new();
    for _ in 0..n_threads {
      let s_clone = s.clone();
      let c = Arc::clone(&counter);
      let b = Arc::clone(&barrier);
      handles.push(thread::spawn(move || {
        b.wait();
        s_clone.acquire();
        let current = c.fetch_add(1, std::sync::atomic::Ordering::SeqCst) + 1;
        assert!(current <= 4, "too many permits: {}", current);
        thread::sleep(std::time::Duration::from_millis(5));
        c.fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
        s_clone.release();
      }));
    }

    for h in handles {
      h.join().unwrap();
    }
  }

  #[test]
  fn test_semaphore_clone_shares_state() {
    let s1 = Semaphore::new(3);
    let s2 = s1.clone();
    s2.acquire();
    assert_eq!(s1.available(), 2);
  }

  #[test]
  fn test_semaphore_init_zero() {
    let s = Semaphore::new(0);
    assert!(!s.try_acquire());

    let s_clone = s.clone();
    thread::spawn(move || {
      thread::sleep(std::time::Duration::from_millis(20));
      s_clone.release();
    });

    s.acquire();
    assert_eq!(s.available(), 0);
  }
}
