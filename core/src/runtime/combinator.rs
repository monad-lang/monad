use std::thread;
use std::time::{Duration, Instant};

use super::fiber::{Fiber, FiberState};
use super::runtime::Runtime;

pub fn all<T: Send + 'static>(fibers: Vec<Fiber<T>>) -> Vec<T> {
  fibers.into_iter().map(|f| f.wait()).collect()
}

pub fn race<T: Send + 'static>(_rt: &Runtime, fibers: Vec<Fiber<T>>) -> Option<T> {
  if fibers.is_empty() {
    return None;
  }
  loop {
    for f in &fibers {
      if f.state() == FiberState::Completed {
        return Some(f.clone().wait());
      }
    }
    thread::yield_now();
  }
}

pub fn timeout<T: Send + 'static>(_rt: &Runtime, fiber: Fiber<T>, dur: Duration) -> Option<T> {
  let deadline = Instant::now() + dur;
  loop {
    if fiber.state() == FiberState::Completed {
      return Some(fiber.wait());
    }
    if Instant::now() >= deadline {
      return None;
    }
    thread::yield_now();
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_all_collects_results() {
    let rt = Runtime::new(2);
    let f1 = rt.spawn(|| 1);
    let f2 = rt.spawn(|| 2);
    let f3 = rt.spawn(|| 3);
    let results = all(vec![f1, f2, f3]);
    assert_eq!(results, vec![1, 2, 3]);
    rt.shutdown();
  }

  #[test]
  fn test_all_empty() {
    let rt = Runtime::new(2);
    let results: Vec<i32> = all(vec![]);
    assert!(results.is_empty());
    rt.shutdown();
  }

  #[test]
  fn test_all_preserves_order() {
    let rt = Runtime::new(2);
    let f1 = rt.spawn(|| 10);
    let f2 = rt.spawn(|| 20);
    let f3 = rt.spawn(|| 30);
    let results = all(vec![f1, f2, f3]);
    assert_eq!(results, vec![10, 20, 30]);
    rt.shutdown();
  }

  #[test]
  fn test_race_returns_result() {
    let rt = Runtime::new(2);
    let f1 = rt.spawn(|| 42);
    let f2 = rt.spawn(|| 99);
    let winner = race(&rt, vec![f1, f2]);
    assert!(winner == Some(42) || winner == Some(99));
    rt.shutdown();
  }

  #[test]
  fn test_race_empty() {
    let rt = Runtime::new(2);
    let result: Option<i32> = race(&rt, vec![]);
    assert_eq!(result, None);
    rt.shutdown();
  }

  #[test]
  fn test_race_single() {
    let rt = Runtime::new(2);
    let f = rt.spawn(|| 42);
    let result = race(&rt, vec![f]);
    assert_eq!(result, Some(42));
    rt.shutdown();
  }

  #[test]
  fn test_race_all_complete_fast() {
    let rt = Runtime::new(4);
    let mut fibers = Vec::new();
    for i in 0..10 {
      fibers.push(rt.spawn(move || i));
    }
    let winner = race(&rt, fibers);
    assert!(winner.is_some());
    let w = winner.unwrap();
    assert!(w >= 0 && w < 10);
    rt.shutdown();
  }

  #[test]
  fn test_timeout_success() {
    let rt = Runtime::new(2);
    let f = rt.spawn(|| 42);
    let result = timeout(&rt, f, Duration::from_secs(5));
    assert_eq!(result, Some(42));
    rt.shutdown();
  }

  #[test]
  fn test_timeout_expires_simple() {
    let rt = Runtime::new(2);
    let f = rt.spawn(|| {
      thread::sleep(Duration::from_secs(1));
      99
    });
    let result = timeout(&rt, f, Duration::from_millis(1));
    assert_eq!(result, None);
    rt.shutdown();
  }
}
