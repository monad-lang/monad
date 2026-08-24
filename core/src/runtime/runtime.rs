use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, OnceLock};
use std::thread::{self, JoinHandle};

use super::fiber::Fiber;
use super::reactor::Reactor;

#[cfg(test)]
use super::reactor::Interest;
use super::scheduler::{QueuePair, Scheduler};

static GLOBAL_QUEUES: OnceLock<Arc<QueuePair>> = OnceLock::new();

pub struct Runtime {
  scheduler: Scheduler,
  reactor: Reactor,
  reactor_thread: Option<JoinHandle<()>>,
  shutdown: Arc<AtomicBool>,
}

impl Runtime {
  pub fn new(num_workers: usize) -> Self {
    let scheduler = Scheduler::with_workers(num_workers);
    let shutdown = Arc::new(AtomicBool::new(false));
    let queues = scheduler.queues();

    let reactor = Reactor::new(queues.clone(), Arc::clone(&shutdown));
    let reactor_clone = reactor.clone();
    let reactor_thread = thread::Builder::new()
      .name("monad-reactor".into())
      .spawn(move || {
        reactor_clone.run();
      })
      .ok();

    Runtime {
      scheduler,
      reactor,
      reactor_thread,
      shutdown,
    }
  }

  pub fn default_workers() -> Self {
    let n = thread::available_parallelism()
      .map(|p| p.get())
      .unwrap_or(4);
    Self::new(n)
  }

  pub fn init_global(num_workers: usize) {
    let rt = Self::new(num_workers);
    GLOBAL_QUEUES
      .set(rt.scheduler.queues())
      .expect("global runtime already initialized");
    std::mem::forget(rt);
  }

  pub fn queues() -> Option<Arc<QueuePair>> {
    GLOBAL_QUEUES.get().cloned()
  }

  pub fn reactor(&self) -> &Reactor {
    &self.reactor
  }

  pub fn spawn<F, T>(&self, f: F) -> Fiber<T>
  where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
  {
    self.scheduler.spawn(f)
  }

  pub fn spawn_and_await<F, T>(&self, f: F) -> T
  where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
  {
    self.scheduler.spawn_and_await(f)
  }

  fn stop_reactor(&self) {
    self.shutdown.store(true, Ordering::SeqCst);
    self.reactor.wake();
  }

  pub fn shutdown(mut self) {
    self.stop_reactor();
    if let Some(handle) = self.reactor_thread.take() {
      let _ = handle.join();
    }
  }
}

impl Drop for Runtime {
  fn drop(&mut self) {
    self.stop_reactor();
    if let Some(handle) = self.reactor_thread.take() {
      let _ = handle.join();
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::sync::mpsc;
  use std::time::Duration;

  #[test]
  fn test_runtime_spawn_and_await() {
    let rt = Runtime::new(2);
    let result = rt.spawn_and_await(|| 42);
    assert_eq!(result, 42);
    rt.shutdown();
  }

  #[test]
  fn test_runtime_spawn_multiple() {
    let rt = Runtime::new(2);
    let f1 = rt.spawn(|| 10);
    let f2 = rt.spawn(|| 20);
    assert_eq!(f1.wait(), Some(10));
    assert_eq!(f2.wait(), Some(20));
    rt.shutdown();
  }

  #[test]
  fn test_runtime_default_workers() {
    let rt = Runtime::default_workers();
    let result = rt.spawn_and_await(|| 99);
    assert_eq!(result, 99);
    rt.shutdown();
  }

  #[test]
  fn test_runtime_cancel_fiber() {
    let rt = Runtime::new(1);
    let fiber = rt.spawn(|| 7);
    fiber.cancel();
    assert!(fiber.is_cancelled());
    rt.shutdown();
  }

  #[test]
  fn test_runtime_integration_basic() {
    let rt = Runtime::new(2);
    let mut fibers = Vec::new();
    for i in 0..50 {
      fibers.push(rt.spawn(move || i * 2));
    }
    let mut results: Vec<i32> = fibers.into_iter().map(|f| f.wait().unwrap()).collect();
    results.sort();
    let expected: Vec<i32> = (0..50).map(|i| i * 2).collect();
    assert_eq!(results, expected);
    rt.shutdown();
  }

  #[test]
  fn test_runtime_shutdown() {
    let rt = Runtime::new(2);
    let fiber = rt.spawn(|| 7);
    assert_eq!(fiber.wait(), Some(7));
    rt.shutdown();
  }

  #[test]
  fn test_runtime_drop_shutdown() {
    let rt = Runtime::new(2);
    let fiber = rt.spawn(|| 7);
    assert_eq!(fiber.wait(), Some(7));
    drop(rt);
  }

  #[test]
  fn test_runtime_init_global() {
    Runtime::init_global(2);
    let queues = Runtime::queues();
    assert!(queues.is_some());
  }

  #[test]
  #[cfg(target_os = "linux")]
  fn test_runtime_reactor_integration() {
    let rt = Runtime::new(2);

    let mut fds = [0i32; 2];
    unsafe { libc::socketpair(libc::AF_UNIX, libc::SOCK_STREAM, 0, fds.as_mut_ptr()) };

    let (tx, rx) = mpsc::channel::<bool>();

    let reactor = rt.reactor.clone();

    reactor.register(
      fds[0],
      Interest::Read,
      Box::new(move || {
        tx.send(true).unwrap();
      }),
    );

    unsafe {
      libc::write(fds[1], &42u8 as *const u8 as *const libc::c_void, 1);
    }

    let result = rx.recv_timeout(Duration::from_secs(2));
    assert!(result.unwrap());

    unsafe {
      libc::close(fds[0]);
      libc::close(fds[1]);
    }
    rt.shutdown();
  }
}
