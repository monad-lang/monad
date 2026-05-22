use std::sync::mpsc::{self, Sender};
use std::thread::{self, JoinHandle};

use super::fiber::{Fiber, FiberState};

enum Task {
  Run(Box<dyn FnOnce() + Send + 'static>),
  Shutdown,
}

pub struct Scheduler {
  tx: Sender<Task>,
  worker: Option<JoinHandle<()>>,
}

impl Scheduler {
  pub fn new() -> Scheduler {
    let (tx, rx) = mpsc::channel::<Task>();
    let worker = thread::Builder::new()
      .name("monad-scheduler".into())
      .spawn(move || {
        while let Ok(task) = rx.recv() {
          match task {
            Task::Run(f) => f(),
            Task::Shutdown => break,
          }
        }
      })
      .expect("failed to spawn scheduler thread");

    Scheduler {
      tx,
      worker: Some(worker),
    }
  }

  pub fn spawn<F, T>(&self, f: F) -> Fiber<T>
  where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
  {
    let fiber = Fiber::<T>::new();
    let fiber_clone = fiber.clone();

    let task = Box::new(move || {
      fiber_clone.set_state(FiberState::Running);
      if fiber_clone.is_cancelled() {
        return;
      }
      let result = f();
      fiber_clone.set_result(result);
      fiber_clone.set_state(FiberState::Completed);
    });

    self
      .tx
      .send(Task::Run(task))
      .expect("scheduler worker has shut down");
    fiber
  }

  pub fn spawn_and_await<F, T>(&self, f: F) -> T
  where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
  {
    let fiber = self.spawn(f);
    fiber.wait()
  }

  pub fn shutdown(mut self) {
    let _ = self.tx.send(Task::Shutdown);
    if let Some(worker) = self.worker.take() {
      let _ = worker.join();
    }
  }
}

impl Drop for Scheduler {
  fn drop(&mut self) {
    let _ = self.tx.send(Task::Shutdown);
    if let Some(worker) = self.worker.take() {
      let _ = worker.join();
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_scheduler_spawn_and_await() {
    let scheduler = Scheduler::new();
    let result = scheduler.spawn_and_await(|| 42);
    assert_eq!(result, 42);
  }

  #[test]
  fn test_scheduler_spawn_multiple() {
    let scheduler = Scheduler::new();
    let fiber1 = scheduler.spawn(|| 10);
    let fiber2 = scheduler.spawn(|| 20);
    assert_eq!(fiber1.wait() + fiber2.wait(), 30);
  }

  #[test]
  fn test_scheduler_ordering_sequential() {
    let scheduler = Scheduler::new();
    let results = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));

    let r1 = results.clone();
    let f1 = scheduler.spawn(move || {
      r1.lock().unwrap().push(1);
      1
    });

    let r2 = results.clone();
    let f2 = scheduler.spawn(move || {
      r2.lock().unwrap().push(2);
      2
    });

    let r3 = results.clone();
    let f3 = scheduler.spawn(move || {
      r3.lock().unwrap().push(3);
      3
    });

    let _ = f1.wait();
    let _ = f2.wait();
    let _ = f3.wait();

    let results = results.lock().unwrap();
    assert_eq!(*results, vec![1, 2, 3]);
  }

  #[test]
  fn test_scheduler_cancel_fiber() {
    let scheduler = Scheduler::new();
    let fiber = scheduler.spawn(|| 42);
    fiber.cancel();
    assert!(fiber.is_cancelled());
  }

  #[test]
  fn test_scheduler_many_fibers() {
    let scheduler = Scheduler::new();
    let mut handles = Vec::new();
    for i in 0..100 {
      handles.push(scheduler.spawn(move || i * 2));
    }
    for (i, handle) in handles.into_iter().enumerate() {
      assert_eq!(handle.wait(), i * 2);
    }
  }
}
