use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::{self, JoinHandle};
use std::time::Duration;

use super::fiber::{Fiber, FiberState};

pub enum Task {
  Run(Box<dyn FnOnce() + Send + 'static>),
  Shutdown,
}

pub struct QueuePair {
  pub global: Arc<Mutex<VecDeque<Task>>>,
  pub idle: Arc<(Mutex<usize>, Condvar)>,
}

impl std::fmt::Debug for QueuePair {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("QueuePair").finish()
  }
}

pub struct Scheduler {
  queues: Arc<QueuePair>,
  all_locals: Arc<Vec<Arc<Mutex<VecDeque<Task>>>>>,
  shutdown: Arc<AtomicBool>,
  handles: Vec<JoinHandle<()>>,
}

fn worker_loop(
  id: usize,
  local: Arc<Mutex<VecDeque<Task>>>,
  global: Arc<Mutex<VecDeque<Task>>>,
  all_locals: Arc<Vec<Arc<Mutex<VecDeque<Task>>>>>,
  idle: Arc<(Mutex<usize>, Condvar)>,
  shutdown: Arc<AtomicBool>,
) {
  let n = all_locals.len();

  loop {
    if let Some(task) = local.lock().unwrap().pop_back() {
      match task {
        Task::Run(f) => f(),
        Task::Shutdown => return,
      }
      continue;
    }

    if let Some(task) = global.lock().unwrap().pop_front() {
      match task {
        Task::Run(f) => f(),
        Task::Shutdown => return,
      }
      continue;
    }

    let mut stolen = None;
    for i in 1..n {
      let victim = (id + i) % n;
      let mut q = all_locals[victim].lock().unwrap();
      if let Some(task) = q.pop_front() {
        stolen = Some(task);
        break;
      }
    }

    if let Some(task) = stolen {
      match task {
        Task::Run(f) => f(),
        Task::Shutdown => return,
      }
      continue;
    }

    if shutdown.load(Ordering::SeqCst) {
      return;
    }

    let (lock, cvar) = &*idle;
    let mut count = lock.lock().unwrap();
    *count += 1;

    let result = cvar.wait_timeout(count, Duration::from_millis(1)).unwrap();
    count = result.0;
    *count -= 1;
  }
}

impl Scheduler {
  pub fn new() -> Self {
    let n = thread::available_parallelism()
      .map(|p| p.get())
      .unwrap_or(4);
    Self::with_workers(n)
  }

  pub fn with_workers(num_workers: usize) -> Self {
    assert!(num_workers > 0, "must have at least 1 worker");

    let queues = Arc::new(QueuePair {
      global: Arc::new(Mutex::new(VecDeque::new())),
      idle: Arc::new((Mutex::new(0usize), Condvar::new())),
    });
    let shutdown = Arc::new(AtomicBool::new(false));

    let locals: Vec<Arc<Mutex<VecDeque<Task>>>> = (0..num_workers)
      .map(|_| Arc::new(Mutex::new(VecDeque::new())))
      .collect();
    let all_locals = Arc::new(locals.clone());

    let mut handles = Vec::with_capacity(num_workers);
    for id in 0..num_workers {
      let local = Arc::clone(&locals[id]);
      let global = Arc::clone(&queues.global);
      let all_locals = Arc::clone(&all_locals);
      let idle = Arc::clone(&queues.idle);
      let shutdown = Arc::clone(&shutdown);

      let handle = thread::Builder::new()
        .name(format!("monad-worker-{}", id))
        .spawn(move || {
          worker_loop(id, local, global, all_locals, idle, shutdown);
        })
        .expect("failed to spawn worker");

      handles.push(handle);
    }

    Scheduler {
      queues,
      all_locals,
      shutdown,
      handles,
    }
  }

  pub fn queues(&self) -> Arc<QueuePair> {
    Arc::clone(&self.queues)
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
      .queues
      .global
      .lock()
      .unwrap()
      .push_back(Task::Run(task));

    let (lock, cvar) = &*self.queues.idle;
    let idle_count = lock.lock().unwrap();
    if *idle_count > 0 {
      cvar.notify_one();
    }

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
    self.shutdown.store(true, Ordering::SeqCst);

    for local in self.all_locals.iter() {
      local.lock().unwrap().push_back(Task::Shutdown);
    }

    let (_, cvar) = &*self.queues.idle;
    cvar.notify_all();

    for handle in self.handles.drain(..) {
      let _ = handle.join();
    }
  }
}

impl Drop for Scheduler {
  fn drop(&mut self) {
    self.shutdown.store(true, Ordering::SeqCst);

    for local in self.all_locals.iter() {
      local.lock().unwrap().push_back(Task::Shutdown);
    }

    let (_, cvar) = &*self.queues.idle;
    cvar.notify_all();

    for handle in self.handles.drain(..) {
      let _ = handle.join();
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::collections::HashSet;

  #[test]
  fn test_scheduler_spawn_and_await() {
    let sched = Scheduler::with_workers(2);
    let result = sched.spawn_and_await(|| 42);
    assert_eq!(result, 42);
  }

  #[test]
  fn test_scheduler_spawn_multiple() {
    let sched = Scheduler::with_workers(2);
    let fiber1 = sched.spawn(|| 10);
    let fiber2 = sched.spawn(|| 20);
    assert_eq!(fiber1.wait(), 10);
    assert_eq!(fiber2.wait(), 20);
  }

  #[test]
  fn test_scheduler_cancel_fiber() {
    let sched = Scheduler::with_workers(1);
    let fiber = sched.spawn(|| 42);
    fiber.cancel();
    assert!(fiber.is_cancelled());
  }

  #[test]
  fn test_scheduler_many_fibers() {
    let sched = Scheduler::with_workers(4);
    let mut fibers = Vec::new();
    for i in 0..100 {
      fibers.push(sched.spawn(move || i * 2));
    }
    let mut results: Vec<i32> = fibers.into_iter().map(|f| f.wait()).collect();
    results.sort();
    let expected: Vec<i32> = (0..100).map(|i| i * 2).collect();
    assert_eq!(results, expected);
  }

  #[test]
  fn test_scheduler_parallel_execution() {
    let sched = Scheduler::with_workers(4);
    let thread_ids = Arc::new(Mutex::new(HashSet::new()));

    let mut fibers = Vec::new();
    for _ in 0..100 {
      let ids = Arc::clone(&thread_ids);
      fibers.push(sched.spawn(move || {
        thread::sleep(Duration::from_micros(50));
        ids.lock().unwrap().insert(thread::current().id());
      }));
    }

    for f in fibers {
      f.wait();
    }

    let ids = thread_ids.lock().unwrap();
    assert!(
      ids.len() >= 2,
      "expected at least 2 distinct thread IDs, got {:?}",
      *ids
    );
  }

  #[test]
  fn test_scheduler_work_distribution() {
    let sched = Scheduler::with_workers(4);
    let counter = Arc::new(Mutex::new(0usize));
    let n_tasks = 50;

    let mut fibers = Vec::new();
    for _ in 0..n_tasks {
      let c = Arc::clone(&counter);
      fibers.push(sched.spawn(move || {
        *c.lock().unwrap() += 1;
      }));
    }

    for f in fibers {
      f.wait();
    }

    assert_eq!(*counter.lock().unwrap(), n_tasks);
  }

  #[test]
  fn test_scheduler_shutdown() {
    let sched = Scheduler::with_workers(2);
    let fiber = sched.spawn(|| 7);
    assert_eq!(fiber.wait(), 7);
    sched.shutdown();
  }

  #[test]
  fn test_scheduler_drop_shutdown() {
    let sched = Scheduler::with_workers(2);
    let fiber = sched.spawn(|| 7);
    assert_eq!(fiber.wait(), 7);
    drop(sched);
  }

  #[test]
  fn test_scheduler_single_worker() {
    let sched = Scheduler::with_workers(1);
    let results = Arc::new(Mutex::new(Vec::new()));

    let r = Arc::clone(&results);
    let f1 = sched.spawn(move || {
      r.lock().unwrap().push(1);
    });

    let r = Arc::clone(&results);
    let f2 = sched.spawn(move || {
      r.lock().unwrap().push(2);
    });

    let r = Arc::clone(&results);
    let f3 = sched.spawn(move || {
      r.lock().unwrap().push(3);
    });

    f1.wait();
    f2.wait();
    f3.wait();

    let results = results.lock().unwrap();
    assert_eq!(*results, vec![1, 2, 3]);
  }
}
