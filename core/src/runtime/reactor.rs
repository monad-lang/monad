use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use super::scheduler::{QueuePair, Task};

#[cfg(target_os = "linux")]
use libc::{
  EFD_CLOEXEC, EFD_NONBLOCK, EPOLL_CTL_ADD, EPOLL_CTL_DEL, EPOLLIN, EPOLLOUT, epoll_create1,
  epoll_ctl, epoll_event, epoll_wait, eventfd, eventfd_t, read, write,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Interest {
  Read,
  Write,
}

#[cfg(target_os = "linux")]
impl Interest {
  fn to_epoll(self) -> u32 {
    match self {
      Interest::Read => EPOLLIN as u32,
      Interest::Write => EPOLLOUT as u32,
    }
  }
}

type Callback = Box<dyn FnOnce() + Send + 'static>;

#[cfg(target_os = "linux")]
const WAKUP_TOKEN: u64 = u64::MAX;

struct TimerEntry {
  deadline: Instant,
  id: u64,
}

impl Eq for TimerEntry {}
impl PartialEq for TimerEntry {
  fn eq(&self, other: &Self) -> bool {
    self.deadline == other.deadline
  }
}
impl PartialOrd for TimerEntry {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}
impl Ord for TimerEntry {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.deadline.cmp(&other.deadline)
  }
}

pub struct Reactor {
  inner: Arc<ReactorInner>,
}

struct ReactorInner {
  epoll_fd: i32,
  wake_fd: i32,
  queues: Arc<QueuePair>,
  registrations: Mutex<HashMap<u64, Callback>>,
  timer_heap: Mutex<BinaryHeap<Reverse<TimerEntry>>>,
  timer_by_id: Mutex<HashMap<u64, Instant>>,
  next_token: AtomicU64,
  shutdown: Arc<AtomicBool>,
}

impl Clone for Reactor {
  fn clone(&self) -> Self {
    Reactor {
      inner: Arc::clone(&self.inner),
    }
  }
}

impl Reactor {
  pub fn new(queues: Arc<QueuePair>, shutdown: Arc<AtomicBool>) -> Reactor {
    #[cfg(target_os = "linux")]
    let (epoll_fd, wake_fd) = unsafe {
      let epfd = epoll_create1(0);
      if epfd < 0 {
        panic!("epoll_create1 failed");
      }

      let wfd = eventfd(0, EFD_NONBLOCK | EFD_CLOEXEC);
      if wfd < 0 {
        libc::close(epfd);
        panic!("eventfd failed");
      }

      let mut event = epoll_event {
        events: EPOLLIN as u32,
        u64: WAKUP_TOKEN,
      };
      if epoll_ctl(epfd, EPOLL_CTL_ADD, wfd, &mut event) != 0 {
        libc::close(wfd);
        libc::close(epfd);
        panic!("epoll_ctl ADD for wake_fd failed");
      }

      (epfd, wfd)
    };

    #[cfg(not(target_os = "linux"))]
    let (epoll_fd, wake_fd) = (-1, -1);

    Reactor {
      inner: Arc::new(ReactorInner {
        epoll_fd,
        wake_fd,
        queues,
        registrations: Mutex::new(HashMap::new()),
        timer_heap: Mutex::new(BinaryHeap::new()),
        timer_by_id: Mutex::new(HashMap::new()),
        next_token: AtomicU64::new(1),
        shutdown,
      }),
    }
  }

  pub fn register(&self, fd: i32, interest: Interest, callback: Callback) -> u64 {
    let token = self.inner.next_token.fetch_add(1, Ordering::SeqCst);

    #[cfg(target_os = "linux")]
    {
      let mut event = epoll_event {
        events: interest.to_epoll(),
        u64: token,
      };

      let ret = unsafe { epoll_ctl(self.inner.epoll_fd, EPOLL_CTL_ADD, fd, &mut event) };
      if ret != 0 {
        panic!("epoll_ctl ADD failed: fd={}", fd);
      }
    }

    #[cfg(not(target_os = "linux"))]
    {
      let _ = fd;
      let _ = interest;
    }

    self
      .inner
      .registrations
      .lock()
      .unwrap()
      .insert(token, callback);
    token
  }

  pub fn deregister(&self, fd: i32, token: u64) {
    #[cfg(target_os = "linux")]
    {
      let mut event = epoll_event {
        events: 0,
        u64: token,
      };
      unsafe {
        epoll_ctl(self.inner.epoll_fd, EPOLL_CTL_DEL, fd, &mut event);
      }
    }

    #[cfg(not(target_os = "linux"))]
    {
      let _ = fd;
    }

    self.inner.registrations.lock().unwrap().remove(&token);
  }

  pub fn schedule_timer(&self, delay: Duration, callback: Callback) -> u64 {
    let id = self.inner.next_token.fetch_add(1, Ordering::SeqCst);
    let deadline = Instant::now() + delay;

    let entry = TimerEntry { deadline, id };

    self.inner.timer_by_id.lock().unwrap().insert(id, deadline);

    let mut heap = self.inner.timer_heap.lock().unwrap();
    self
      .inner
      .registrations
      .lock()
      .unwrap()
      .insert(id, callback);
    heap.push(Reverse(entry));

    id
  }

  pub fn cancel_timer(&self, id: u64) {
    self.inner.registrations.lock().unwrap().remove(&id);
    self.inner.timer_by_id.lock().unwrap().remove(&id);
  }

  pub fn wake(&self) {
    #[cfg(target_os = "linux")]
    {
      let val: eventfd_t = 1;
      let ret = unsafe {
        write(
          self.inner.wake_fd,
          &val as *const eventfd_t as *const libc::c_void,
          8,
        )
      };
      if ret != 8 {
        eprintln!("reactor::wake: write to eventfd returned {}", ret);
      }
    }
  }

  fn next_timeout_ms(&self) -> i32 {
    let heap = self.inner.timer_heap.lock().unwrap();
    if let Some(Reverse(entry)) = heap.peek() {
      let now = Instant::now();
      if entry.deadline <= now {
        return 0;
      }
      let duration = entry.deadline.duration_since(now);
      let millis = duration.as_millis();
      if millis > i32::MAX as u128 {
        i32::MAX
      } else {
        millis as i32
      }
    } else {
      -1
    }
  }

  fn expire_timers(&self) -> Vec<Callback> {
    let mut callbacks = Vec::new();
    let now = Instant::now();
    let mut heap = self.inner.timer_heap.lock().unwrap();

    loop {
      let should_pop = heap.peek().map_or(false, |Reverse(e)| e.deadline <= now);
      if !should_pop {
        break;
      }
      let Reverse(entry) = heap.pop().unwrap();
      if let Some(cb) = self.inner.registrations.lock().unwrap().remove(&entry.id) {
        self.inner.timer_by_id.lock().unwrap().remove(&entry.id);
        callbacks.push(cb);
      }
    }

    callbacks
  }

  pub fn run(&self) {
    #[cfg(target_os = "linux")]
    {
      let mut events: [epoll_event; 64] = unsafe { std::mem::zeroed() };

      loop {
        if self.inner.shutdown.load(Ordering::SeqCst) {
          break;
        }

        let timeout = self.next_timeout_ms();
        let n = unsafe {
          epoll_wait(
            self.inner.epoll_fd,
            events.as_mut_ptr(),
            events.len() as i32,
            timeout,
          )
        };

        if n < 0 {
          let err = std::io::Error::last_os_error();
          if err.kind() == std::io::ErrorKind::Interrupted {
            continue;
          }
          panic!("epoll_wait failed: {:?}", err);
        }

        for i in 0..n as usize {
          let token = events[i].u64;
          if token == WAKUP_TOKEN {
            let mut buf: eventfd_t = 0;
            unsafe {
              read(
                self.inner.wake_fd,
                &mut buf as *mut eventfd_t as *mut libc::c_void,
                8,
              );
            }
            continue;
          }
          if let Some(cb) = self.inner.registrations.lock().unwrap().remove(&token) {
            self.push_callback(cb);
          }
        }

        for cb in self.expire_timers() {
          self.push_callback(cb);
        }
      }
    }

    #[cfg(not(target_os = "linux"))]
    {
      eprintln!("reactor: epoll not available on this platform");
    }
  }

  fn push_callback(&self, cb: Callback) {
    self
      .inner
      .queues
      .global
      .lock()
      .unwrap()
      .push_back(Task::Run(cb));
    let (lock, cvar) = &*self.inner.queues.idle;
    let count = lock.lock().unwrap();
    if *count > 0 {
      cvar.notify_one();
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::runtime::scheduler::Scheduler;
  use std::sync::mpsc;
  use std::thread;

  #[test]
  #[cfg(target_os = "linux")]
  fn test_epoll_wait_timeout_no_fds() {
    let epfd = unsafe { epoll_create1(0) };
    assert!(epfd >= 0, "epoll_create1 failed");

    let mut events: [epoll_event; 1] = unsafe { std::mem::zeroed() };
    let start = Instant::now();
    let n = unsafe { epoll_wait(epfd, events.as_mut_ptr(), 1, 100) };
    let elapsed = start.elapsed();

    assert!(n == 0, "expected 0 events, got {}", n);
    assert!(
      elapsed >= Duration::from_millis(90),
      "expected >= 90ms elapsed, got {:?}",
      elapsed
    );
    unsafe { libc::close(epfd) };
  }

  #[test]
  fn test_reactor_socket_read_ready() {
    #[cfg(target_os = "linux")]
    {
      let sched = Scheduler::with_workers(1);
      let shutdown = Arc::new(AtomicBool::new(false));
      let reactor = Reactor::new(sched.queues(), Arc::clone(&shutdown));

      let mut fds = [0i32; 2];
      unsafe { libc::socketpair(libc::AF_UNIX, libc::SOCK_STREAM, 0, fds.as_mut_ptr()) };

      let (tx, rx) = mpsc::channel::<bool>();

      reactor.register(
        fds[0],
        Interest::Read,
        Box::new(move || {
          tx.send(true).unwrap();
        }),
      );

      let reactor_handle = thread::spawn({
        let reactor = reactor.clone();
        move || {
          reactor.run();
        }
      });

      unsafe { libc::write(fds[1], &42u8 as *const u8 as *const libc::c_void, 1) };

      assert!(rx.recv_timeout(Duration::from_secs(2)).unwrap());

      shutdown.store(true, Ordering::SeqCst);
      reactor.wake();
      reactor_handle.join().unwrap();

      unsafe {
        libc::close(fds[0]);
        libc::close(fds[1]);
      }
    }
  }

  #[test]
  fn test_reactor_socket_write_ready() {
    #[cfg(target_os = "linux")]
    {
      let sched = Scheduler::with_workers(1);
      let shutdown = Arc::new(AtomicBool::new(false));
      let reactor = Reactor::new(sched.queues(), Arc::clone(&shutdown));

      let mut fds = [0i32; 2];
      unsafe { libc::socketpair(libc::AF_UNIX, libc::SOCK_STREAM, 0, fds.as_mut_ptr()) };

      let (tx, rx) = mpsc::channel::<bool>();

      reactor.register(
        fds[1],
        Interest::Write,
        Box::new(move || {
          tx.send(true).unwrap();
        }),
      );

      let reactor_handle = thread::spawn({
        let reactor = reactor.clone();
        move || {
          reactor.run();
        }
      });

      assert!(rx.recv_timeout(Duration::from_secs(2)).unwrap());

      shutdown.store(true, Ordering::SeqCst);
      reactor.wake();
      reactor_handle.join().unwrap();

      unsafe {
        libc::close(fds[0]);
        libc::close(fds[1]);
      }
    }
  }

  #[test]
  #[cfg(target_os = "linux")]
  fn test_reactor_timer_fires() {
    let sched = Scheduler::with_workers(1);
    let shutdown = Arc::new(AtomicBool::new(false));
    let reactor = Reactor::new(sched.queues(), Arc::clone(&shutdown));

    let (tx, rx) = mpsc::channel::<bool>();

    reactor.schedule_timer(
      Duration::from_millis(100),
      Box::new(move || {
        tx.send(true).unwrap();
      }),
    );

    let reactor_handle = thread::spawn({
      let reactor = reactor.clone();
      move || {
        reactor.run();
      }
    });

    let result = rx.recv_timeout(Duration::from_secs(5));
    assert!(result.unwrap());

    shutdown.store(true, Ordering::SeqCst);
    reactor.wake();
    reactor_handle.join().unwrap();
  }

  #[test]
  #[cfg(target_os = "linux")]
  fn test_reactor_timer_order() {
    let sched = Scheduler::with_workers(1);
    let shutdown = Arc::new(AtomicBool::new(false));
    let reactor = Reactor::new(sched.queues(), Arc::clone(&shutdown));

    let results = Arc::new(Mutex::new(Vec::new()));

    let r1 = Arc::clone(&results);
    reactor.schedule_timer(
      Duration::from_millis(30),
      Box::new(move || {
        r1.lock().unwrap().push(2);
      }),
    );

    let r2 = Arc::clone(&results);
    reactor.schedule_timer(
      Duration::from_millis(10),
      Box::new(move || {
        r2.lock().unwrap().push(1);
      }),
    );

    let reactor_handle = thread::spawn({
      let reactor = reactor.clone();
      move || {
        reactor.run();
      }
    });

    thread::sleep(Duration::from_millis(100));

    shutdown.store(true, Ordering::SeqCst);
    reactor.wake();
    reactor_handle.join().unwrap();

    let results = results.lock().unwrap();
    assert_eq!(*results, vec![1, 2], "timers should fire in deadline order");
  }
}
