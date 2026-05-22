use std::collections::VecDeque;
use std::sync::{Arc, Condvar, Mutex};

pub struct Channel<T> {
  inner: Arc<Inner<T>>,
}

struct Inner<T> {
  buffer: Mutex<Buffer<T>>,
  send_ready: Condvar,
  recv_ready: Condvar,
}

struct Buffer<T> {
  queue: VecDeque<T>,
  capacity: usize,
  closed: bool,
}

impl<T> Clone for Channel<T> {
  fn clone(&self) -> Self {
    Channel {
      inner: Arc::clone(&self.inner),
    }
  }
}

impl<T> Channel<T> {
  pub fn new(capacity: usize) -> Self {
    assert!(capacity > 0, "channel capacity must be > 0");
    Channel {
      inner: Arc::new(Inner {
        buffer: Mutex::new(Buffer {
          queue: VecDeque::with_capacity(capacity),
          capacity,
          closed: false,
        }),
        send_ready: Condvar::new(),
        recv_ready: Condvar::new(),
      }),
    }
  }

  pub fn send(&self, value: T) -> Result<(), T> {
    let mut buffer = self.inner.buffer.lock().unwrap();
    loop {
      if buffer.closed {
        return Err(value);
      }
      if buffer.queue.len() < buffer.capacity {
        buffer.queue.push_back(value);
        self.inner.recv_ready.notify_one();
        return Ok(());
      }
      buffer = self.inner.send_ready.wait(buffer).unwrap();
    }
  }

  pub fn recv(&self) -> Option<T> {
    let mut buffer = self.inner.buffer.lock().unwrap();
    loop {
      if let Some(value) = buffer.queue.pop_front() {
        self.inner.send_ready.notify_one();
        return Some(value);
      }
      if buffer.closed {
        return None;
      }
      buffer = self.inner.recv_ready.wait(buffer).unwrap();
    }
  }

  pub fn try_send(&self, value: T) -> Result<(), T> {
    let mut buffer = self.inner.buffer.lock().unwrap();
    if buffer.closed {
      return Err(value);
    }
    if buffer.queue.len() < buffer.capacity {
      buffer.queue.push_back(value);
      self.inner.recv_ready.notify_one();
      Ok(())
    } else {
      Err(value)
    }
  }

  pub fn try_recv(&self) -> Option<T> {
    let mut buffer = self.inner.buffer.lock().unwrap();
    let value = buffer.queue.pop_front();
    if value.is_some() {
      self.inner.send_ready.notify_one();
    }
    value
  }

  pub fn close(&self) {
    let mut buffer = self.inner.buffer.lock().unwrap();
    buffer.closed = true;
    self.inner.send_ready.notify_all();
    self.inner.recv_ready.notify_all();
  }

  pub fn len(&self) -> usize {
    self.inner.buffer.lock().unwrap().queue.len()
  }

  pub fn is_empty(&self) -> bool {
    self.inner.buffer.lock().unwrap().queue.is_empty()
  }

  pub fn is_closed(&self) -> bool {
    self.inner.buffer.lock().unwrap().closed
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::sync::Barrier;
  use std::thread;

  #[test]
  fn test_channel_send_recv_single() {
    let ch = Channel::new(1);
    assert!(ch.send(42).is_ok());
    assert_eq!(ch.recv(), Some(42));
  }

  #[test]
  fn test_channel_fifo_order() {
    let ch = Channel::new(3);
    ch.send(1).unwrap();
    ch.send(2).unwrap();
    ch.send(3).unwrap();
    assert_eq!(ch.recv(), Some(1));
    assert_eq!(ch.recv(), Some(2));
    assert_eq!(ch.recv(), Some(3));
  }

  #[test]
  fn test_channel_send_blocks_when_full() {
    let ch = Channel::new(1);
    ch.send(1).unwrap();

    let ch_clone = ch.clone();
    let barrier = Arc::new(Barrier::new(2));
    let b = Arc::clone(&barrier);

    let handle = thread::spawn(move || {
      b.wait();
      ch_clone.recv();
    });

    barrier.wait();
    let result = ch.send(2);
    handle.join().unwrap();

    assert!(result.is_ok());
  }

  #[test]
  fn test_channel_recv_blocks_when_empty() {
    let ch = Channel::<i32>::new(1);

    let ch_clone = ch.clone();
    let barrier = Arc::new(Barrier::new(2));
    let b = Arc::clone(&barrier);

    let handle = thread::spawn(move || {
      b.wait();
      thread::sleep(std::time::Duration::from_millis(50));
      ch_clone.send(99).unwrap();
    });

    barrier.wait();
    let result = ch.recv();
    handle.join().unwrap();

    assert_eq!(result, Some(99));
  }

  #[test]
  fn test_channel_try_send_recv() {
    let ch = Channel::new(1);
    assert!(ch.try_send(7).is_ok());
    assert!(ch.try_send(8).is_err());
    assert_eq!(ch.try_recv(), Some(7));
    assert_eq!(ch.try_recv(), None);
  }

  #[test]
  fn test_channel_close() {
    let ch = Channel::new(2);
    ch.send(1).unwrap();
    ch.send(2).unwrap();
    ch.close();

    assert!(ch.is_closed());
    assert_eq!(ch.send(3), Err(3));
    assert_eq!(ch.recv(), Some(1));
    assert_eq!(ch.recv(), Some(2));
    assert_eq!(ch.recv(), None);
  }

  #[test]
  fn test_channel_close_wakes_receivers() {
    let ch = Channel::<i32>::new(1);
    let ch_clone = ch.clone();
    let barrier = Arc::new(Barrier::new(2));
    let b = Arc::clone(&barrier);

    let handle = thread::spawn(move || {
      b.wait();
      assert_eq!(ch_clone.recv(), None);
    });

    barrier.wait();
    thread::sleep(std::time::Duration::from_millis(10));
    ch.close();
    handle.join().unwrap();
  }

  #[test]
  fn test_channel_mpsc() {
    let ch = Channel::new(2);
    let n_senders = 4;
    let n_per_sender = 100;
    let total = n_senders * n_per_sender;
    let barrier = Arc::new(Barrier::new(n_senders + 2));

    let mut sender_handles = Vec::new();
    for i in 0..n_senders {
      let ch_clone = ch.clone();
      let b = Arc::clone(&barrier);
      sender_handles.push(thread::spawn(move || {
        b.wait();
        for j in 0..n_per_sender {
          let value = i * n_per_sender + j;
          ch_clone.send(value).unwrap();
        }
      }));
    }

    let ch_recv = ch.clone();
    let b_recv = Arc::clone(&barrier);
    let recv_handle = thread::spawn(move || {
      let mut received = Vec::new();
      b_recv.wait();
      for _ in 0..total {
        received.push(ch_recv.recv().unwrap());
      }
      received
    });

    barrier.wait();
    let received = recv_handle.join().unwrap();
    for h in sender_handles {
      h.join().unwrap();
    }

    let mut received = received;
    received.sort();
    let expected: Vec<usize> = (0..total).collect();
    assert_eq!(received, expected);
  }

  #[test]
  fn test_channel_mpsc_variable_capacity() {
    for capacity in [1, 2, 4, 8, 16, 32] {
      let ch = Channel::new(capacity);
      let n = 200;
      let n_threads = 4;
      let total = n_threads * n;

      let barrier = Arc::new(Barrier::new(n_threads + 2));
      let mut sender_handles = Vec::new();

      for tid in 0..n_threads {
        let ch_clone = ch.clone();
        let b = Arc::clone(&barrier);
        sender_handles.push(thread::spawn(move || {
          b.wait();
          for i in 0..n {
            ch_clone.send(tid * n + i).unwrap();
          }
        }));
      }

      let ch_recv = ch.clone();
      let b_recv = Arc::clone(&barrier);
      let recv_handle = thread::spawn(move || {
        let mut received = Vec::new();
        b_recv.wait();
        for _ in 0..total {
          received.push(ch_recv.recv().unwrap());
        }
        received
      });

      barrier.wait();
      let mut received = recv_handle.join().unwrap();
      for h in sender_handles {
        h.join().unwrap();
      }

      received.sort();
      let expected: Vec<usize> = (0..total).collect();
      assert_eq!(received, expected);
    }
  }

  #[test]
  fn test_channel_len() {
    let ch = Channel::new(5);
    assert!(ch.is_empty());
    assert_eq!(ch.len(), 0);
    ch.send(1).unwrap();
    assert_eq!(ch.len(), 1);
    ch.send(2).unwrap();
    assert_eq!(ch.len(), 2);
    ch.recv();
    assert_eq!(ch.len(), 1);
  }
}
