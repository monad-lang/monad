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
  table.next_id += 1;
  table.objects.insert(id, Box::new(obj));
  id
}

pub fn with<T: 'static, R>(id: u64, f: impl FnOnce(&T) -> R) -> Option<R> {
  let table = HANDLE_TABLE.lock().expect("handle table poisoned");
  table
    .objects
    .get(&id)
    .and_then(|obj| obj.downcast_ref::<T>().map(f))
}

pub fn take<T: 'static>(id: u64) -> Option<T> {
  let mut table = HANDLE_TABLE.lock().expect("handle table poisoned");
  table
    .objects
    .remove(&id)
    .and_then(|obj| obj.downcast::<T>().ok().map(|b| *b))
}

pub fn drop_handle(id: u64) {
  let mut table = HANDLE_TABLE.lock().expect("handle table poisoned");
  table.objects.remove(&id);
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
}
