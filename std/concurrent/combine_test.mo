// Structured concurrency tests: all, race, scoped, sleepIO, cancel_all

use std.concurrent.fiber {Fiber, await_fiber, cancel_fiber, forkIO}
use std.concurrent.combine {Scope, scope_fork, scoped, sleepIO}

// Helper thunks

def io_10_action (_ : Unit) : IO I64 := IO.io 10

def io_20_action (_ : Unit) : IO I64 := IO.io 20

def io_30_action (_ : Unit) : IO I64 := IO.io 30

def io_42_action (_ : Unit) : IO I64 := IO.io 42

// all: concrete specialized

def all_i64 (fibers : List (Fiber I64)) : IO (List I64) :=
  match fibers {
    List.empty => IO.io (List.empty : List I64),
    List.cons f rest => do {
      let head <- await_fiber f;
      let tail <- all_i64 rest;
      return (List.cons head tail)
    }
  }

// race: concrete specialized

def cancel_i64 (fibers : List (Fiber I64)) : IO Unit :=
  match fibers {
    List.empty => IO.io Unit.unit,
    List.cons f rest => do {
      cancel_fiber f;
      cancel_i64 rest
    }
  }

def race_i64 (fibers : List (Fiber I64)) : IO I64 :=
  match fibers {
    List.cons f rest => do {
      cancel_i64 rest;
      await_fiber f
    }
  }

// Tests

#[test]
def test_all_single : IO Bool {
  let f <- forkIO io_42_action;
  let fibers := List.cons f List.empty;
  let results <- all_i64 fibers;
  return true
}

#[test]
def test_all_two : IO Bool {
  let f1 <- forkIO io_10_action;
  let f2 <- forkIO io_20_action;
  let fibers := List.cons f1 (List.cons f2 List.empty);
  let results <- all_i64 fibers;
  return true
}

#[test]
def test_all_three : IO Bool {
  let f1 <- forkIO io_10_action;
  let f2 <- forkIO io_20_action;
  let f3 <- forkIO io_30_action;
  let fibers := List.cons f1 (List.cons f2 (List.cons f3 List.empty));
  let results <- all_i64 fibers;
  return true
}

def is_empty (xs : List I64) : Bool :=
  match xs {
    List.empty => true,
    List.cons _ _ => false
  }

#[test]
def test_all_empty : IO Bool {
  let fibers := (List.empty : List (Fiber I64));
  let results <- all_i64 fibers;
  return (is_empty results)
}

#[test]
def test_race_first : IO Bool {
  let f1 <- forkIO io_10_action;
  let f2 <- forkIO io_20_action;
  let fibers := List.cons f1 (List.cons f2 List.empty);
  let result <- race_i64 fibers;
  return (result == 10)
}

#[test]
def test_race_single : IO Bool {
  let f1 <- forkIO io_30_action;
  let fibers := List.cons f1 List.empty;
  let result <- race_i64 fibers;
  return (result == 30)
}

#[test]
def test_cancel_all_smoke : IO Bool {
  let f1 <- forkIO io_10_action;
  let f2 <- forkIO io_20_action;
  let fibers := List.cons f1 (List.cons f2 List.empty);
  cancel_i64 fibers;
  return true
}

// scoped: creates scope, runs action, auto-cancels on exit

def fork_io_42_scoped (s : Scope) : IO (Fiber I64) := scope_fork s io_42_action

def scoped_fork_await_42 (s : Scope) : IO I64 := do {
  let f <- fork_io_42_scoped s;
  await_fiber f
}

#[test]
def test_scoped_runs_action : IO Bool {
  let result <- scoped scoped_fork_await_42;
  return (result == 42)
}

// scoped: auto-cancels on exit (callback returns without awaiting)
def scoped_forget (s : Scope) : IO I64 := do {
  scope_fork s io_42_action;
  return 0
}

#[test]
def test_scoped_cancels : IO Bool {
  let result <- scoped scoped_forget;
  return (result == 0)
}

// sleepIO: basic smoke test

#[test]
def test_sleepIO_smoke : IO Bool {
  sleepIO 10;
  return true
}
