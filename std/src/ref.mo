/// A shared, mutable slot.
///
/// `Ref` is the primitive a server needs for state that outlives a request
/// (a session store, a rate-limit table, a hot-reload version cell). It is
/// deliberately small: get, set, and one *atomic* read-modify-write.
///
/// Concurrency: native fibers are OS threads, so an unlocked slot would be a
/// data race. `Ref.update` applies a PURE function under a lock and is the
/// only correct way to do a read-modify-write across fibers. The function it
/// is given MUST NOT call another `Ref` operation: the lock is not reentrant,
/// and a nested call deadlocks.
///
/// On wasi/web the runtime is single-threaded, so the lock is a no-op; the
/// API and the atomicity contract are the same. A `Ref` is never matched or
/// compared; the constructor is not built by user code.
pub type Ref (A : Type) { ref }

#[native cell_new]
pub def Ref.new (init : A) : IO (Ref A)

#[native cell_get]
pub def Ref.get (r : Ref A) : IO A

#[native cell_set]
pub def Ref.set (r : Ref A) (v : A) : IO Unit

/// Apply a pure `f` under the lock and store the result. Returns the new
/// value. `f` must not call a `Ref` operation (non-reentrant lock).
#[native cell_update]
pub def Ref.update (r : Ref A) (f : A -> A) : IO A

/// An atomic integer add, for counters (rate limits, sequence numbers) where
/// a general `update` would allocate a closure per call.
#[native cell_add_i64]
pub def Ref.add_i64 (r : Ref I64) (delta : I64) : IO I64

/// `Ref.update` with the result discarded.
pub def Ref.modify (r : Ref A) (f : A -> A) : IO Unit := do {
  let _ <- Ref.update r f;
  return unit
}
