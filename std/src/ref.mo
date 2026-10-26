/// A shared, mutable slot.
///
/// `Ref` is the primitive a server needs for state that outlives a request
/// (a session store, a rate-limit table, a hot-reload version cell). It is
/// deliberately small: get, set, and one *atomic* read-modify-write.
///
/// Concurrency: native fibers are OS threads, so an unlocked slot would be a
/// data race. `Ref.update` applies a PURE function atomically and is the
/// only correct way to do a read-modify-write across fibers. No lock is held
/// while the function runs: if another fiber stores first, the function is
/// applied again to the new value, so it may run more than once.
///
/// On wasi/web the runtime is single-threaded; the API and the atomicity
/// contract are the same. A `Ref` is never matched or
/// compared; the constructor is not built by user code.
pub type Ref (A : Type) { ref }

#[native cell_new]
priv def cell_new_raw (init : A) : RawIO (Ref A)

pub def Ref.new (init : A) : IO (Ref A) := IO.mk (cell_new_raw init)

#[native cell_get]
priv def cell_get_raw (r : Ref A) : RawIO A

pub def Ref.get (r : Ref A) : IO A := IO.mk (cell_get_raw r)

#[native cell_set]
priv def cell_set_raw (r : Ref A) (v : A) : RawIO Unit

pub def Ref.set (r : Ref A) (v : A) : IO Unit := IO.mk (cell_set_raw r v)

#[native cell_update]
priv def cell_update_raw (r : Ref A) (f : A -> A) : RawIO A

/// Apply a pure `f` to the current value and store the result atomically.
/// Returns the new value. `f` may run more than once under contention.
pub def Ref.update (r : Ref A) (f : A -> A) : IO A :=
  IO.mk (cell_update_raw r f)

#[native cell_add_i64]
priv def cell_add_i64_raw (r : Ref I64) (delta : I64) : RawIO I64

/// An atomic integer add, for counters (rate limits, sequence numbers) where
/// a general `update` would allocate a closure per call.
pub def Ref.add_i64 (r : Ref I64) (delta : I64) : IO I64 :=
  IO.mk (cell_add_i64_raw r delta)

/// `Ref.update` with the result discarded.
pub def Ref.modify (r : Ref A) (f : A -> A) : IO Unit := do {
  let _ <- Ref.update r f;
  return unit
}
