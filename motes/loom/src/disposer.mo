/// A resource's teardown -- Loom Phase 2 (plugin-framework.md). `!` is
/// intent: multiplicity is not enforced yet (the plan's Current Verified
/// State C), so `Strand.dispose`'s LIFO test is the live invariant. A
/// teardown reports failure as a value so one bad disposer cannot stop the
/// rest.
///
/// The action is a THUNK: a bare `IO A` is already-performed when it is
/// constructed in the compiled backend, so the teardown would run at mount
/// time instead of disposal time.
pub struct Disposer {
    !run : Unit -> IO (Result String Unit)
}

/// Run one teardown, consuming the linear field.
pub def Disposer.run (d : Disposer) : IO (Result String Unit) :=
    match d { { run, .. } => run unit }
