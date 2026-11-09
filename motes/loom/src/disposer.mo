/// A resource's teardown -- Loom Phase 2 (plugin-framework.md). The field is
/// meant to be consumed once, but nothing enforces that (the `!` field prefix
/// that spelled the intent was never checked, and is gone from the grammar),
/// so `Strand.dispose`'s LIFO test is the live invariant. A teardown reports
/// failure as a value so one bad disposer cannot stop the rest.
///
/// The action is a THUNK: a bare `IO A` is already-performed when it is
/// constructed in the compiled backend, so the teardown would run at mount
/// time instead of disposal time.
pub struct Disposer {
    run : Unit -> IO (Result String Unit)
}

/// Run one teardown, consuming the disposer.
pub def Disposer.run (d : Disposer) : IO (Result String Unit) :=
    match d { { run, .. } => run unit }
