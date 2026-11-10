/// `Strand` -- Loom Phase 2 (plugin-framework.md): a plugin lifecycle step
/// as an indexed monad over `IO`, carrying the disposers of everything it
/// mounted. `Pending -> Active -> Disposed` are phantom type markers: the
/// checker does not enforce the transition yet, so the typed entry points
/// and the LIFO test are the live contract.
///
/// The action is a THUNK. A bare `IO A` is an already-performed value in
/// the compiled backend (`init/src/io.mo` and the recorded note in weaver's
/// `dumb.mo`), so storing one would run the mount at construction. The
/// thunk defers it to `run`/`activate`.
///
/// The action returns a `StrandRun` (value + disposers). `bind` puts the
/// second strand's disposers FIRST, so disposing head-first over the list
/// unwinds in true LIFO order. A named result type, not `Pair`: the
/// self-hosted checker mis-infers a generic `Pair A (List Disposer)` with
/// two free type variables here.
use loom::disposer {Disposer}

pub type Pending {}
pub type Active {}
pub type Disposed {}

/// One strand action's result: its value and the disposers it registered.
/// A one-constructor type rather than a struct: the self-hosted checker
/// cannot infer a generic struct literal's type here.
pub type StrandRun A {
    run_result (value : A) (disposers : List Disposer)
}

pub def StrandRun.value (r : StrandRun A) : A :=
    match r { run_result v _ => v }

pub def StrandRun.disposers (r : StrandRun A) : List Disposer :=
    match r { run_result _ ds => ds }

pub type Strand (I : Type) (J : Type) (A : Type) {
    strand (run : Unit -> IO (StrandRun A))
}

/// Run any strand. The indices are phantom, so this is the practical entry.
pub def Strand.run {I J A : Type} (s : Strand I J A) : IO (StrandRun A) :=
    match s { strand f => f unit }

/// A `Pending -> Active` producer (the index-transition test's start).
pub def Strand.pending {A : Type} (f : Unit -> IO (StrandRun A)) : Strand Pending Active A :=
    Strand.strand f

/// Mount one resource in an already-active context and register its teardown.
pub def Strand.bracket {A : Type} (mount : Unit -> IO A) (dispose : A -> IO (Result String Unit)) : Strand Active Active A :=
    Strand.strand (fn (_ : Unit) => do {
        let a <- mount unit;
        let d : Disposer := { run := fn (_ : Unit) => dispose a };
        let out : StrandRun A := StrandRun.run_result a (List.cons d List.empty);
        IO.pure out
    })

/// `Pending -> Active`: run the action.
pub def Strand.activate {A : Type} (s : Strand Pending Active A) : IO (StrandRun A) :=
    Strand.run s

/// `Active -> Disposed`: an action that disposes the stack it was given.
pub def Strand.sealed (sink : String -> IO Unit) (ds : List Disposer) : Strand Active Disposed Unit :=
    Strand.strand (fn (_ : Unit) => do {
        let _ <- Strand.dispose sink ds;
        let out : StrandRun Unit := StrandRun.run_result unit List.empty;
        IO.pure out
    })

/// Run the disposers head-first (LIFO), report each error to `sink`, and
/// never stop early.
#[partial]
pub def Strand.dispose (sink : String -> IO Unit) (ds : List Disposer) : IO Unit :=
    match ds {
        List.empty => IO.pure unit,
        List.cons d rest => do {
            let r <- Disposer.run d;
            match r {
                Result.ok _ => Strand.dispose sink rest,
                Result.err e => do {
                    let _ <- sink e;
                    Strand.dispose sink rest
                },
            }
        },
    }

/// `bind`'s IO composition, kept in its own def: a `let … <-` inside a
/// match arm in the same do-block is the shape the checker rejects.
def bind_run {I J K : Type} {A B : Type} (a : Strand I J A) (f : A -> Strand J K B) : IO (StrandRun B) :=
    Monad.bind (Strand.run a) (fn (ra : StrandRun A) =>
        Monad.bind (Strand.run (f (StrandRun.value ra))) (fn (rb : StrandRun B) =>
            let out : StrandRun B := StrandRun.run_result (StrandRun.value rb) (List.append (StrandRun.disposers rb) (StrandRun.disposers ra)) in
            IO.pure out))

pub instance IndexedMonad Strand {
    def pure (a : A) : Strand I I A :=
        Strand.strand (fn (_ : Unit) =>
            let out : StrandRun A := StrandRun.run_result a List.empty in
            IO.pure out)

    def bind (a : Strand I J A) (f : A -> Strand J K B) : Strand I K B :=
        Strand.strand (fn (_ : Unit) => bind_run a f)

    def map (f : A -> B) (ma : Strand I J A) : Strand I J B :=
        Strand.strand (fn (_ : Unit) => do {
            let r <- Strand.run ma;
            let out : StrandRun B := StrandRun.run_result (f (StrandRun.value r)) (StrandRun.disposers r);
            IO.pure out
        })

    def and_then (first : Strand I J A) (second : Strand J K B) : Strand I K B :=
        Strand.strand (fn (_ : Unit) => do {
            let r1 <- Strand.run first;
            let r2 <- Strand.run second;
            let out : StrandRun B := StrandRun.run_result (StrandRun.value r2) (List.append (StrandRun.disposers r2) (StrandRun.disposers r1));
            IO.pure out
        })

    def lift (a : A) : Strand I I A :=
        Strand.strand (fn (_ : Unit) =>
            let out : StrandRun A := StrandRun.run_result a List.empty in
            IO.pure out)
}

/// The prelude's variable-head bridge (`Monad (M I I)`) does not dispatch by
/// type head, so spell the equal-index instance out for `Strand`.
pub instance Monad (Strand I I) {
    def pure (a : A) : Strand I I A :=
        Strand.strand (fn (_ : Unit) =>
            let out : StrandRun A := StrandRun.run_result a List.empty in
            IO.pure out)

    def bind (a : Strand I I A) (f : A -> Strand I I B) : Strand I I B :=
        Strand.strand (fn (_ : Unit) => bind_run a f)
}
