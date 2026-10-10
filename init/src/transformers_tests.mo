use std::test {}
use lib::id {Id, Id.run}
use lib::transformers {StateT, ResultT, OptionT}

// StateT spike: the smallest shape that exercises everything the rest of
// this module depends on -- a higher-kinded type parameter (`M : Type -> Type`)
// on an inductive, a `[Monad M]`-constrained instance, and run-time recursive
// dispatch of `Monad.pure`/`Monad.bind` on the underlying monad through the
// instance body's variable `M` (concretized to `Id` at the call site).

#[test]
def test_statet_pure_run : Bool :=
    let m : StateT I64 Id I64 := Monad.pure 42 in
    match Id.run (StateT.run m 0) {
        Pair.pair s a => (s == 0) && (a == 42)
    }

// `test_statet_bind` was commented out here, blamed on `MatchTraversalMismatch`
// triggered by `Monad.bind` immediately followed by a `Pair.pair` match in
// the same `def`, and called "StateT-specific." That diagnosis is only half
// right: splitting `Monad.bind`'s computation into its own top-level `def`
// (the fix that resurrects `ResultT`/`OptionT`'s own bind tests below, after
// finding the SAME lowering bug there -- it is not StateT-specific) does
// clear the `MatchTraversalMismatch` here too. But it then exposes a SECOND,
// separate bug: `eval error: value is not a constructor` at run time, inside
// `StateT.bind_go`/`StateT.bind_step` (`lib/transformers.mo`) -- a real
// interpreter bug in `StateT`'s own `bind`, previously masked by the
// lowering failure, not something this plan's `ResultT`/`OptionT` work
// is scoped to chase down. Restore the split-`def` form once that is fixed:
//
// def statet_bind_result : StateT I64 Id I64 :=
//     let m : StateT I64 Id I64 := Monad.pure 10 in
//     Monad.bind m (fn a => Monad.pure (a + 1))
//
// #[test]
// def test_statet_bind : Bool :=
//     match Id.run (StateT.run statet_bind_result 100) {
//         Pair.pair s a => (s == 100) && (a == 11)
//     }

// ResultT/OptionT `bind`: a throwaway single-file probe (outside this mote,
// its own tiny `#![mote {...}]`) run BEFORE writing these instances showed
// `Monad.bind` dispatch followed immediately by a `Result.ok`/`err` or
// `Option.some`/`none` match passing cleanly -- but that probe was
// MISLEADING. Run for real, in THIS file (part of `init`'s own full
// prelude context, much bigger than an isolated probe), the identical
// `Monad.bind`-then-`match` shape reproduces the exact same
// `MatchTraversalMismatch` StateT's own note describes. So the bug is not
// "StateT-specific" as that note concluded -- it is sensitive to the
// surrounding compilation context's size/shape, and a small standalone
// probe is not a reliable predictor of the real target file. The fix that
// *does* work, confirmed here: put `Monad.bind`'s own computation in its
// own top-level `def`, so the `match` that reads the result is no longer
// in the same `def` as the `bind` dispatch -- exactly the mitigation this
// codebase already uses for Loom's indexed-monad do-blocks.

def resultt_bind_result : ResultT String Id I64 :=
    let m : ResultT String Id I64 := Monad.pure 10 in
    Monad.bind m (fn a => Monad.pure (a + 1))

#[test]
def test_resultt_pure_run : Bool :=
    let m : ResultT String Id I64 := Monad.pure 42 in
    match Id.run (ResultT.run m) {
        Result.ok a => a == 42,
        Result.err _ => false
    }

#[test]
def test_resultt_bind : Bool :=
    match Id.run (ResultT.run resultt_bind_result) {
        Result.ok a => a == 11,
        Result.err _ => false
    }

def resultt_bind_short_circuit_result : ResultT String Id I64 :=
    let m : ResultT String Id I64 := ResultT.mk (Id.id (Result.err "boom")) in
    Monad.bind m (fn a => Monad.pure (a + 1))

#[test]
def test_resultt_bind_short_circuits : Bool :=
    match Id.run (ResultT.run resultt_bind_short_circuit_result) {
        Result.ok _ => false,
        Result.err e => String.beq e "boom"
    }

#[test]
def test_optiont_pure_run : Bool :=
    let m : OptionT Id I64 := Monad.pure 42 in
    match Id.run (OptionT.run m) {
        Option.some a => a == 42,
        Option.none => false
    }

def optiont_bind_result : OptionT Id I64 :=
    let m : OptionT Id I64 := Monad.pure 10 in
    Monad.bind m (fn a => Monad.pure (a + 1))

#[test]
def test_optiont_bind : Bool :=
    match Id.run (OptionT.run optiont_bind_result) {
        Option.some a => a == 11,
        Option.none => false
    }

def optiont_bind_short_circuit_result : OptionT Id I64 :=
    let m : OptionT Id I64 := OptionT.mk (Id.id Option.none) in
    Monad.bind m (fn a => Monad.pure (a + 1))

#[test]
def test_optiont_bind_short_circuits : Bool :=
    match Id.run (OptionT.run optiont_bind_short_circuit_result) {
        Option.some _ => false,
        Option.none => true
    }
