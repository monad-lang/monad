use std::test {}
use lib::id {Id, Id.run}
use lib::transformers {
    StateT, ReaderT, ResultT, OptionT, WriterT, IdentityT,
}

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
// the same `def`, and called "StateT-specific." That diagnosis was only half
// right: splitting `Monad.bind`'s computation into its own top-level `def`
// (the fix that resurrects `ResultT`/`OptionT`'s own bind tests below)
// cleared the `MatchTraversalMismatch` here too. But it then exposed a
// SECOND, separate failure: `eval error: value is not a constructor` at run
// time, inside the `StateT` instance's own `bind`/`StateT.bind_step`
// (`lib/transformers.mo`),
// previously blamed on a real interpreter bug in `StateT`'s own `bind`.
// That blame was wrong: the failure was the checker's dictionary-resolution
// gap for instance calls whose `[Monad M]` dictionary argument resolves
// from a partially-applied spine (`StateT I64 Id`), fixed by the
// constraint-position work in `core_check_module.rs`/`core_check.rs` --
// the split-`def` form below now passes.
def statet_bind_result : StateT I64 Id I64 :=
    let m : StateT I64 Id I64 := Monad.pure 10 in
    Monad.bind m (fn a => Monad.pure (a + 1))

#[test]
def test_statet_bind : Bool :=
    match Id.run (StateT.run statet_bind_result 100) {
        Pair.pair s a => (s == 100) && (a == 11)
    }

// ReaderT: the same probes as StateT, with the state replaced by a
// read-only environment. `bind` uses the split-`def` form above for the
// same `MatchTraversalMismatch` reason.
#[test]
def test_readert_pure_run : Bool :=
    let m : ReaderT I64 Id I64 := Monad.pure 42 in
    (Id.run (ReaderT.run m 7)) == 42

def readert_bind_result : ReaderT I64 Id I64 :=
    let m : ReaderT I64 Id I64 := Monad.pure 10 in
    Monad.bind m (fn a => Monad.pure (a + 1))

#[test]
def test_readert_bind : Bool :=
    (Id.run (ReaderT.run readert_bind_result 100)) == 11

#[test]
def test_readert_ask : Bool :=
    let m : ReaderT I64 Id I64 := ReaderT.ask in
    (Id.run (ReaderT.run m 7)) == 7

#[test]
def test_readert_asks : Bool :=
    let m : ReaderT I64 Id I64 := ReaderT.asks (fn (x : I64) => x + 1) in
    (Id.run (ReaderT.run m 7)) == 8

#[test]
def test_readert_local : Bool :=
    let m : ReaderT I64 Id I64 := ReaderT.ask in
    (Id.run (ReaderT.run (ReaderT.local (fn (x : I64) => x + 1) m) 7)) == 8

#[test]
def test_readert_lift : Bool :=
    let m : ReaderT I64 Id I64 := ReaderT.lift (Id.id 5) in
    (Id.run (ReaderT.run m 0)) == 5

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

// ── StateT: get / put / modify (MonadState operations, no class) ────────

def statet_get_result : StateT I64 Id I64 :=
    StateT.get

#[test]
def test_statet_get : Bool :=
    match Id.run (StateT.run statet_get_result 5i64) {
        Pair.pair s a => Bool.and (s == 5) (a == 5)
    }

def statet_put_result : StateT I64 Id Unit :=
    StateT.put 9i64

#[test]
def test_statet_put : Bool :=
    match Id.run (StateT.run statet_put_result 5i64) {
        Pair.pair s _ => s == 9
    }

def statet_modify_result : StateT I64 Id Unit :=
    StateT.modify (fn (x : I64) => x + 1i64)

#[test]
def test_statet_modify : Bool :=
    match Id.run (StateT.run statet_modify_result 5i64) {
        Pair.pair s _ => s == 6
    }

// ── ReaderT with a NON-Copy environment ─────────────────────────────────
//
// `List I64` has no `Copy` instance. `ReaderT.bind` names its environment
// twice; the binder's type is an unattributable type variable, so the
// affine rule's fail-open path exempts it. This test pins that a non-Copy
// environment still runs.

def readert_list_bind_result : ReaderT (List I64) Id I64 :=
    let m : ReaderT (List I64) Id I64 := ReaderT.ask in
    Monad.bind m (fn (xs : List I64) =>
        match xs {
            List.cons h _ => Monad.pure h,
            List.empty => Monad.pure 0i64
        })

#[test]
def test_readert_bind_non_copy_env : Bool :=
    let env : List I64 := List.cons 1i64 (List.cons 2i64 List.empty) in
    (Id.run (ReaderT.run readert_list_bind_result env)) == 1

// ── ResultT: ExceptT operations ─────────────────────────────────────────

def resultt_throw_result : ResultT String Id I64 :=
    ResultT.throw "bad"

#[test]
def test_resultt_throw : Bool :=
    match Id.run (ResultT.run resultt_throw_result) {
        Result.ok _ => false,
        Result.err e => String.beq e "bad"
    }

def resultt_catch_result : ResultT String Id I64 :=
    ResultT.catch resultt_throw_result (fn (_e : String) => Monad.pure 9i64)

#[test]
def test_resultt_catch : Bool :=
    match Id.run (ResultT.run resultt_catch_result) {
        Result.ok a => a == 9,
        Result.err _ => false
    }

def resultt_map_error_result : ResultT I64 Id I64 :=
    ResultT.map_error (fn (_e : String) => 42i64) resultt_throw_result

#[test]
def test_resultt_map_error : Bool :=
    match Id.run (ResultT.run resultt_map_error_result) {
        Result.ok _ => false,
        Result.err e => e == 42
    }

// ── WriterT ─────────────────────────────────────────────────────────────

def writert_bind_log_result : WriterT String Id I64 :=
    let m : WriterT String Id I64 := Monad.pure 10i64 in
    Monad.bind m (fn a =>
        Monad.bind (WriterT.tell "x") (fn (_ : Unit) => Monad.pure (a + 1i64)))

#[test]
def test_writert_bind_log : Bool :=
    match Id.run (WriterT.run writert_bind_log_result) {
        Pair.pair w a => Bool.and (String.beq w "x") (a == 11)
    }

#[test]
def test_writert_lift_empty_log : Bool :=
    let m : WriterT String Id I64 := WriterT.lift (Id.id 5i64) in
    match Id.run (WriterT.run m) {
        Pair.pair w a => Bool.and (String.is_empty w) (a == 5)
    }

def writert_listen_result : WriterT String Id (Pair I64 String) :=
    let m : WriterT String Id I64 :=
        Monad.bind (WriterT.tell "log") (fn (_ : Unit) => Monad.pure 7i64) in
    WriterT.listen m

#[test]
def test_writert_listen : Bool :=
    match Id.run (WriterT.run writert_listen_result) {
        Pair.pair w p =>
            match p {
                Pair.pair a w2 =>
                    Bool.and (String.beq w "log")
                        (Bool.and (String.beq w2 "log") (a == 7))
            }
    }

def writert_censor_result : WriterT String Id I64 :=
    let m : WriterT String Id I64 :=
        Monad.bind (WriterT.tell "abc") (fn (_ : Unit) => Monad.pure 1i64) in
    WriterT.censor (fn (w : String) => String.concat w "!") m

#[test]
def test_writert_censor : Bool :=
    match Id.run (WriterT.run writert_censor_result) {
        Pair.pair w a => Bool.and (String.beq w "abc!") (a == 1)
    }

// ── IdentityT ───────────────────────────────────────────────────────────

#[test]
def test_idt_lift : Bool :=
    let m : IdentityT Id I64 := IdentityT.lift (Id.id 5i64) in
    (Id.run (IdentityT.run m)) == 5

def idt_bind_result : IdentityT Id I64 :=
    let m : IdentityT Id I64 := Monad.pure 10i64 in
    Monad.bind m (fn a => Monad.pure (a + 1i64))

#[test]
def test_idt_bind : Bool :=
    (Id.run (IdentityT.run idt_bind_result)) == 11
