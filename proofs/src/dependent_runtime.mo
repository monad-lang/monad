// Executable dependent-elimination tests. `dependent.mo` VERIFIES
// `bool_elim`/`sigma_snd`; these CALL them, so a failure here is a real
// link/run failure -- the self-hosted runner compiles this file and checks
// the returned `Bool`.
//
// A type/inductive NAME in value position (`idT I64 5`'s `I64`) compiles to
// an inert sort-level immediate in both backends. It used to become
// `call i64 @I64` (codegen) / `gd_unresolved` (evaluator), which is why a
// verified eliminator could not previously be called at all.
//
// IMPLICIT type arguments are now inferred from the argument's type
// (`Sigma.snd (Sigma.dpair 1 2)`); a type APPLICATION as a value
// (`List I64`) and a type-level lambda whose body applies a type
// constructor remain inexpressible.
//
// `Sigma.snd` is ambient (the prelude defines it next to `Sigma.fst`), so
// only the explicit `sigma_snd` theorem is imported here.

use lib::dependent {sigma_snd}

/// The minimal polymorphic identity; its first argument is type-level only.
pub def idT (T : Type) (x : T) : T := x

#[test]
def test_idT_supplied_type_argument_executes : Bool :=
    I64.beq (idT I64 5) 5

/// `Sigma.snd` on a concrete dependent pair. The expected
/// `Sigma I64 (fn (a : I64) => I64)` comes from `sigma_snd`'s third
/// parameter, which is what lets the checker bind `dpair`'s A and B; the
/// eliminator then returns the second field.
#[test]
def test_sigma_snd_supplied_type_arguments_execute : Bool :=
    I64.beq (sigma_snd I64 (fn (a : I64) => I64) (Sigma.dpair 1 2)) 2

/// The implicit spelling: `A` and `B` come from `p` itself.
#[test]
def test_sigma_snd_implicit_type_arguments_execute : Bool :=
    I64.beq (Sigma.snd (Sigma.dpair 1 2)) 2
