/// `lib::typecheck::nat_literal`: the literal ⇄ unary-chain conversions and
/// the `Nat.of_i64` reduction `whnf` uses (the `Slice` index work).
use lib::types {DebugName, Identifier, Literal, NumSuffix, Term, sentinel}
use lib::typecheck::nat_literal {
    nat_literal_term, nat_of_i64_unary_app, nat_value_of, small_nat_literal,
}

/// `Nat.of_i64 <lit>` as `apply_nat_rewrite` builds it.
def of_i64_app (n : I64) : Term :=
    Term.app (Term.var sentinel (DebugName.named (Identifier.id "Nat.of_i64")))
        (Term.lit (Literal.num n NumSuffix.i64))

#[test]
def test_a_chain_reads_back_as_its_number : Bool :=
    match nat_value_of (nat_literal_term 3) {
        Option.some n => I64.beq n 3,
        Option.none => false,
    }

#[test]
def test_zero_is_the_empty_chain : Bool :=
    match nat_value_of (nat_literal_term 0) {
        Option.some n => I64.beq n 0,
        Option.none => false,
    }

#[test]
def test_an_of_i64_application_is_a_small_literal : Bool :=
    match small_nat_literal (of_i64_app 2) {
        Option.some n => I64.beq n 2,
        Option.none => false,
    }

/// The reduction `whnf` performs: the application becomes the unary chain.
#[test]
def test_of_i64_reduces_to_the_chain : Bool :=
    match nat_of_i64_unary_app (of_i64_app 2) {
        Option.some unary =>
            match nat_value_of unary {
                Option.some n => I64.beq n 2,
                Option.none => false,
            },
        Option.none => false,
    }

/// The bound is deliberate: past it the term stays as written.
#[test]
def test_an_of_i64_beyond_the_bound_stays_stuck : Bool :=
    match nat_of_i64_unary_app (of_i64_app 65) {
        Option.some _ => false,
        Option.none => true,
    }

/// A negative literal is not a `Nat`.
#[test]
def test_a_negative_literal_is_not_a_nat : Bool :=
    match small_nat_literal (of_i64_app (0 - 1)) {
        Option.some _ => false,
        Option.none => true,
    }
