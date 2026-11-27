/// `infer.mo`'s `retag_nat_index_literals`: the signature twin of the
/// literal retag. A numeric literal in a TYPE position is always a `Nat`
/// index, so it must become the `Nat.of_i64 <lit>` builder the rest of the
/// checker (and `whnf`) expects -- otherwise `def f (v : Vec 2 I64)` keeps
/// an `I64` literal and a computed index can never meet it.
///
/// The pass is structural on purpose: resolving the application's head to
/// ask whether the parameter is `Nat` was tried and silently did nothing
/// for a type spelled bare but registered module-qualified, which is the
/// common case for an imported type.
use lib::types {
    DebugName, Identifier, Literal, NumSuffix, Term, sentinel, show_identifier, term_peel,
}
use lib::typecheck::infer {retag_nat_index_literals, retag_when_indexed}

/// `Wrap <lit>`, the shape every indexed type application shares.
def wrap_app (n : I64) : Term :=
    Term.app (Term.var sentinel (DebugName.named (Identifier.id "Wrap")))
        (Term.lit (Literal.num n NumSuffix.i64))

def app_arg (t : Term) : Option Term :=
    match term_peel t {
        Term.app _f a => Option.some (term_peel a),
        _ => Option.none,
    }

def is_of_i64_app (t : Term) : Bool :=
    match term_peel t {
        Term.app f _a =>
            match term_peel f {
                Term.var _idx dbg =>
                    match dbg {
                        DebugName.named id => String.beq (show_identifier id) "Nat.of_i64",
                        DebugName.unnamed => false,
                    },
                _ => false,
            },
        _ => false,
    }

#[test]
def test_a_type_index_literal_becomes_the_builder : Bool :=
    match app_arg (retag_nat_index_literals (wrap_app 2)) {
        Option.some a => is_of_i64_app a,
        Option.none => false,
    }

/// Idempotence matters: a declaration's type is retagged once for its own
/// check and again when a CALLER reads its signature from the scope.
#[test]
def test_the_builder_is_already_retagged : Bool :=
    let once : Term := retag_nat_index_literals (wrap_app 2) in
    let twice : Term := retag_nat_index_literals once in
    match app_arg twice {
        Option.some a => is_of_i64_app a,
        Option.none => false,
    }

/// A suffixed literal is not a `Nat` spelling and stays as written.
#[test]
def test_a_suffixed_literal_is_left_alone : Bool :=
    let t : Term := Term.app (Term.var sentinel (DebugName.named (Identifier.id "Wrap")))
        (Term.lit (Literal.num 2 NumSuffix.u8)) in
    match app_arg (retag_nat_index_literals t) {
        Option.some a => Bool.not (is_of_i64_app a),
        Option.none => false,
    }

/// The gate answers "no literal here" for the overwhelming majority of
/// types, and leaves them untouched when it does.
#[test]
def test_the_gate_leaves_a_literal_free_type_alone : Bool :=
    let t : Term := Term.app (Term.var sentinel (DebugName.named (Identifier.id "Wrap")))
        (Term.var sentinel (DebugName.named (Identifier.id "A"))) in
    match app_arg (retag_when_indexed t) {
        Option.some a => Bool.not (is_of_i64_app a),
        Option.none => false,
    }

/// A literal deeper inside the type -- `List (Wrap 2)` -- is reached too.
#[test]
def test_a_nested_index_literal_is_retagged : Bool :=
    let inner : Term := wrap_app 2 in
    let outer : Term := Term.app (Term.var sentinel (DebugName.named (Identifier.id "List"))) inner in
    match term_peel (retag_nat_index_literals outer) {
        Term.app _f a => match app_arg a {
            Option.some lit => is_of_i64_app lit,
            Option.none => false,
        },
        _ => false,
    }
