/// `symbol_ref`: a bare MLIR identifier prints as-is; anything else, such
/// as a Monad qualified def (`main::k`), is quoted -- `mlir-opt` rejects
/// `@main::k` outright.
use lib::ir {symbol_ref}

#[test]
def test_a_bare_symbol_is_unquoted : Bool :=
    String.beq (symbol_ref "saxpy_2.v$") "@saxpy_2.v$"

#[test]
def test_a_qualified_symbol_is_quoted : Bool :=
    String.beq (symbol_ref "main::axpy") "@\"main::axpy\""

#[test]
def test_a_leading_digit_is_quoted : Bool :=
    String.beq (symbol_ref "2x") "@\"2x\""
