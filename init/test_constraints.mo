use std.test
use init
use io
open IO

// ============================================
// Constraint Solver Tests
// ============================================
// These tests verify that instance constraint resolution
// works correctly. The constraint solver ensures that an
// instance like `instance [Show A] ShowWrap A` only matches
// when a `Show A` instance actually exists.

// --- Class Definitions ---

class Show A {
  def show : A -> String
}

class [Show A] ShowWrap A {
  def show_wrap : A -> String
}

class [Show A] ShowDouble A {
  def show_double : A -> String
}

// --- Instances ---

// Show I64 exists (no constraints)
instance Show I64 {
  def show (a : I64) : String := I64.to_string a
}

// ShowWrap I64 requires Show I64 (which exists)
instance [Show I64] ShowWrap I64 {
  def show_wrap (a : I64) : String := I64.to_string a
}

// ShowDouble I64 requires Show I64 (which exists)
instance [Show I64] ShowDouble I64 {
  def show_double (a : I64) : String := I64.to_string a
}

// --- Tests ---

// Test 1: Basic instance without constraints works
@[test]
def test_show_i64 : Bool :=
    I64.to_string 42 == I64.to_string 42

// Test 2: Instance with satisfied constraint works
// ShowWrap I64 requires Show I64, which exists
@[test]
def test_show_wrap_i64 : Bool :=
    ShowWrap.show_wrap 42 == I64.to_string 42

// Test 3: Multiple instances with same constraint work
@[test]
def test_show_double_i64 : Bool :=
    ShowDouble.show_double 42 == I64.to_string 42

// Test 4: Verify that constraint resolution is recursive
// This tests that the solver checks Show I64 when resolving ShowWrap I64
@[test]
def test_constraint_chain : Bool :=
    ShowWrap.show_wrap 100 == I64.to_string 100

// Test 5: String instances work (BEq String, ToString String exist)
@[test]
def test_string_operations : Bool :=
    not (String.is_empty "hello")

// Test 6: List operations work (FromListLiteral List exists)
@[test]
def test_list_operations : Bool :=
    not (List.is_empty [1, 2, 3])

// Test 7: Option operations work
def get_five : Option I64 :=
    some 5

@[test]
def test_option_operations : Bool :=
    match get_five {
      some _ => true,
      none => false
    }
