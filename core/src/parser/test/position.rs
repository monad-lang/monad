use super::*;
use crate::parser::error;

/// Helper to get error position from parse result
fn get_error_pos(input: &str) -> (usize, usize) {
  let result = parse_file(input);
  let err = match result {
    Ok(_) => panic!("Expected parse error for input: {}", input),
    Err(e) => e,
  };
  error::get_error_line_column(&err.source, &err.error)
}

/// Test that error on line 1 at end of incomplete expression reports position AFTER last token
/// Input: "def foo : I64 := " is 17 bytes
/// Error should be at column 18 (after the last space)
#[test]
fn test_error_position_end_of_line() {
  let input = "def foo : I64 := ";
  let (line, col) = get_error_pos(input);

  assert_eq!(line, 1, "Error should be on line 1, got line {}", line);
  // "def foo : I64 := " is 17 bytes, error after last space
  assert_eq!(
    col, 18,
    "Error should be at column 18 (after trailing space), got column {}",
    col
  );
}

/// Test error on line 2
/// Input: "def foo : I64 := 42\ndef bar : I64 := "
/// Line 1: "def foo : I64 := 42" is 19 bytes + newline = 20 bytes
/// Line 2: "def bar : I64 := " is 17 bytes
/// Error after line 2, so column 18
#[test]
fn test_error_position_after_newline() {
  let input = "def foo : I64 := 42\ndef bar : I64 := ";
  let (line, col) = get_error_pos(input);

  assert_eq!(line, 2, "Error should be on line 2, got line {}", line);
  assert_eq!(col, 18, "Error should be at column 18, got column {}", col);
}

/// Test error on line 3
/// Input has 3 lines, error on line 3 after "def c : I64 := "
#[test]
fn test_error_position_multiline() {
  let input = "def a : I64 := 1\ndef b : I64 := 2\ndef c : I64 := \ndef d : I64 := 4";
  let (line, col) = get_error_pos(input);

  // After parsing "def c : I64 := " and the following newline, parser is at line 4
  // The error is reported at the start of line 4
  assert_eq!(line, 4, "Error should be on line 4, got line {}", line);
  assert_eq!(col, 1, "Error should be at column 1, got column {}", col);
}

/// Test error after incomplete operator
/// "def foo : I64 := 1 + " is 21 bytes
#[test]
fn test_error_position_incomplete_operator() {
  let input = "def foo : I64 := 1 + ";
  let (line, col) = get_error_pos(input);

  assert_eq!(line, 1, "Error should be on line 1, got line {}", line);
  assert_eq!(
    col, 22,
    "Error should be at column 22 (after + and space), got column {}",
    col
  );
}

/// Test error in nested structure
/// Line 2: "  if true then 1 else " is 21 chars
#[test]
fn test_error_position_nested_if() {
  let input = "def foo : I64 := \n  if true then 1 else \ndef bar : I64 := 42";
  let (line, col) = get_error_pos(input);

  // After parsing the do block, parser consumes the newline, moving to line 3
  assert_eq!(line, 3, "Error should be on line 3, got line {}", line);
  assert_eq!(col, 1, "Error should be at column 1, got column {}", col);
}

/// Test error with use statements - if it fails, position should be within bounds
#[test]
fn test_error_position_use_statements() {
  let input = "use io\nopen IO\nuse process\nuse lang.types\n";
  let result = parse_file(input);

  if let Err(err) = result {
    let (line, col) = error::get_error_line_column(&err.source, &err.error);
    assert!(
      line >= 1 && line <= 4,
      "Error line {} out of range [1,4]",
      line
    );
    assert!(col >= 1, "Column should be at least 1, got {}", col);

    if line == 4 {
      // "use lang.types" is 14 chars
      assert!(col <= 15, "Column {} on line 4 exceeds line length 15", col);
    }
  }
}

/// Test error on single character "x"
/// Parser consumes "x", then fails expecting more
/// Error at offset 1, which is after "x", so column 2
#[test]
fn test_error_position_exact_offset() {
  let input = "x";
  let (line, col) = get_error_pos(input);

  assert_eq!(line, 1, "Error should be on line 1, got line {}", line);
  // After consuming "x" (1 char), error at offset 1, column = 1 + 1 = 2
  assert_eq!(
    col, 2,
    "Error should be at column 2 (after 'x'), got column {}",
    col
  );
}

/// Test error after multiple newlines
/// 3 newlines + "def foo : I64 := " (17 bytes) = line 4, column 18
#[test]
fn test_error_position_after_multiple_newlines() {
  let input = "\n\n\ndef foo : I64 := ";
  let (line, col) = get_error_pos(input);

  assert_eq!(line, 4, "Error should be on line 4, got line {}", line);
  assert_eq!(col, 18, "Error should be at column 18, got column {}", col);
}

/// Test empty file
#[test]
fn test_error_position_start_of_file() {
  let input = "";
  let result = parse_file(input);

  if let Err(err) = result {
    let (line, col) = error::get_error_line_column(&err.source, &err.error);
    assert_eq!(line, 1, "Error should be on line 1, got line {}", line);
    assert_eq!(col, 1, "Error should be at column 1, got column {}", col);
  }
}

/// Test long line
/// "def very_long_function_name : VeryLongType := " is 46 bytes
#[test]
fn test_error_position_long_line() {
  let input = "def very_long_function_name : VeryLongType := ";
  let (line, col) = get_error_pos(input);

  assert_eq!(line, 1, "Error should be on line 1, got line {}", line);
  // 46 bytes + 1 = column 47
  assert_eq!(col, 47, "Error should be at column 47, got column {}", col);
}

/// Test simple syntax error
#[test]
fn test_error_position_simple() {
  let input = "def foo := 42";
  let (line, col) = get_error_pos(input);

  assert_eq!(line, 1, "Error should be on line 1, got line {}", line);
  // Just verify it's on line 1 with reasonable column
  assert!(
    col >= 1 && col <= 20,
    "Column {} out of reasonable range",
    col
  );
}

/// Regression test: a parse error occurring after one or more string literals
/// must still report its true absolute position. `string_literal` used to
/// rebuild its continuation span via `Span::new`, which reset `offset` to 0
/// and `line` to 1 — silently corrupting the location of any later error.
#[test]
fn test_error_position_after_string_literals() {
  let input = "def a : String := \"hello\"\ndef b : String := \"world\"\ndef c : I64 := ";
  let (line, col) = get_error_pos(input);

  assert_eq!(
    line, 3,
    "Error should be on line 3 (after two string literals), got line {}",
    line
  );
  assert_eq!(
    col, 16,
    "Error should be at column 16 (after trailing space on line 3), got column {}",
    col
  );
}

/// Regression test: same as above but for char literals.
#[test]
fn test_error_position_after_char_literals() {
  let input = "def a : Char := 'x'\ndef b : Char := 'y'\ndef c : I64 := ";
  let (line, col) = get_error_pos(input);

  assert_eq!(
    line, 3,
    "Error should be on line 3 (after two char literals), got line {}",
    line
  );
  assert_eq!(
    col, 16,
    "Error should be at column 16 (after trailing space on line 3), got column {}",
    col
  );
}

/// Test that error column and line are never 0
#[test]
fn test_error_position_never_zero() {
  let inputs = vec![
    "def ",
    "def foo",
    "def foo :",
    "def foo : I64",
    "def foo : I64 :=",
    ":=",
    "+",
    "if",
  ];

  for input in inputs {
    let result = parse_file(input);
    if let Err(err) = result {
      let (line, col) = error::get_error_line_column(&err.source, &err.error);
      assert!(line >= 1, "Line should be >= 1 for input: {}", input);
      assert!(
        col >= 1,
        "Column should be >= 1 for input: {}, got col={}",
        input,
        col
      );
    }
  }
}

// ============================================================================
// Complex module parsing tests for lang/main.mo issue
// ============================================================================

/// Test simple dotted module path
#[test]
fn test_use_dotted_path_simple() {
  let input = "use a.b";
  let result = parse_file(input);
  assert!(result.is_ok(), "Should parse: {}", input);
}

/// Test dotted module path like in lang/main.mo
#[test]
fn test_use_dotted_path_lang_types() {
  let input = "use lang.types";
  let result = parse_file(input);
  assert!(result.is_ok(), "Should parse: {}", input);
}

/// Test multiple use/open statements (lines 1-4 from main.mo)
#[test]
fn test_multiple_use_open_statements() {
  let input = "use io\nopen IO\nuse process\nuse lang.types";
  let result = parse_file(input);
  assert!(result.is_ok(), "Should parse multiple use/open: {}", input);
}

/// Test lines 1-5 from main.mo
#[test]
fn test_main_mo_lines_1_5() {
  let input = "use io\nopen IO\nuse process\nuse lang.types\nuse lang.codegen.ir";
  let result = parse_file(input);
  assert!(result.is_ok(), "Should parse lines 1-5 of main.mo");
}

/// Test lines 1-10 from main.mo
#[test]
fn test_main_mo_lines_1_10() {
  let input = "use io\nopen IO\nuse process\nuse lang.types\nuse lang.codegen.ir\nuse lang.codegen.emit\nuse lang.module\nuse lang.parser\nuse lang.pretty\nuse lang.parser.core";
  let result = parse_file(input);
  assert!(result.is_ok(), "Should parse lines 1-10 of main.mo");
}

/// Test lines 1-20 from main.mo (adds more uses and opens)
#[test]
fn test_main_mo_lines_1_20() {
  let input = "use io\nopen IO\nuse process\nuse lang.types\nuse lang.codegen.ir\nuse lang.codegen.emit\nuse lang.module\nuse lang.parser\nuse lang.pretty\nuse lang.parser.core\nuse lang.parser.combinators\nuse lang.typecheck.infer\nuse lang.scope\nuse std.list\n\nopen LLVMType\nopen LLVMValue\nopen Term\nopen Literal";
  let result = parse_file(input);
  assert!(result.is_ok(), "Should parse lines 1-20 of main.mo");
}

/// Test lines 1-30 from main.mo (adds first definition)
#[test]
fn test_main_mo_lines_1_30() {
  let input = "use io\nopen IO\nuse process\nuse lang.types\nuse lang.codegen.ir\nuse lang.codegen.emit\nuse lang.module\nuse lang.parser\nuse lang.pretty\nuse lang.parser.core\nuse lang.parser.combinators\nuse lang.typecheck.infer\nuse lang.scope\nuse std.list\n\nopen LLVMType\nopen LLVMValue\nopen Term\nopen Literal\nopen DebugName\nopen ParseResult\nopen NumSuffix\nopen Param\nopen Def\nopen ModulePath\nopen TypeError\n\n#[partial]\ndef empty_str_list : List String := []";
  let result = parse_file(input);
  assert!(result.is_ok(), "Should parse lines 1-30 of main.mo");
}

/// Test parsing lang/types.mo (dependency of main.mo, might have the error)
#[test]
fn test_parse_lang_types() {
  // Repo-relative (CARGO_MANIFEST_DIR's parent is the repo root, `core`'s
  // sibling `lang/` -- mirrors `core_check_module.rs`'s `repo_search_paths`),
  let types_mo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
    .parent()
    .expect("core crate's manifest dir has a parent directory")
    .join("lang/types.mo");
  let source = std::fs::read_to_string(&types_mo)
    .unwrap_or_else(|e| panic!("Failed to read {}: {e}", types_mo.display()));
  let lines: Vec<&str> = source.lines().collect();
  println!("lang/types.mo has {} lines", lines.len());

  let result = parse_file(&source);
  if let Err(ref err) = result {
    let (line, col) = error::get_error_line_column(&err.source, &err.error);
    println!("Parse error at line {}, column {}", line, col);
    println!("Error: {}", err);

    // Check if error is at 4:16
    if line == 4 && col == 16 {
      panic!("Error at 4:16 in lang/types.mo!");
    }
  }
  assert!(result.is_ok(), "lang/types.mo should parse successfully");
}

// ============================================================================
// Tests for return and let..in in do notation issues
// ============================================================================

/// Test that return inside if without do block produces a parse error
/// This is illegal: return is only valid as a top-level do_statement
#[test]
fn test_return_inside_if_without_do() {
  let input = r#"def test : IO I64 {
    if true then
        return 42
    else
        return 0
}"#;
  let result = parse_file(input);

  assert!(
    result.is_err(),
    "Should fail to parse return inside if without do"
  );

  if let Err(ref err) = result {
    let (line, col) = error::get_error_line_column(&err.source, &err.error);
    // Error should be at or near the 'return' keyword on line 3
    assert_eq!(
      line, 3,
      "Error should be on line 3 (the 'return' line), got line {}",
      line
    );
    assert!(
      col >= 9 && col <= 15,
      "Error column should be near 'return' (position 9-15), got col {}",
      col
    );
  }
}

/// Test that return inside if with do block is legal
#[test]
fn test_return_inside_if_with_do() {
  let input = r#"def test : IO I64 {
    if true then do {
        return 42
    } else do {
        return 0
    }
}"#;
  let result = parse_file(input);
  // This should parse successfully
  assert!(result.is_ok(), "Return inside if with do should be legal");
}

/// Test that a bare `return` as a match arm body (no enclosing `do`) produces
/// a parse error, matching the same restriction as `if` branches above.
/// This is the exact pattern that broke lang/module.mo's `load_module_decls`:
/// `match result { Foo _ x => return Bar.baz x, ... }` without wrapping the
/// arm body in `do { }`.
#[test]
fn test_return_inside_match_without_do() {
  let input = r#"def test : IO I64 {
    match true {
        true => return 42,
        false => return 0
    }
}"#;
  let result = parse_file(input);

  assert!(
    result.is_err(),
    "Should fail to parse return inside match arm without do"
  );
}

/// Test that return inside a match arm wrapped in its own do block is legal.
#[test]
fn test_return_inside_match_with_do() {
  let input = r#"def test : IO I64 {
    match true {
        true => do { return 42 },
        false => do { return 0 }
    }
}"#;
  let result = parse_file(input);
  assert!(
    result.is_ok(),
    "Return inside match arm with do should be legal"
  );
}

/// Test that let..in inside do block produces a parse error
/// let..in is not valid inside do blocks; use let..:=; instead
#[test]
fn test_let_in_inside_do_block() {
  let input = r#"def test : IO I64 {
    let x := 42 in
    return x
}"#;
  let result = parse_file(input);

  assert!(
    result.is_err(),
    "Should fail to parse let..in inside do block"
  );

  if let Err(ref err) = result {
    let (line, col) = error::get_error_line_column(&err.source, &err.error);
    // Error should be at or near the 'in' keyword on line 2
    assert_eq!(
      line, 2,
      "Error should be on line 2 (the 'let..in' line), got line {}",
      line
    );
    // 'in' is at column 17 (0-indexed: "let x := 42 in" -> 'i' is at position 14, 'n' at 15)
    assert!(
      col >= 14 && col <= 17,
      "Error column should be near 'in' (position 14-17), got col {}",
      col
    );
  }
}

/// Test error position in module with many declarations
/// This ensures that error positions are correct even after parsing many valid declarations
#[test]
fn test_error_position_many_decls() {
  let input = r#"use io
open IO
use process
use lang.types
use lang.codegen.ir
use lang.codegen.emit
use lang.module
use lang.parser
use lang.pretty
use lang.parser.core
use lang.parser.combinators
use lang.typecheck.infer
use lang.scope
use std.list

open LLVMType
open LLVMValue
open Term
open Literal
open DebugName
open ParseResult
def valid_decl : I64 := 42
def another_valid : I64 := 100
def test : IO I64 {
    if true then
        return 42
    else
        return 0
}
def more_decls : I64 := 50"#;

  let result = parse_file(input);

  assert!(
    result.is_err(),
    "Should fail to parse return inside if without do"
  );

  if let Err(ref err) = result {
    let (line, col) = error::get_error_line_column(&err.source, &err.error);
    // Error should be on the line with the return statement (line 26)
    assert_eq!(
      line, 26,
      "Error should be on line 26 (the 'return' line), got line {}",
      line
    );
    // 'return' starts at column 9 (8 spaces + 1)
    assert!(
      col >= 9 && col <= 15,
      "Error column should be near 'return' (position 9-15), got col {}",
      col
    );
  }
}
