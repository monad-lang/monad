// Pure tests for motes/sql's value/row/error layer. No IO and no FFI, so
// these run under both the Rust host and the self-hosted compiler.

use std::test {}
use std::list {List.length}
use lib::value {*}

def row_of (cells : List (Pair String Value)) : Row :=
    let r : Row := { cells := cells } in r

def error_is_type_mismatch (e : SqlError) : Bool :=
    match e {
        SqlError.type_mismatch _ => true,
        _ => false
    }

def i64_result_is_type_mismatch (r : Result SqlError I64) : Bool :=
    match r {
        Result.err e => error_is_type_mismatch e,
        Result.ok _ => false
    }

#[test]
def test_value_as_i64 : Bool :=
    match Value.as_i64 (Value.integer 42) {
        Result.ok n => n == 42,
        Result.err _ => false
    }

#[test]
def test_value_as_i64_rejects_text : Bool :=
    i64_result_is_type_mismatch (Value.as_i64 (Value.text "42"))

#[test]
def test_value_as_text : Bool :=
    match Value.as_text (Value.text "hi") {
        Result.ok s => String.beq s "hi",
        Result.err _ => false
    }

#[test]
def test_value_as_bool_accepts_boolean : Bool :=
    match Value.as_bool (Value.boolean true) {
        Result.ok b => b,
        Result.err _ => false
    }

#[test]
def test_value_as_bool_accepts_integer : Bool :=
    match Value.as_bool (Value.integer 1) {
        Result.ok b => b,
        Result.err _ => false
    }

#[test]
def test_value_as_bool_rejects_zero : Bool :=
    match Value.as_bool (Value.integer 0) {
        Result.ok b => Bool.not b,
        Result.err _ => false
    }

#[test]
def test_value_as_blob : Bool :=
    match Value.as_blob (Value.blob [1u8, 2u8]) {
        Result.ok bytes => List.length bytes == 2,
        Result.err _ => false
    }

def row_text_is (r : Row) (name : String) (expected : String) : Bool :=
    match Row.get_text r name {
        Result.ok s => String.beq s expected,
        Result.err _ => false
    }

#[test]
def test_row_get_finds_cell : Bool :=
    let r := row_of [Pair.pair "id" (Value.integer 7), Pair.pair "name" (Value.text "ada")] in
    match Row.get r "name" {
        Option.some _ => row_text_is r "name" "ada",
        Option.none => false
    }

#[test]
def test_row_get_missing_is_none : Bool :=
    let r := row_of [Pair.pair "id" (Value.integer 7)] in
    match Row.get r "absent" {
        Option.some _ => false,
        Option.none => true
    }

#[test]
def test_row_get_i64 : Bool :=
    let r := row_of [Pair.pair "id" (Value.integer 7)] in
    match Row.get_i64 r "id" {
        Result.ok n => n == 7,
        Result.err _ => false
    }

#[test]
def test_row_get_i64_missing_column : Bool :=
    let r := row_of List.empty in
    i64_result_is_type_mismatch (Row.get_i64 r "id")

#[test]
def test_row_get_text : Bool :=
    let r := row_of [Pair.pair "name" (Value.text "ada")] in
    match Row.get_text r "name" {
        Result.ok s => String.beq s "ada",
        Result.err _ => false
    }

#[test]
def test_sql_error_message : Bool :=
    let e : SqlError := SqlError.backend "no such table" 1 in
    String.beq (SqlError.message e) "no such table"

#[test]
def test_sql_error_code : Bool :=
    let e : SqlError := SqlError.backend "no such table" 5 in
    SqlError.code e == 5

def and_then_ok : Result String I64 :=
    SqlResult.and_then (Result.ok 41) (fn (n : I64) => Result.ok (n + 1))

#[test]
def test_and_then_ok : Bool :=
    match and_then_ok {
        Result.ok n => n == 42,
        Result.err _ => false
    }

def and_then_short_circuit : Result String I64 :=
    SqlResult.and_then (Result.err "boom") (fn (n : I64) => Result.ok (n + 1))

#[test]
def test_and_then_short_circuits : Bool :=
    match and_then_short_circuit {
        Result.ok _ => false,
        Result.err e => String.beq e "boom"
    }
