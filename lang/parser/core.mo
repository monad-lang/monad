/// Self-hosted Monad grammar parser core types and constants.

use lang.types {mk}
use std.list {length}


type ParseError {
	tag String,
	custom String,
	}


type ParseResult O {
	success (remaining: String) (output: O),
	fail (error: ParseError)
	}




type OpEntry {
	mk (op_str: String) (prec: I64) (right_assoc: Bool)
	}


def op_chars : List String :=
	["+", "&", "=", "|", "<", ">", "*", "/", "-", "!", ".", "@"]


def op_table : List OpEntry :=
	[OpEntry.mk "|>" 5 false,
	 OpEntry.mk "<|" 5 true,
	 OpEntry.mk ">>=" 10 true,
	 OpEntry.mk "." 12 true,
	 OpEntry.mk "<*>" 15 false,
	 OpEntry.mk "<|>" 20 false,
	 OpEntry.mk "||" 25 true,
	 OpEntry.mk "&&" 30 true,
	 OpEntry.mk "==" 40 false,
	 OpEntry.mk "!=" 40 false,
	 OpEntry.mk "++" 50 true,
	 // No built-in meaning — see the matching `tag("@")` entry in
	 // `core/src/parser.rs`'s `infix_symbol`/`operator_precedence`.
	 OpEntry.mk "@" 50 true,
	 OpEntry.mk ">>" 60 false,
	 OpEntry.mk "<<" 60 false,
	 OpEntry.mk "+" 65 false,
	 OpEntry.mk "-" 65 false,
	 OpEntry.mk "*" 70 false,
	 OpEntry.mk "/" 70 false]


#[partial]
def op_char_member (c : String) (chars : List String) : Bool := 
	match chars {
		List.cons ch rest => if String.beq ch c then true else op_char_member c rest,
		List.empty => false
		}


#[partial]
def op_entry_name (entry : OpEntry) : String := 
	match entry {
		OpEntry.mk o _ _ => o
		}


#[partial]
def op_entry_prec (entry : OpEntry) : I64 := 
	match entry {
		OpEntry.mk _ p _ => p
		}


#[partial]
def op_entry_rassoc (entry : OpEntry) : Bool := 
	match entry {
		OpEntry.mk _ _ r => r
		}


#[partial]
def op_lookup_prec (op_str : String) (table : List OpEntry) : I64 := 
	match table {
		List.cons entry rest =>
			if String.beq (op_entry_name entry) op_str then op_entry_prec entry
			else op_lookup_prec op_str rest,
		List.empty => 0
		}


#[partial]
def op_lookup_rassoc (op_str : String) (table : List OpEntry) : Bool := 
	match table {
		List.cons entry rest =>
			if String.beq (op_entry_name entry) op_str then op_entry_rassoc entry
			else op_lookup_rassoc op_str rest,
		List.empty => false
		}


def kw_list : List String := 
	["def", "let", "in", "use", "open", "class", "struct", "instance",
	 "type", "fn", "match", "if", "then", "else", "infix",
	 "do", "return", "for", "quote", "with"]


#[partial]
def kw_member (s : String) (kws : List String) : Bool := 
	match kws {
		List.cons kw rest => if String.beq kw s then true else kw_member s rest,
		List.empty => false
		}


def is_empty (s : String) : Bool := (String.length s) == 0

