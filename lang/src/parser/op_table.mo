/// Monad's operator table: which characters can form an operator, and each
/// operator's precedence and associativity.
///
/// Split out of `parser/core.mo`, which is otherwise generic. This file is the
/// opposite -- every entry below is a fact about THIS language's grammar, so a
/// parser substrate reused elsewhere must not carry it.

use parsec::core {ParseResult}

pub type OpEntry {
	mk (op_str: String) (prec: I64) (right_assoc: Bool)
	}


pub def op_chars : List String :=
	["+", "&", "=", "|", "<", ">", "*", "/", "-", "!", ".", "@"]


pub def op_table : List OpEntry :=
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
	 // Same precedence level as ==/!= (40), matching the Rust
	 // reference's operator_precedence (rust/core/src/parser.rs) exactly --
	 // missing here, `infix (<) := BOrd.lt`/`infix (>) := BOrd.gt`
	 // (init/prelude.mo) rejected as "unknown operator" (op_check,
	 // lang/parser.mo), which truncated the ENTIRE rest of prelude.mo
	 // under decls_parser's lenient truncate-on-failure behavior --
	 // silently dropping every later declaration (List.last,
	 // Option.get_or_default, ...) from self-hosted-compiled programs'
	 // dependency loading. <=/>= added too for the same parity, even
	 // though nothing currently declares them via `infix (...)`.
	 OpEntry.mk "<" 40 false,
	 OpEntry.mk ">" 40 false,
	 OpEntry.mk "<=" 40 false,
	 OpEntry.mk ">=" 40 false,
	 OpEntry.mk "++" 50 true,
	 // No built-in meaning — see the matching `tag("@")` entry in
	 // `rust/core/src/parser.rs`'s `infix_symbol`/`operator_precedence`.
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


/// Single-scan lookup returning the whole matching `OpEntry`, so a
/// caller that needs BOTH precedence and associativity for the same
/// operator (`lang/parser.mo`'s `expr_climb_op_prec`/
/// `expr_climb_op_rhs_ws`, on the same call path for every operator
/// token in every expression parsed) walks `table` once instead of
/// calling `op_lookup_prec` and `op_lookup_rassoc` separately.
/// `op_lookup_prec`/`op_lookup_rassoc` themselves stay as-is for
/// call sites that only need one or the other (e.g. `op_precedence`).
#[partial]
def op_lookup_entry (op_str : String) (table : List OpEntry) : Option OpEntry :=
	match table {
		List.cons entry rest =>
			if String.beq (op_entry_name entry) op_str then Option.some entry
			else op_lookup_entry op_str rest,
		List.empty => Option.none
		}
