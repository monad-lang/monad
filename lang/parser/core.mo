/// Self-hosted Monad grammar parser core types and constants.

use lang.types {mk}
use std.list {length}


/// Every `fail` value carries not just a message but the input
/// remaining right at the point of failure (`remaining` below) — this
/// is what lets `lang/parser/position.mo`'s `location_of_remaining`
/// recover a real line:column for a diagnostic (by diffing `remaining`
/// against the original full source text) without needing to thread a
/// `LocatedSpan` through every one of this parser's ~450 grammar
/// functions the way the Rust reference does (nom-locate,
/// core/src/parser/locate.rs) — `ParseError` is the only type that
/// needed to change, not `ParseResult` itself. See
/// `location_of_remaining`'s own doc comment for the full rationale.
type ParseError {
	tag (expected: String) (remaining: String),
	custom (msg: String) (remaining: String),
	}

/// Pull `remaining` back out of an already-failed `ParseError` — for the
/// handful of call sites that want to re-describe a failure with a more
/// helpful message (e.g. "expected ] after class constraint" instead of
/// a bare "tag ]") but don't have a conveniently-in-scope `orig`/`rem`
/// local to attach; the wrapped error's own `remaining` is exactly the
/// right position to reuse, since it's the same failure being
/// re-described, not a new one.
#[partial]
def parse_error_remaining (e : ParseError) : String :=
	match e {
		tag _ remaining => remaining,
		custom _ remaining => remaining,
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
	 // Same precedence level as ==/!= (40), matching the Rust
	 // reference's operator_precedence (core/src/parser.rs) exactly --
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

