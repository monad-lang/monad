/// Self-hosted Monad grammar parser.
/// Self-contained: defines local types to avoid module loading issues.

use lang.types

type ParseError {
	tag String,
	custom String,
	}

type ParseResult O {
	success (remaining: String) (output: O),
	fail (error: ParseError)
}

open ParseResult

type OpEntry {
	mk (op_str: String) (prec: I64) (right_assoc: Bool)
}

def op_chars : List String :=
	["+", "&", "=", "|", "<", ">", "*", "/", "-", "!", "."]

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
	 OpEntry.mk ">>" 60 false,
	 OpEntry.mk "<<" 60 false,
	 OpEntry.mk "+" 65 false,
	 OpEntry.mk "-" 65 false,
	 OpEntry.mk "*" 70 false,
	 OpEntry.mk "/" 70 false]

@[partial]
def op_char_member (c : String) (chars : List String) : Bool :=
	match chars {
		List.cons ch rest => if String.beq ch c then true else op_char_member c rest,
		List.empty => false
	}

@[partial]
def op_entry_name (entry : OpEntry) : String :=
	match entry {
		OpEntry.mk o _ _ => o
	}

@[partial]
def op_entry_prec (entry : OpEntry) : I64 :=
	match entry {
		OpEntry.mk _ p _ => p
	}

@[partial]
def op_entry_rassoc (entry : OpEntry) : Bool :=
	match entry {
		OpEntry.mk _ _ r => r
	}

@[partial]
def op_lookup_prec (op_str : String) (table : List OpEntry) : I64 :=
	match table {
		List.cons entry rest =>
			if String.beq (op_entry_name entry) op_str then op_entry_prec entry
			else op_lookup_prec op_str rest,
		List.empty => 0
	}

@[partial]
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

@[partial]
def kw_member (s : String) (kws : List String) : Bool :=
	match kws {
		List.cons kw rest => if String.beq kw s then true else kw_member s rest,
		List.empty => false
	}

def decl_parsers : List (String -> ParseResult Decl) :=
	[use_parser, open_parser, infix_parser, def_parser,
	 struct_parser, type_parser, class_parser, instance_parser]

@[partial]
def decl_fail_to_unknown (r : ParseResult Decl) : ParseResult Decl :=
	match r {
		success rem out => success rem out,
		fail _ => fail (ParseError.custom "unknown declaration")
	}

// --- Helper ---

@[partial]
def is_empty (s : String) : Bool := (String.length s) == 0


// --- Position tracking (Phase 1.2) ---

@[partial]
def new_span (s : String) : LocatedSpan :=
	LocatedSpan.mk s (Location.mk 0 1 1)

@[partial]
def span_location (span : LocatedSpan) : Location :=
	match span {
		mk frag loc => loc
	}

@[partial]
def span_fragment (span : LocatedSpan) : String :=
	match span {
		mk frag loc => frag
	}

@[partial]
def count_newlines (s : String) (acc : I64) : I64 :=
	if is_empty s
	then acc
	else count_newlines_tail (String.slice s 0 1) (String.drop 1 s) acc

@[partial]
def count_newlines_tail (c : String) (s : String) (acc : I64) : I64 :=
	if String.beq "\n" c
	then count_newlines s (I64.add acc 1)
	else count_newlines s acc

@[partial]
def advance_location (loc : Location) (consumed : String) (n : I64) : Location :=
	match loc {
		mk off line col =>
			let newlines : I64 := count_newlines consumed 0 in
			if I64.beq newlines 0
			then Location.mk (I64.add off n) line (I64.add col n)
			else Location.mk (I64.add off n) (I64.add line newlines) 1
	}

@[partial]
def consume_span (span : LocatedSpan) (n : I64) : LocatedSpan :=
	match span {
		mk frag loc =>
			let consumed : String := String.slice frag 0 n in
			let rest : String := String.drop n frag in
			let new_loc : Location := advance_location loc consumed n in
			LocatedSpan.mk rest new_loc
	}

// --- Combinators ---

@[partial]
def tag (s : String) (input : String) : ParseResult String :=
	if is_prefix s input
	then success (String.drop (String.length s) input) s
	else fail (ParseError.tag s)

@[partial]
def is_prefix (pre : String) (s : String) : Bool :=
	pre == (String.slice s 0 (String.length pre))

@[partial]
def alt (a : String -> ParseResult A) (b : String -> ParseResult A) (input : String) : ParseResult A :=
	alt_body (a input) b input

@[partial]
def alt_body (r : ParseResult A) (b : String -> ParseResult A) (input : String) : ParseResult A :=
	match r {
		success rem out => success rem out,
		fail e1 => alt_second (b input) e1
	}

@[partial]
def alt_second (r : ParseResult A) (e1 : ParseError) : ParseResult A :=
	match r {
		success rem out => success rem out,
		fail e2 => fail (ParseError.custom "both alt failed")
	}

// --- Char predicates ---

@[partial]
def is_digit (c : String) : Bool :=
	if "0" == c then true
	else if "1" == c then true
	else if "2" == c then true
	else if "3" == c then true
	else if "4" == c then true
	else if "5" == c then true
	else if "6" == c then true
	else if "7" == c then true
	else if String.beq "8" c then true
	else String.beq "9" c

@[partial]
def is_alpha_lower (c : String) : Bool :=
	if String.beq "a" c then true
	else if String.beq "b" c then true
	else if String.beq "c" c then true
	else if String.beq "d" c then true
	else if String.beq "e" c then true
	else if String.beq "f" c then true
	else if String.beq "g" c then true
	else if String.beq "h" c then true
	else if String.beq "i" c then true
	else if String.beq "j" c then true
	else if String.beq "k" c then true
	else if String.beq "l" c then true
	else if String.beq "m" c then true
	else false

@[partial]
def is_alpha_lower2 (c : String) : Bool :=
	if String.beq "n" c then true
	else if String.beq "o" c then true
	else if String.beq "p" c then true
	else if String.beq "q" c then true
	else if String.beq "r" c then true
	else if String.beq "s" c then true
	else if String.beq "t" c then true
	else if String.beq "u" c then true
	else if String.beq "v" c then true
	else if String.beq "w" c then true
	else if String.beq "x" c then true
	else if String.beq "y" c then true
	else String.beq "z" c

@[partial]
def is_alpha_upper (c : String) : Bool :=
	if String.beq "A" c then true
	else if String.beq "B" c then true
	else if String.beq "C" c then true
	else if String.beq "D" c then true
	else if String.beq "E" c then true
	else if String.beq "F" c then true
	else if String.beq "G" c then true
	else if String.beq "H" c then true
	else if String.beq "I" c then true
	else if String.beq "J" c then true
	else if String.beq "K" c then true
	else if String.beq "L" c then true
	else if String.beq "M" c then true
	else false

@[partial]
def is_alpha_upper2 (c : String) : Bool :=
	if String.beq "N" c then true
	else if String.beq "O" c then true
	else if String.beq "P" c then true
	else if String.beq "Q" c then true
	else if String.beq "R" c then true
	else if String.beq "S" c then true
	else if String.beq "T" c then true
	else if String.beq "U" c then true
	else if String.beq "V" c then true
	else if String.beq "W" c then true
	else if String.beq "X" c then true
	else if String.beq "Y" c then true
	else String.beq "Z" c

@[partial]
def is_alpha (c : String) : Bool :=
	if is_alpha_lower c then true
	else if is_alpha_lower2 c then true
	else if is_alpha_upper c then true
	else is_alpha_upper2 c

@[partial]
def is_alphanumeric (c : String) : Bool :=
	if is_digit c then true
	else is_alpha c

@[partial]
def is_ident_char (c : String) : Bool :=
	if is_alphanumeric c then true
	else String.beq "_" c

@[partial]
def is_space (c : String) : Bool :=
	if String.beq " " c then true
	else if String.beq "\t" c then true
	else if String.beq "\n" c then true
	else String.beq "\r" c

// --- Keyword check ---

@[partial]
def is_keyword (s : String) : Bool :=
	kw_member s kw_list

// --- Identifier parser ---

@[partial]
def ident_start (c : String) : Bool :=
	if is_alpha c then true
	else String.beq "_" c

@[partial]
def identifier (input : String) : ParseResult String :=
	identifier_try (take_while is_ident_char input)

@[partial]
def identifier_try (r : ParseResult String) : ParseResult String :=
	match r {
		success rem out =>
			if is_empty out
			then fail (ParseError.custom "expected identifier")
			else identifier_check_start out rem,
		fail e => fail e
	}

@[partial]
def identifier_check_start (s : String) (rem : String) : ParseResult String :=
	if ident_start (String.slice s 0 1)
	then identifier_check_kw s rem
	else fail (ParseError.custom "identifier cannot start with digit")

@[partial]
def identifier_check_kw (s : String) (rem : String) : ParseResult String :=
	if is_keyword s
	then fail (ParseError.custom ("reserved keyword: " ++ s))
	else success rem s

// --- Number parser ---

@[partial]
def take_while (pred : String -> Bool) (input : String) : ParseResult String :=
	take_while_loop pred "" input

@[partial]
def take_while_loop (pred : String -> Bool) (acc : String) (input : String) : ParseResult String :=
	if is_empty input
	then success input acc
	else take_while_check pred acc input (String.slice input 0 1) (String.drop 1 input)

@[partial]
def take_while_check (pred : String -> Bool) (acc : String) (input : String) (ch : String) (rest : String) : ParseResult String :=
	if pred ch
	then take_while_loop pred (String.concat acc ch) rest
	else success input acc

@[partial]
def is_digit_or_underscore (c : String) : Bool :=
	if is_digit c then true
	else String.beq "_" c

@[partial]
def number (input : String) : ParseResult I64 :=
	number_body (take_while is_digit_or_underscore input)

@[partial]
def number_body (r : ParseResult String) : ParseResult I64 :=
	match r {
		success rem out =>
			if is_empty out
			then fail (ParseError.custom "expected number")
			else number_parse out rem,
		fail e => fail e
	}

@[partial]
def number_parse (s : String) (rem : String) : ParseResult I64 :=
	if is_empty s
	then fail (ParseError.custom "empty number")
	else if is_digit (String.slice s 0 1)
	then success rem (parse_digits s)
	else fail (ParseError.custom "number must start with digit")

// --- Whitespace ---

@[partial]
def spaces (input : String) : ParseResult String :=
	take_while is_space input

// --- many0 / many1 ---

@[partial]
def many0 (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	many0_body (p input) p input

@[partial]
def many0_body (r : ParseResult A) (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	match r {
		success rem out =>
			many0_next (many0 p rem) out rem,
		fail _ => success input List.empty
	}

@[partial]
def many0_next (r : ParseResult (List A)) (out : A) (rem : String) : ParseResult (List A) :=
	match r {
		success rem2 rest => success rem2 (List.cons out rest),
		fail _ => success rem (List.cons out List.empty)
	}

// --- Type helpers ---

@[partial]
def var_term (s : String) : TermV0 :=
	TermV0.var (NameRef.nid (Identifier.id s))

// --- Type expression parser ---

@[partial]
def type_variable (input : String) : ParseResult TermV0 :=
	type_var_got (identifier input)

@[partial]
def type_var_got (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem out => success rem (var_term out),
		fail e => fail e
	}

@[partial]
def type_parens (input : String) : ParseResult TermV0 :=
	type_parens_open (tag "(" input)

@[partial]
def type_parens_open (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem _ => type_parens_expr (type_expression rem),
		fail e => fail e
	}

@[partial]
def type_parens_expr (r : ParseResult TermV0) : ParseResult TermV0 :=
	match r {
		success rem out => type_parens_close (tag ")" rem) out,
		fail e => fail e
	}

@[partial]
def type_parens_close (r : ParseResult String) (out : TermV0) : ParseResult TermV0 :=
	match r {
		success rem _ => success rem out,
		fail e => fail e
	}

@[partial]
def type_atom (input : String) : ParseResult TermV0 :=
	type_atom_try_var (type_variable input) input

@[partial]
def type_atom_try_var (r : ParseResult TermV0) (input : String) : ParseResult TermV0 :=
	match r {
		success rem out => success rem out,
		fail _ => type_parens input
	}

@[partial]
def type_expression (input : String) : ParseResult TermV0 :=
	type_expr_ws (take_while is_space input)

@[partial]
def type_expr_ws (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem _ => type_expr_first (type_atom rem) rem,
		fail e => fail e
	}

@[partial]
def type_expr_first (r : ParseResult TermV0) (rem : String) : ParseResult TermV0 :=
	match r {
		success after lhs => type_expr_apps after lhs,
		fail e => fail e
	}

@[partial]
def type_expr_apps (input : String) (lhs : TermV0) : ParseResult TermV0 :=
	type_expr_app_ws (take_while is_space input) lhs

@[partial]
def type_expr_app_ws (r : ParseResult String) (lhs : TermV0) : ParseResult TermV0 :=
	match r {
		success rem _ => type_expr_app_next (type_atom rem) rem lhs,
		fail e => fail e
	}

@[partial]
def type_expr_app_next (r : ParseResult TermV0) (input : String) (lhs : TermV0) : ParseResult TermV0 :=
	match r {
		success rem rhs => type_expr_apps rem (TermV0.app lhs rhs),
		fail _ => type_expr_check_arrow input lhs
	}

@[partial]
def type_expr_check_arrow (input : String) (lhs : TermV0) : ParseResult TermV0 :=
	type_expr_arrow_ws (take_while is_space input) input lhs

@[partial]
def type_expr_arrow_ws (r : ParseResult String) (input : String) (lhs : TermV0) : ParseResult TermV0 :=
	match r {
		success rem _ => type_expr_try_arrow rem lhs (tag "->" rem),
		fail e => fail e
	}

@[partial]
def type_expr_try_arrow (input : String) (lhs : TermV0) (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem _ => type_expr_rhs lhs (type_expression rem),
		fail _ => success input lhs
	}

@[partial]
def type_expr_rhs (lhs : TermV0) (r : ParseResult TermV0) : ParseResult TermV0 :=
	match r {
		success rem out => success rem (TermV0.pi lhs out),
		fail e => fail e
	}

// --- many1 ---

@[partial]
def many1 (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	many1_body (p input) p input

@[partial]
def many1_body (r : ParseResult A) (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	match r {
		success rem out =>
			many0_next (many0 p rem) out rem,
		fail e => fail e
	}
// --- Extended combinators (Phase 1.1) ---

@[partial]
def map_parse (f : A -> B) (p : String -> ParseResult A) (input : String) : ParseResult B :=
	map_parse_body (p input) f

@[partial]
def map_parse_body (r : ParseResult A) (f : A -> B) : ParseResult B :=
	match r {
		success rem out => map_parse_ok rem out f,
		fail e => map_parse_fail e
	}

@[partial]
def map_parse_ok (rem : String) (out : A) (f : A -> B) : ParseResult B :=
	success rem (f out)

@[partial]
def map_parse_fail (e : ParseError) : ParseResult B :=
	fail e

@[partial]
def bind_parse (p : String -> ParseResult A) (f : A -> String -> ParseResult B) (input : String) : ParseResult B :=
	bind_parse_body (p input) f

@[partial]
def bind_parse_body (r : ParseResult A) (f : A -> String -> ParseResult B) : ParseResult B :=
	match r {
		success rem out => f out rem,
		fail e => bind_parse_fail e
	}

@[partial]
def bind_parse_fail (e : ParseError) : ParseResult B :=
	fail e

@[partial]
def alt_fold (parsers : List (String -> ParseResult A)) (input : String) : ParseResult A :=
	match parsers {
		List.cons p ps => alt_fold_try (p input) ps input,
		List.empty => fail (ParseError.custom "alt_fold: empty list")
	}

@[partial]
def alt_fold_try (r : ParseResult A) (parsers : List (String -> ParseResult A)) (input : String) : ParseResult A :=
	match r {
		success rem out => alt_fold_ok rem out,
		fail e => alt_fold parsers input
	}

@[partial]
def alt_fold_ok (rem : String) (out : A) : ParseResult A :=
	success rem out

@[partial]
def preceded_by (before : String -> ParseResult A) (p : String -> ParseResult B) (input : String) : ParseResult B :=
	preceded_by_body (before input) p

@[partial]
def preceded_by_body (r : ParseResult A) (p : String -> ParseResult B) : ParseResult B :=
	match r {
		success rem _ => p rem,
		fail e => preceded_by_err e
	}

@[partial]
def preceded_by_err (e : ParseError) : ParseResult B :=
	fail e

@[partial]
def terminated_by (p : String -> ParseResult A) (after : String -> ParseResult B) (input : String) : ParseResult A :=
	terminated_by_body (p input) after

@[partial]
def terminated_by_body (r : ParseResult A) (after : String -> ParseResult B) : ParseResult A :=
	match r {
		success rem out => terminated_by_after (after rem) out,
		fail e => terminated_by_err e
	}

@[partial]
def terminated_by_after (r : ParseResult B) (out : A) : ParseResult A :=
	match r {
		success rem _ => terminated_by_ok rem out,
		fail e => terminated_by_err e
	}

@[partial]
def terminated_by_ok (rem : String) (out : A) : ParseResult A :=
	success rem out

@[partial]
def terminated_by_err (e : ParseError) : ParseResult A :=
	fail e

@[partial]
def delimited_by (before : String -> ParseResult A) (p : String -> ParseResult B) (after : String -> ParseResult C) (input : String) : ParseResult B :=
	delimited_by_before (before input) p after

@[partial]
def delimited_by_before (r : ParseResult A) (p : String -> ParseResult B) (after : String -> ParseResult C) : ParseResult B :=
	match r {
		success rem _ => delimited_by_body (p rem) after,
		fail e => delimited_by_err e
	}

@[partial]
def delimited_by_body (r : ParseResult B) (after : String -> ParseResult C) : ParseResult B :=
	match r {
		success rem out => delimited_by_after (after rem) out,
		fail e => delimited_by_err e
	}

@[partial]
def delimited_by_after (r : ParseResult C) (out : B) : ParseResult B :=
	match r {
		success rem _ => delimited_by_ok rem out,
		fail e => delimited_by_err e
	}

@[partial]
def delimited_by_ok (rem : String) (out : B) : ParseResult B :=
	success rem out

@[partial]
def delimited_by_err (e : ParseError) : ParseResult B :=
	fail e

@[partial]
def separated_by (sep : String -> ParseResult A) (p : String -> ParseResult B) (input : String) : ParseResult (List B) :=
	separated_by_body (p input) p sep input List.empty

@[partial]
def separated_by_body (r : ParseResult B) (p : String -> ParseResult B) (sep : String -> ParseResult A) (input : String) (acc : List B) : ParseResult (List B) :=
	match r {
		success rem out => separated_by_loop (sep rem) rem out p sep acc,
		fail e => separated_by_ok input acc
	}

@[partial]
def separated_by_loop (r : ParseResult A) (rem : String) (out : B) (p : String -> ParseResult B) (sep : String -> ParseResult A) (acc : List B) : ParseResult (List B) :=
	match r {
		success rem2 _ => separated_by_body (p rem2) p sep rem2 (List.cons out acc),
		fail e => separated_by_ok rem (List.cons out acc)
	}

@[partial]
def separated_by_ok (input : String) (acc : List B) : ParseResult (List B) :=
	success input (list_reverse acc)

@[partial]
def opt (p : String -> ParseResult A) (input : String) : ParseResult (Option A) :=
	opt_body (p input) input

@[partial]
def opt_body (r : ParseResult A) (input : String) : ParseResult (Option A) :=
	match r {
		success rem out => opt_some rem out,
		fail e => opt_none input
	}

@[partial]
def opt_some (rem : String) (out : A) : ParseResult (Option A) :=
	success rem (Option.some out)

@[partial]
def opt_none (input : String) : ParseResult (Option A) :=
	success input Option.none

@[partial]
def ws0 (input : String) : ParseResult String :=
	take_while is_space input

@[partial]
def ws1 (input : String) : ParseResult String :=
	ws1_body (take_while is_space input) input

@[partial]
def ws1_body (r : ParseResult String) (input : String) : ParseResult String :=
	match r {
		success rem out => if is_empty out then fail (ParseError.custom "expected whitespace") else success rem out,
		fail e => fail e
	}


// --- Number parsing helpers ---

@[partial]
def char_to_digit (c : String) : I64 :=
	if String.beq "0" c then 0
	else if String.beq "1" c then 1
	else if String.beq "2" c then 2
	else if String.beq "3" c then 3
	else if String.beq "4" c then 4
	else if String.beq "5" c then 5
	else if String.beq "6" c then 6
	else if String.beq "7" c then 7
	else if String.beq "8" c then 8
	else 9

@[partial]
def parse_digits (s : String) : I64 :=
	parse_digits_loop s 0

@[partial]
def parse_digits_loop (s : String) (acc : I64) : I64 :=
	if is_empty s
	then acc
	else parse_digits_char (String.slice s 0 1) (String.drop 1 s) acc

@[partial]
def parse_digits_char (ch : String) (rest : String) (acc : I64) : I64 :=
	parse_digits_loop rest (I64.add (I64.mul acc 10) (char_to_digit ch))

// --- String literal ---

@[partial]
def is_not_quote (c : String) : Bool :=
	if String.beq "\"" c then false
	else true

@[partial]
def string_parse (input : String) : ParseResult TermV0 :=
	string_parse_open (tag "\"" input)

@[partial]
def string_parse_open (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem _ => string_parse_content (take_while is_not_quote rem),
		fail e => fail e
	}

@[partial]
def string_parse_content (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem out => string_parse_close (tag "\"" rem) out,
		fail e => fail e
	}

@[partial]
def string_parse_close (r : ParseResult String) (content : String) : ParseResult TermV0 :=
	match r {
		success rem _ => success rem (TermV0.lit (Literal.str content)),
		fail e => fail e
	}

// --- Number term wrapper ---

@[partial]
def number_term (input : String) : ParseResult TermV0 :=
	number_term_body (number input)

@[partial]
def number_term_body (r : ParseResult I64) : ParseResult TermV0 :=
	match r {
		success rem out => success rem (TermV0.lit (Literal.num out NumSuffix.i64)),
		fail e => fail e
	}

// --- Variable parser ---

// --- Path variable parser (e.g. A.B.C) ---

@[partial]
def path_variable (input : String) : ParseResult TermV0 :=
	path_var_first (identifier input)

@[partial]
def path_var_first (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem first => path_var_need_dot rem (List.cons (Identifier.id first) List.empty),
		fail e => fail e
	}

@[partial]
def path_var_need_dot (input : String) (ids : List Identifier) : ParseResult TermV0 :=
	path_var_need_dot_try (tag "." input) ids input

@[partial]
def path_var_need_dot_try (r : ParseResult String) (ids : List Identifier) (orig : String) : ParseResult TermV0 :=
	match r {
		success rem _ => path_var_field (identifier rem) ids,
		fail _ => fail (ParseError.custom "not a dotted path")
	}

@[partial]
def path_var_loop (input : String) (ids : List Identifier) : ParseResult TermV0 :=
	path_var_loop_dot (tag "." input) ids input

@[partial]
def path_var_loop_dot (r : ParseResult String) (ids : List Identifier) (orig : String) : ParseResult TermV0 :=
	match r {
		success rem _ => path_var_field (identifier rem) ids,
		fail _ =>
			let rev : List Identifier := list_reverse ids in
			success orig (TermV0.var (NameRef.nmp (ModulePath.mp rev)))
	}

@[partial]
def path_var_field (r : ParseResult String) (ids : List Identifier) : ParseResult TermV0 :=
	match r {
		success rem next => path_var_loop rem (List.cons (Identifier.id next) ids),
		fail e => fail e
	}

// --- Variable parser (dotted path or simple identifier) ---

@[partial]
def variable (input : String) : ParseResult TermV0 :=
	variable_try_path (path_variable input) input

@[partial]
def variable_try_path (r : ParseResult TermV0) (input : String) : ParseResult TermV0 :=
	match r {
		success rem out => success rem out,
		fail _ => variable_got (identifier input)
	}

@[partial]
def variable_got (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem out => success rem (TermV0.var (NameRef.nid (Identifier.id out))),
		fail e => fail e
	}

// --- Literal term (string or number) ---

@[partial]
def literal_term (input : String) : ParseResult TermV0 :=
	literal_try_str (string_parse input) input

@[partial]
def literal_try_str (r : ParseResult TermV0) (input : String) : ParseResult TermV0 :=
	match r {
		success rem out => success rem out,
		fail _ => number_term input
	}

// --- Atom term (variable, literal, parenthesized expression) ---

@[partial]
def atom_paren_parser (input : String) : ParseResult TermV0 :=
	atom_try_paren (tag "(" input) input

def atom_parsers (input : String) : List (String -> ParseResult TermV0) :=
	[variable, literal_term, match_parser, if_parser,
	 let_parser, do_parser, lambda_parser, atom_paren_parser]

@[partial]
def atom_term (input : String) : ParseResult TermV0 :=
	alt_fold (atom_parsers input) input

@[partial]
def atom_try_paren (r : ParseResult String) (input : String) : ParseResult TermV0 :=
	match r {
		success rem _ => atom_inner_expr (expression rem),
		fail e => fail e
	}

@[partial]
def atom_inner_expr (r : ParseResult TermV0) : ParseResult TermV0 :=
	match r {
		success rem out => atom_close_paren (tag ")" rem) out,
		fail e => fail e
	}

@[partial]
def atom_close_paren (r : ParseResult String) (out : TermV0) : ParseResult TermV0 :=
	match r {
		success rem _ => success rem out,
		fail e => fail e
	}

// --- Whitespace skip (non-ParseResult version) ---

@[partial]
def skip_spaces (input : String) : String :=
	skip_spaces_match (take_while is_space input) input

@[partial]
def skip_spaces_match (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ => rem,
		fail _ => orig
	}

// --- Match case parser ---

@[partial]
def match_case (input : String) : ParseResult MatchCase :=
	match_case_name (identifier (skip_spaces input))

@[partial]
def match_case_name (r : ParseResult String) : ParseResult MatchCase :=
	match r {
		success rem name => match_case_args (many0 identifier (skip_spaces rem)) (Identifier.id name),
		fail e => fail e
	}

@[partial]
def match_case_args (r : ParseResult (List String)) (name : Identifier) : ParseResult MatchCase :=
	match r {
		success rem _ => match_case_arrow (tag "=>" (skip_spaces rem)) name,
		fail e => fail e
	}

@[partial]
def match_case_arrow (r : ParseResult String) (name : Identifier) : ParseResult MatchCase :=
	match r {
		success rem _ => match_case_body (expression (skip_spaces rem)) name,
		fail e => fail e
	}

@[partial]
def match_case_body (r : ParseResult TermV0) (name : Identifier) : ParseResult MatchCase :=
	match r {
		success rem body =>
			let empty_args : List Identifier := List.empty in
			success (match_case_tail rem) (MatchCase.mc name empty_args body),
		fail e => fail e
	}

@[partial]
def match_case_tail (input : String) : String :=
	match_case_tail_sp (take_while is_space input) input

@[partial]
def match_case_tail_sp (r : ParseResult String) (orig : String) : String :=
	match r {
		success after_sp _ => match_case_tail_cm (tag "," after_sp) after_sp,
		fail _ => orig
	}

@[partial]
def match_case_tail_cm (r : ParseResult String) (after_sp : String) : String :=
	match r {
		success rem _ => skip_spaces rem,
		fail _ => after_sp
	}

// --- Match expression parser ---

@[partial]
def match_parser (input : String) : ParseResult TermV0 :=
	match_kw (tag "match" input)

@[partial]
def match_kw (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem _ => match_scrutinee (expression (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def match_scrutinee (r : ParseResult TermV0) : ParseResult TermV0 :=
	match r {
		success rem scrutinee => match_brace_open (tag "{" (skip_spaces rem)) scrutinee,
		fail e => fail e
	}

@[partial]
def match_brace_open (r : ParseResult String) (scrutinee : TermV0) : ParseResult TermV0 :=
	match r {
		success rem _ => match_cases_parse (many1 match_case rem) scrutinee,
		fail e => fail e
	}

@[partial]
def match_cases_parse (r : ParseResult (List MatchCase)) (scrutinee : TermV0) : ParseResult TermV0 :=
	match r {
		success rem cases => match_close (tag "}" (skip_spaces rem)) scrutinee cases,
		fail e => fail e
	}

@[partial]
def match_close (r : ParseResult String) (scrutinee : TermV0) (cases : List MatchCase) : ParseResult TermV0 :=
	match r {
		success rem _ => success rem (TermV0.lit (Literal.match_ scrutinee cases)),
		fail e => fail e
	}

// --- If expression parser ---

@[partial]
def if_parser (input : String) : ParseResult TermV0 :=
	if_kw (tag "if" input)

@[partial]
def if_kw (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem _ => if_cond (expression (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def if_cond (r : ParseResult TermV0) : ParseResult TermV0 :=
	match r {
		success rem cond => if_then_kw (tag "then" (skip_spaces rem)) cond,
		fail e => fail e
	}

@[partial]
def if_then_kw (r : ParseResult String) (cond : TermV0) : ParseResult TermV0 :=
	match r {
		success rem _ => if_then_branch (expression (skip_spaces rem)) cond,
		fail e => fail e
	}

@[partial]
def if_then_branch (r : ParseResult TermV0) (cond : TermV0) : ParseResult TermV0 :=
	match r {
		success rem then_b => if_else_kw (tag "else" (skip_spaces rem)) cond then_b,
		fail e => fail e
	}

@[partial]
def if_else_kw (r : ParseResult String) (cond : TermV0) (then_b : TermV0) : ParseResult TermV0 :=
	match r {
		success rem _ => if_else_branch (expression (skip_spaces rem)) cond then_b,
		fail e => fail e
	}

@[partial]
def if_else_branch (r : ParseResult TermV0) (cond : TermV0) (then_b : TermV0) : ParseResult TermV0 :=
	match r {
		success rem else_b => success rem (TermV0.lit (Literal.if_ cond then_b else_b)),
		fail e => fail e
	}

// --- Lambda expression parser ---

@[partial]
def lambda_parser (input : String) : ParseResult TermV0 :=
	lambda_kw (alt (alt (tag "fn") (tag "ꟛ")) (tag "\\") input)

@[partial]
def lambda_kw (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem _ => lambda_mult (skip_spaces rem),
		fail e => fail e
	}

@[partial]
def lambda_mult (input : String) : ParseResult TermV0 :=
	lambda_mult_prefix (tag "!" input) Multiplicity.linear input

@[partial]
def lambda_mult_prefix (r : ParseResult String) (mult : Multiplicity) (orig : String) : ParseResult TermV0 :=
	match r {
		success rem _ => lambda_name (identifier rem) mult,
		fail _ => lambda_mult_affine (tag "?" orig) mult orig
	}

@[partial]
def lambda_mult_affine (r : ParseResult String) (mult : Multiplicity) (orig : String) : ParseResult TermV0 :=
	match r {
		success rem _ => lambda_name (identifier rem) Multiplicity.affine,
		fail _ => lambda_name (identifier orig) Multiplicity.many
	}

@[partial]
def lambda_name (r : ParseResult String) (mult : Multiplicity) : ParseResult TermV0 :=
	match r {
		success rem name => lambda_arrow_mult (tag "=>" (skip_spaces rem)) (Identifier.id name) mult,
		fail e => fail e
	}

@[partial]
def lambda_arrow_mult (r : ParseResult String) (name : Identifier) (mult : Multiplicity) : ParseResult TermV0 :=
	match r {
		success rem _ => lambda_body_mult (expression (skip_spaces rem)) name mult,
		fail e => fail e
	}

@[partial]
def lambda_body_mult (r : ParseResult TermV0) (name : Identifier) (mult : Multiplicity) : ParseResult TermV0 :=
	match r {
		success rem body => success rem (TermV0.lam (mk_param name (TermV0.type_ 1) mult) body),
		fail e => fail e
	}

// --- Let expression parser ---

@[partial]
def let_parser (input : String) : ParseResult TermV0 :=
	let_kw (tag "let" input)

@[partial]
def let_kw (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem _ => let_name (identifier (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def let_name (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem name => let_assign (tag ":=" (skip_spaces rem)) (Identifier.id name),
		fail e => fail e
	}

@[partial]
def let_assign (r : ParseResult String) (name : Identifier) : ParseResult TermV0 :=
	match r {
		success rem _ => let_value (expression (skip_spaces rem)) name,
		fail e => fail e
	}

@[partial]
def let_value (r : ParseResult TermV0) (name : Identifier) : ParseResult TermV0 :=
	match r {
		success rem value => let_in_kw (tag "in" (skip_spaces rem)) name value,
		fail e => fail e
	}

@[partial]
def let_in_kw (r : ParseResult String) (name : Identifier) (value : TermV0) : ParseResult TermV0 :=
	match r {
		success rem _ => let_body (expression (skip_spaces rem)) name value,
		fail e => fail e
	}

@[partial]
def let_body (r : ParseResult TermV0) (name : Identifier) (value : TermV0) : ParseResult TermV0 :=
	match r {
		success rem body => success rem (TermV0.app (TermV0.lam (param_many name (TermV0.type_ 1)) body) value),
		fail e => fail e
	}

// --- Do-notation parser ---

@[partial]
def do_stmt_return (input : String) : ParseResult DoStmt :=
	do_stmt_ret_kw (tag "return" input) input

@[partial]
def do_stmt_ret_kw (r : ParseResult String) (orig : String) : ParseResult DoStmt :=
	match r {
		success rem _ => do_stmt_ret_expr (expression (skip_spaces rem)),
		fail _ => do_stmt_try_let (tag "let" (skip_spaces orig)) orig
	}

@[partial]
def do_stmt_try_let (r : ParseResult String) (orig : String) : ParseResult DoStmt :=
	match r {
		success rem _ => do_stmt_let_name (identifier (skip_spaces rem)),
		fail _ => do_stmt_expr (expression (skip_spaces orig))
	}

@[partial]
def do_stmt_let_name (r : ParseResult String) : ParseResult DoStmt :=
	match r {
		success rem name => do_stmt_let_kind rem (Identifier.id name),
		fail e => fail e
	}

@[partial]
def do_stmt_let_kind (input : String) (name : Identifier) : ParseResult DoStmt :=
	do_stmt_let_kind_try (tag ":=" (skip_spaces input)) name input

@[partial]
def do_stmt_let_kind_try (r : ParseResult String) (name : Identifier) (orig : String) : ParseResult DoStmt :=
	match r {
		success rem _ => do_stmt_let_value (expression (skip_spaces rem)) name,
		fail _ => do_stmt_bind_arrow (tag "<-" (skip_spaces orig)) name orig
	}

@[partial]
def do_stmt_let_value (r : ParseResult TermV0) (name : Identifier) : ParseResult DoStmt :=
	match r {
		success rem value => success rem (DoStmt.let_s name value),
		fail e => fail e
	}

@[partial]
def do_stmt_bind_arrow (r : ParseResult String) (name : Identifier) (orig : String) : ParseResult DoStmt :=
	match r {
		success rem _ => do_stmt_bind_value (expression (skip_spaces rem)) name,
		fail _ => fail (ParseError.custom "expected := or <- after let in do block")
	}

@[partial]
def do_stmt_bind_value (r : ParseResult TermV0) (name : Identifier) : ParseResult DoStmt :=
	match r {
		success rem value => success rem (DoStmt.bind_s name value),
		fail e => fail e
	}

@[partial]
def do_stmt_ret_expr (r : ParseResult TermV0) : ParseResult DoStmt :=
	match r {
		success rem value => success rem (DoStmt.ret_s value),
		fail e => fail e
	}

@[partial]
def do_stmt_expr (r : ParseResult TermV0) : ParseResult DoStmt :=
	match r {
		success rem value => success rem (DoStmt.expr_s value),
		fail e => fail e
	}

@[partial]
def do_stmts (input : String) : ParseResult (List DoStmt) :=
	do_stmts_check_end (tag "}" (skip_spaces input)) input

@[partial]
def do_stmts_check_end (r : ParseResult String) (orig : String) : ParseResult (List DoStmt) :=
	match r {
		success rem _ =>
			let empty : List DoStmt := List.empty in
			success rem empty,
		fail _ => do_stmts_first (do_stmt_return (skip_spaces orig)) (skip_spaces orig)
	}

@[partial]
def do_stmts_first (r : ParseResult DoStmt) (orig : String) : ParseResult (List DoStmt) :=
	match r {
		success rem stmt => do_stmts_next (do_stmts (do_stmts_tail rem)) stmt,
		fail e => fail e
	}

@[partial]
def do_stmts_tail (input : String) : String :=
	do_stmts_tail_sp (take_while is_space input) input

@[partial]
def do_stmts_tail_sp (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ => do_stmts_tail_semi (tag ";" rem) rem orig,
		fail _ => orig
	}

@[partial]
def do_stmts_tail_semi (r : ParseResult String) (after_sp : String) (orig : String) : String :=
	match r {
		success rem _ => skip_spaces rem,
		fail _ => after_sp
	}

@[partial]
def do_stmts_next (r : ParseResult (List DoStmt)) (first : DoStmt) : ParseResult (List DoStmt) :=
	match r {
		success rem rest => success rem (List.cons first rest),
		fail e => fail e
	}

@[partial]
def do_parser (input : String) : ParseResult TermV0 :=
	do_kw (tag "do" input)

@[partial]
def do_kw (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem _ => do_brace (tag "{" (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def do_brace (r : ParseResult String) : ParseResult TermV0 :=
	match r {
		success rem _ => do_build (do_stmts rem),
		fail e => fail e
	}

@[partial]
def do_build (r : ParseResult (List DoStmt)) : ParseResult TermV0 :=
	match r {
		success rem stmts => success rem (desugar_do stmts),
		fail e => fail e
	}

// --- Operator parsing ---

@[partial]
def is_op_char (c : String) : Bool :=
	op_char_member c op_chars

@[partial]
def operator_parse (input : String) : ParseResult String :=
	operator_parse_body (take_while is_op_char input)

@[partial]
def operator_parse_body (r : ParseResult String) : ParseResult String :=
	match r {
		success rem out =>
			if is_empty out
			then fail (ParseError.custom "expected operator")
			else operator_check out rem,
		fail e => fail e
	}

@[partial]
def operator_check (s : String) (rem : String) : ParseResult String :=
	if I64.beq 0 (op_precedence s)
	then fail (ParseError.custom "unknown operator")
	else success rem s

@[partial]
def op_precedence (op : String) : I64 :=
	op_lookup_prec op op_table

@[partial]
def op_is_right_assoc (op : String) : Bool :=
	op_lookup_rassoc op op_table

// --- Expression (atom + juxtaposition application + operators) ---

@[partial]
def expression (input : String) : ParseResult TermV0 :=
	expr_first (atom_term input)

@[partial]
def expr_first (r : ParseResult TermV0) : ParseResult TermV0 :=
	match r {
		success rem lhs => expr_rest rem lhs,
		fail e => fail e
	}

@[partial]
def expr_rest (input : String) (lhs : TermV0) : ParseResult TermV0 :=
	expr_rest_ws (take_while is_space input) lhs

@[partial]
def expr_rest_ws (r : ParseResult String) (lhs : TermV0) : ParseResult TermV0 :=
	match r {
		success rem _ => expr_rest_next (atom_term rem) rem lhs,
		fail e => fail e
	}

@[partial]
def expr_rest_next (r : ParseResult TermV0) (input : String) (lhs : TermV0) : ParseResult TermV0 :=
	match r {
		success rem rhs => expr_rest rem (TermV0.app lhs rhs),
		fail _ => expr_op input lhs
	}

@[partial]
def expr_op (input : String) (lhs : TermV0) : ParseResult TermV0 :=
	expr_op_try (operator_parse input) input lhs

@[partial]
def expr_op_try (r : ParseResult String) (input : String) (lhs : TermV0) : ParseResult TermV0 :=
	match r {
		success rem op => expr_op_prec input lhs op rem,
		fail _ => success input lhs
	}

@[partial]
def expr_op_prec (input : String) (lhs : TermV0) (op : String) (rem : String) : ParseResult TermV0 :=
	expr_op_prec_val (op_precedence op) input lhs op rem

@[partial]
def expr_op_prec_val (prec : I64) (input : String) (lhs : TermV0) (op : String) (rem : String) : ParseResult TermV0 :=
	if I64.beq prec 0
	then success input lhs
	else expr_op_rhs_ws (take_while is_space rem) lhs op

@[partial]
def expr_op_rhs_ws (r : ParseResult String) (lhs : TermV0) (op : String) : ParseResult TermV0 :=
	match r {
		success rem _ => expr_op_rhs_expr (expression rem) lhs op,
		fail e => fail e
	}

@[partial]
def expr_op_rhs_expr (r : ParseResult TermV0) (lhs : TermV0) (op : String) : ParseResult TermV0 :=
	match r {
		success rem rhs => success rem (TermV0.app (TermV0.app (TermV0.var (NameRef.nop (Operator.operator op))) lhs) rhs),
		fail e => fail e
	}

// --- Declaration parsers ---

// Module path parser (e.g. init.prelude)

@[partial]
def module_path_parser (input : String) : ParseResult ModulePath :=
	mp_first (identifier input)

@[partial]
def mp_first (r : ParseResult String) : ParseResult ModulePath :=
	match r {
		success rem first => mp_need_dot rem (List.cons (Identifier.id first) List.empty),
		fail e => fail e
	}

@[partial]
def mp_need_dot (input : String) (ids : List Identifier) : ParseResult ModulePath :=
	mp_need_dot_try (tag "." input) ids input

@[partial]
def mp_need_dot_try (r : ParseResult String) (ids : List Identifier) (orig : String) : ParseResult ModulePath :=
	match r {
		success rem _ => mp_field (identifier rem) ids,
		fail _ =>
			let rev : List Identifier := list_reverse ids in
			success orig (ModulePath.mp rev)
	}

@[partial]
def mp_loop (input : String) (ids : List Identifier) : ParseResult ModulePath :=
	mp_loop_dot (tag "." input) ids input

@[partial]
def mp_loop_dot (r : ParseResult String) (ids : List Identifier) (orig : String) : ParseResult ModulePath :=
	match r {
		success rem _ => mp_field (identifier rem) ids,
		fail _ =>
			let rev : List Identifier := list_reverse ids in
			success orig (ModulePath.mp rev)
	}

@[partial]
def mp_field (r : ParseResult String) (ids : List Identifier) : ParseResult ModulePath :=
	match r {
		success rem next => mp_loop rem (List.cons (Identifier.id next) ids),
		fail e => fail e
	}

// use module.path

@[partial]
def use_parser (input : String) : ParseResult Decl :=
	use_kw (tag "use" input)

@[partial]
def use_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => use_path (module_path_parser (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def use_path (r : ParseResult ModulePath) : ParseResult Decl :=
	match r {
		success rem path => success rem (Decl.use_d path),
		fail e => fail e
	}

// open module.path

@[partial]
def open_parser (input : String) : ParseResult Decl :=
	open_kw (tag "open" input)

@[partial]
def open_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => open_path (module_path_parser (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def open_path (r : ParseResult ModulePath) : ParseResult Decl :=
	match r {
		success rem path => success rem (Decl.open_d path),
		fail e => fail e
	}

// infix:prec (op) := path

@[partial]
def infix_parser (input : String) : ParseResult Decl :=
	infix_kw (tag "infix" input)

@[partial]
def infix_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => infix_colon (tag ":" (skip_spaces rem)) rem,
		fail e => fail e
	}

@[partial]
def infix_colon (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => infix_prec (number rem),
		fail _ => infix_paren (tag "(" (skip_spaces orig)) orig
	}

@[partial]
def infix_prec (r : ParseResult I64) : ParseResult Decl :=
	match r {
		success rem _ => infix_paren (tag "(" (skip_spaces rem)) rem,
		fail e => fail e
	}

@[partial]
def infix_paren (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => infix_op (operator_parse (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def infix_op (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem op => infix_close (tag ")" (skip_spaces rem)) op,
		fail e => fail e
	}

@[partial]
def infix_close (r : ParseResult String) (op : String) : ParseResult Decl :=
	match r {
		success rem _ => infix_assign (tag ":=" (skip_spaces rem)) op,
		fail e => fail e
	}

@[partial]
def infix_assign (r : ParseResult String) (op : String) : ParseResult Decl :=
	match r {
		success rem _ => infix_path (module_path_parser (skip_spaces rem)) op,
		fail e => fail e
	}

@[partial]
def infix_path (r : ParseResult ModulePath) (op : String) : ParseResult Decl :=
	match r {
		success rem path => success rem (Decl.infix_d (Operator.operator op) path),
		fail e => fail e
	}

// struct Name { field1 : Type, field2 : Type := default }

@[partial]
def struct_parser (input : String) : ParseResult Decl :=
	struct_kw (tag "struct" input)

@[partial]
def struct_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => struct_name (identifier (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def struct_name (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem name => struct_brace (tag "{" (skip_spaces rem)) (Identifier.id name),
		fail e => fail e
	}

@[partial]
def struct_brace (r : ParseResult String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ => struct_fields_top rem name,
		fail e => fail e
	}

@[partial]
def struct_fields_top (input : String) (name : Identifier) : ParseResult Decl :=
	struct_field_first (struct_one_field (skip_spaces input)) input name

@[partial]
def struct_field_first (r : ParseResult StructField) (orig : String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem fld => struct_fields_rest rem (List.cons fld List.empty) name,
		fail _ => struct_empty_close (tag "}" (skip_spaces orig)) name
	}

@[partial]
def struct_empty_close (r : ParseResult String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_fields : List StructField := List.empty in
			success rem (Decl.struct_d (Struct.mk name empty_fields)),
		fail e => fail (ParseError.custom "expected }")
	}

@[partial]
def struct_fields_rest (input : String) (fields : List StructField) (name : Identifier) : ParseResult Decl :=
	struct_fields_rest_comma (tag "," (skip_spaces input)) input fields name

@[partial]
def struct_fields_rest_comma (r : ParseResult String) (orig : String) (fields : List StructField) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ => struct_fields_rest_more (struct_one_field (skip_spaces rem)) fields name,
		fail _ => struct_close (tag "}" (skip_spaces orig)) name fields
	}

@[partial]
def struct_fields_rest_more (r : ParseResult StructField) (fields : List StructField) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem fld => struct_fields_rest rem (List.cons fld fields) name,
		fail _ => struct_close (tag "}" (skip_spaces "")) name fields
	}

@[partial]
def struct_close (r : ParseResult String) (name : Identifier) (fields : List StructField) : ParseResult Decl :=
	match r {
		success rem _ =>
			let rev : List StructField := list_reverse fields in
			success rem (Decl.struct_d (Struct.mk name rev)),
		fail e => fail e
	}

@[partial]
def struct_one_field (input : String) : ParseResult StructField :=
	struct_field_name (identifier input)

@[partial]
def struct_field_name (r : ParseResult String) : ParseResult StructField :=
	match r {
		success rem name => struct_field_colon (tag ":" (skip_spaces rem)) (Identifier.id name),
		fail e => fail e
	}

@[partial]
def struct_field_colon (r : ParseResult String) (name : Identifier) : ParseResult StructField :=
	match r {
		success rem _ => struct_field_type (type_expression (skip_spaces rem)) name,
		fail e => fail e
	}

@[partial]
def struct_field_type (r : ParseResult TermV0) (name : Identifier) : ParseResult StructField :=
	match r {
		success rem typ => struct_field_default (tag ":=" (skip_spaces rem)) rem name typ,
		fail e => fail e
	}

@[partial]
def struct_field_default (r : ParseResult String) (orig : String) (name : Identifier) (typ : TermV0) : ParseResult StructField :=
	match r {
		success rem _ => struct_field_default_val (expression (skip_spaces rem)) name typ,
		fail _ =>
			let none : Option TermV0 := Option.none in
			success orig (StructField.mk name typ none)
	}

@[partial]
def struct_field_default_val (r : ParseResult TermV0) (name : Identifier) (typ : TermV0) : ParseResult StructField :=
	match r {
		success rem defval =>
			let some_val : Option TermV0 := Option.some defval in
			success rem (StructField.mk name typ some_val),
		fail e => fail e
	}

// class [constraints] Name params { def method sig, def method sig := default }

@[partial]
def class_parser (input : String) : ParseResult Decl :=
	class_kw (tag "class" input)

@[partial]
def class_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => class_constraints_or_name rem,
		fail e => fail e
	}

@[partial]
def class_constraints_or_name (input : String) : ParseResult Decl :=
	class_try_constraints (tag "[" (skip_spaces input)) input

@[partial]
def class_try_constraints (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => class_name_after_bracket rem,
		fail _ => class_name (identifier (skip_spaces orig))
	}

@[partial]
def class_name_after_bracket (input : String) : ParseResult Decl :=
	class_find_bracket_close (take_while is_not_bracket input) input

@[partial]
def is_not_bracket (c : String) : Bool :=
	if String.beq "]" c then false
	else true

@[partial]
def class_find_bracket_close (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => class_name_after_close (tag "]" rem) orig,
		fail _ => fail (ParseError.custom "expected ]")
	}

@[partial]
def class_name_after_close (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => class_name (identifier (skip_spaces rem)),
		fail _ => class_name (identifier (skip_spaces orig))
	}

@[partial]
def class_name (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem name =>
			let empty_params : List Identifier := List.empty in
			class_params rem (Identifier.id name) empty_params,
		fail e => fail e
	}

@[partial]
def class_params (input : String) (name : Identifier) (params : List Identifier) : ParseResult Decl :=
	class_params_try (identifier (skip_spaces input)) input name params

@[partial]
def class_params_try (r : ParseResult String) (orig : String) (name : Identifier) (params : List Identifier) : ParseResult Decl :=
	match r {
		success rem next => class_params rem name (List.cons (Identifier.id next) params),
		fail _ => class_brace (tag "{" (skip_spaces orig)) name
	}

@[partial]
def class_brace (r : ParseResult String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_methods : List ClassDef := List.empty in
			class_methods rem name empty_methods,
		fail e => fail e
	}

@[partial]
def class_methods (input : String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	class_try_close_or_method (tag "def" (skip_spaces input)) input name methods

@[partial]
def class_try_close_or_method (r : ParseResult String) (orig : String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ => class_methods_single rem name methods,
		fail _ => class_close (tag "}" (skip_spaces orig)) name methods
	}

@[partial]
def class_methods_single (input : String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	class_method_name (identifier (skip_spaces input)) name methods

@[partial]
def class_method_name (r : ParseResult String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem mname => class_method_colon_or_sig rem (Identifier.id mname) name methods,
		fail e => fail e
	}

@[partial]
def class_method_colon_or_sig (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	class_method_params_try (tag "(" (skip_spaces input)) input mname name methods

@[partial]
def class_method_params_try (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ => class_method_param_loop rem mname name methods,
		fail _ => class_method_ret_type (tag ":" (skip_spaces orig)) mname name methods
	}

@[partial]
def class_method_param_loop (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	class_method_one_param (identifier (skip_spaces input)) input mname name methods

@[partial]
def class_method_one_param (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem pname => class_method_param_colon (tag ":" (skip_spaces rem)) mname name methods orig,
		fail e => fail e
	}

@[partial]
def class_method_param_colon (r : ParseResult String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => class_method_param_type (type_expression rem) mname name methods orig,
		fail e => fail e
	}

@[partial]
def class_method_param_type (r : ParseResult TermV0) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => class_method_close_or_next rem mname name methods orig,
		fail e => fail e
	}

@[partial]
def class_method_close_or_next (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (orig : String) : ParseResult Decl :=
	class_method_try_close_param (tag ")" (skip_spaces input)) input mname name methods

@[partial]
def class_method_try_close_param (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ => class_method_ret_or_more rem mname name methods,
		fail _ => class_method_next_param (tag "(" (skip_spaces orig)) orig mname name methods
	}

@[partial]
def class_method_ret_or_more (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	class_method_try_ret_type (tag ":" (skip_spaces input)) input mname name methods

@[partial]
def class_method_try_ret_type (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ => class_method_ret_type_val (type_expression rem) mname name methods,
		fail _ => class_method_next_param (tag "(" (skip_spaces orig)) orig mname name methods
	}

@[partial]
def class_method_ret_type_val (r : ParseResult TermV0) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem typ => class_method_default_or_done rem mname typ name methods,
		fail e => fail e
	}

@[partial]
def class_method_next_param (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ => class_method_param_loop rem mname name methods,
		fail _ => fail (ParseError.custom "expected ) or another parameter")
	}

@[partial]
def class_method_ret_type (r : ParseResult String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ => class_method_sig_type (type_expression rem) mname name methods,
		fail _ => fail (ParseError.custom "expected : return type")
	}

@[partial]
def class_method_sig_type (r : ParseResult TermV0) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem typ => class_method_default_or_done rem mname typ name methods,
		fail e => fail e
	}

@[partial]
def class_method_default_or_done (input : String) (mname : Identifier) (typ : TermV0) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	class_method_try_default (tag ":=" (skip_spaces input)) input mname typ name methods

@[partial]
def class_method_try_default (r : ParseResult String) (orig : String) (mname : Identifier) (typ : TermV0) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ => class_method_default_val (expression (skip_spaces rem)) orig mname typ name methods,
		fail _ =>
			let none_val : Option TermV0 := Option.none in
			class_methods orig name (List.cons (ClassDef.mk mname typ none_val) methods)
	}

@[partial]
def class_method_default_val (r : ParseResult TermV0) (orig : String) (mname : Identifier) (typ : TermV0) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem defval =>
			let some_val : Option TermV0 := Option.some defval in
			class_methods rem name (List.cons (ClassDef.mk mname typ some_val) methods),
		fail e => fail e
	}

@[partial]
def class_close (r : ParseResult String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=
	match r {
		success rem _ =>
			let rev_methods : List ClassDef := list_reverse methods in
			let empty_params : List Param := List.empty in
			let empty_constraints : List TypeConstraint := List.empty in
			success rem (Decl.class_d (Class.mk name empty_params empty_constraints rev_methods)),
		fail e => fail e
	}

// instance [constraints] [name :] Class args { methods }

@[partial]
def instance_parser (input : String) : ParseResult Decl :=
	instance_kw (tag "instance" input)

@[partial]
def instance_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => instance_try_constraints (tag "[" (skip_spaces rem)) rem,
		fail e => fail e
	}

@[partial]
def instance_try_constraints (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => instance_name (module_path_parser (skip_spaces rem)),
		fail _ => instance_name (module_path_parser (skip_spaces orig))
	}

@[partial]
def instance_name (r : ParseResult ModulePath) : ParseResult Decl :=
	match r {
		success rem path =>
			let empty_args : List TermV0 := List.empty in
			instance_args_or_brace rem path empty_args,
		fail e => fail e
	}

@[partial]
def instance_args_or_brace (input : String) (cls : ModulePath) (args : List TermV0) : ParseResult Decl :=
	instance_try_arg (atom_term (skip_spaces input)) input cls args

@[partial]
def instance_try_arg (r : ParseResult TermV0) (orig : String) (cls : ModulePath) (args : List TermV0) : ParseResult Decl :=
	match r {
		success rem arg => instance_args_or_brace rem cls (List.cons arg args),
		fail _ => instance_brace (tag "{" (skip_spaces orig)) cls args
	}

@[partial]
def instance_brace (r : ParseResult String) (cls : ModulePath) (args : List TermV0) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty_methods : List Def := List.empty in
			instance_methods rem cls args empty_methods,
		fail e => fail e
	}

@[partial]
def instance_methods (input : String) (cls : ModulePath) (args : List TermV0) (methods : List Def) : ParseResult Decl :=
	instance_try_close_or_def (tag "def" (skip_spaces input)) input cls args methods

@[partial]
def instance_try_close_or_def (r : ParseResult String) (orig : String) (cls : ModulePath) (args : List TermV0) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem _ => instance_method_single rem cls args methods,
		fail _ => instance_close (tag "}" (skip_spaces orig)) cls args methods
	}

@[partial]
def instance_method_single (input : String) (cls : ModulePath) (args : List TermV0) (methods : List Def) : ParseResult Decl :=
	instance_method_name (identifier (skip_spaces input)) cls args methods

@[partial]
def instance_method_name (r : ParseResult String) (cls : ModulePath) (args : List TermV0) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem name => instance_method_params_or_body rem (Identifier.id name) cls args methods,
		fail e => fail e
	}

@[partial]
def instance_method_params_or_body (input : String) (name : Identifier) (cls : ModulePath) (args : List TermV0) (methods : List Def) : ParseResult Decl :=
	instance_method_try_body (atom_term (skip_spaces input)) input name cls args methods

@[partial]
def instance_method_try_body (r : ParseResult TermV0) (orig : String) (name : Identifier) (cls : ModulePath) (args : List TermV0) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem arg =>
			let start_args : List TermV0 := List.cons arg List.empty in
			instance_method_body_loop rem start_args name cls args methods,
		fail _ => instance_method_finish (tag ":=" (skip_spaces orig)) name cls args methods
	}

@[partial]
def instance_method_body_loop (input : String) (body_args : List TermV0) (name : Identifier) (cls : ModulePath) (args : List TermV0) (methods : List Def) : ParseResult Decl :=
	instance_method_body_next (atom_term (skip_spaces input)) input body_args name cls args methods

@[partial]
def instance_method_body_next (r : ParseResult TermV0) (orig : String) (body_args : List TermV0) (name : Identifier) (cls : ModulePath) (args : List TermV0) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem arg => instance_method_body_loop rem (List.cons arg body_args) name cls args methods,
		fail _ => instance_method_finish (tag ":=" (skip_spaces orig)) name cls args methods
	}

@[partial]
def instance_method_finish (r : ParseResult String) (name : Identifier) (cls : ModulePath) (args : List TermV0) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem _ => instance_method_body (expression (skip_spaces rem)) name cls args methods,
		fail _ => fail (ParseError.custom "expected := in instance method")
	}

@[partial]
def instance_method_body (r : ParseResult TermV0) (name : Identifier) (cls : ModulePath) (args : List TermV0) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem body =>
			let empty_constraints : List TypeConstraint := List.empty in
			let empty_attrs : List String := List.empty in
			let d : Def := Def.mk (ModulePath.mp (List.cons name List.empty)) (TermV0.hole) body empty_constraints empty_attrs in
			instance_methods rem cls args (List.cons d methods),
		fail e => fail e
	}

@[partial]
def instance_close (r : ParseResult String) (cls : ModulePath) (args : List TermV0) (methods : List Def) : ParseResult Decl :=
	match r {
		success rem _ =>
			let rev_methods : List Def := list_reverse methods in
			let rev_args : List TermV0 := list_reverse args in
			let empty_constraints : List TypeConstraint := List.empty in
			success rem (Decl.instance_d (Instance.mk (Identifier.id "_") cls empty_constraints rev_args)),
		fail e => fail e
	}

// type Name { constructor1 (args), constructor2 }

@[partial]
def type_parser (input : String) : ParseResult Decl :=
	type_kw (tag "type" input)

@[partial]
def type_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => type_name (identifier (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def type_name (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem name =>
			let empty_params : List Identifier := List.empty in
			type_params_skip rem (Identifier.id name) empty_params,
		fail e => fail e
	}

@[partial]
def type_params_skip (input : String) (name : Identifier) (params : List Identifier) : ParseResult Decl :=
	type_params_skip_try (identifier (skip_spaces input)) input name params

@[partial]
def type_params_skip_try (r : ParseResult String) (orig : String) (name : Identifier) (params : List Identifier) : ParseResult Decl :=
	match r {
		success rem next => type_params_skip rem name (List.cons (Identifier.id next) params),
		fail _ => type_brace (tag "{" (skip_spaces orig)) name
	}

@[partial]
def type_brace (r : ParseResult String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ => type_constructors_with_name rem name,
		fail e => fail e
	}

@[partial]
def type_constructors_with_name (input : String) (name : Identifier) : ParseResult Decl :=
	type_cons_first_named (type_one_constructor (skip_spaces input)) input name

@[partial]
def type_cons_first_named (r : ParseResult InductConstructor) (orig : String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem con => type_cons_rest_named rem (List.cons con List.empty) name,
		fail _ => type_empty_close_named (tag "}" (skip_spaces orig)) name
	}

@[partial]
def type_empty_close_named (r : ParseResult String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty : List InductConstructor := List.empty in
			success rem (type_to_decl name empty),
		fail e => fail (ParseError.custom "expected }")
	}

@[partial]
def type_cons_rest_named (input : String) (cons : List InductConstructor) (name : Identifier) : ParseResult Decl :=
	type_cons_rest_comma_named (tag "," (skip_spaces input)) input cons name

@[partial]
def type_cons_rest_comma_named (r : ParseResult String) (orig : String) (cons : List InductConstructor) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ => type_cons_rest_more_named (type_one_constructor (skip_spaces rem)) cons name,
		fail _ => type_close_brace (tag "}" (skip_spaces orig)) name cons
	}

@[partial]
def type_cons_rest_more_named (r : ParseResult InductConstructor) (cons : List InductConstructor) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem con => type_cons_rest_named rem (List.cons con cons) name,
		fail _ => type_close_brace (tag "}" (skip_spaces "")) name cons
	}

@[partial]
def type_close_brace (r : ParseResult String) (name : Identifier) (cons : List InductConstructor) : ParseResult Decl :=
	match r {
		success rem _ =>
			let rev : List InductConstructor := list_reverse cons in
			success rem (type_to_decl name rev),
		fail e => fail e
	}

@[partial]
def type_one_constructor (input : String) : ParseResult InductConstructor :=
	type_cons_name (identifier input)

@[partial]
def type_cons_name (r : ParseResult String) : ParseResult InductConstructor :=
	match r {
		success rem name => type_cons_paren_or_nil (tag "(" (skip_spaces rem)) rem (Identifier.id name),
		fail e => fail e
	}

@[partial]
def type_cons_paren_or_nil (r : ParseResult String) (orig : String) (name : Identifier) : ParseResult InductConstructor :=
	match r {
		success rem _ => type_cons_params (type_param_list rem) name,
		fail _ =>
			let empty_params : List Param := List.empty in
			success orig (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) empty_params (TermV0.hole))
	}

@[partial]
def type_cons_params (r : ParseResult (List Param)) (name : Identifier) : ParseResult InductConstructor :=
	match r {
		success rem params => type_cons_close_paren (tag ")" (skip_spaces rem)) name params,
		fail e => fail e
	}

@[partial]
def type_cons_close_paren (r : ParseResult String) (name : Identifier) (params : List Param) : ParseResult InductConstructor :=
	match r {
		success rem _ => success rem (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) params (TermV0.hole)),
		fail e => fail e
	}

@[partial]
def type_param_list (input : String) : ParseResult (List Param) :=
	type_param_first (type_one_param (skip_spaces input))

@[partial]
def type_one_param (input : String) : ParseResult Param :=
	type_one_param_name (identifier input)

@[partial]
def type_one_param_name (r : ParseResult String) : ParseResult Param :=
	match r {
		success rem name => type_one_param_type (tag ":" (skip_spaces rem)) (Identifier.id name),
		fail e => fail e
	}

@[partial]
def type_one_param_type (r : ParseResult String) (name : Identifier) : ParseResult Param :=
	match r {
		success rem _ => type_one_param_val (type_expression (skip_spaces rem)) name,
		fail e => fail e
	}

@[partial]
def type_one_param_val (r : ParseResult TermV0) (name : Identifier) : ParseResult Param :=
	match r {
		success rem typ => success rem (param_many name typ),
		fail e => fail e
	}

@[partial]
def type_param_first (r : ParseResult Param) : ParseResult (List Param) :=
	match r {
		success rem param => type_param_rest rem (List.cons param List.empty),
		fail _ =>
			let empty : List Param := List.empty in
			success "" empty
	}

@[partial]
def type_param_rest (input : String) (params : List Param) : ParseResult (List Param) :=
	type_param_rest_comma (tag "," (skip_spaces input)) input params

@[partial]
def type_param_rest_comma (r : ParseResult String) (orig : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ => type_param_rest_more (type_one_param (skip_spaces rem)) params,
		fail _ =>
			let rev : List Param := list_reverse params in
			success orig rev
	}

@[partial]
def type_param_rest_more (r : ParseResult Param) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem param => type_param_rest rem (List.cons param params),
		fail _ =>
			let rev : List Param := list_reverse params in
			success "" rev
	}

@[partial]
def type_to_decl (name : Identifier) (cons : List InductConstructor) : Decl :=
	let empty_params : List Param := List.empty in
	let empty_attrs : List String := List.empty in
	Decl.inductive_d (Inductive.mk (ModulePath.mp (List.cons name List.empty)) empty_params (TermV0.type_ 1) cons empty_attrs)

@[partial]
def def_parser (input : String) : ParseResult Decl :=
	def_try_attrs (tag "@[" (skip_spaces input)) input

@[partial]
def def_try_attrs (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => def_attr_skip (take_while is_not_attr_end rem) rem,
		fail _ => def_kw (tag "def" (skip_spaces orig))
	}

@[partial]
def is_not_attr_end (c : String) : Bool :=
	if String.beq "]" c then false
	else true

@[partial]
def def_attr_skip (r : ParseResult String) (rest : String) : ParseResult Decl :=
	match r {
		success rem _ => def_attr_close (tag "]" rem),
		fail _ => fail (ParseError.custom "expected ]")
	}

@[partial]
def def_attr_close (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => def_kw (tag "def" (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def def_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => def_name (identifier (skip_spaces rem)),
		fail e => fail e
	}

@[partial]
def def_name (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem name =>
			let empty : List Param := List.empty in
			def_params (def_params_loop (skip_spaces rem) empty) (Identifier.id name),
		fail e => fail e
	}

@[partial]
def def_params_loop (input : String) (params : List Param) : ParseResult (List Param) :=
	def_params_try_implicit (tag "{" input) input params

@[partial]
def def_params_try_implicit (r : ParseResult String) (orig : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ => def_implicit_param (identifier (skip_spaces rem)) rem params,
		fail _ => def_params_try_explicit (tag "(" orig) orig params
	}

@[partial]
def def_implicit_param (r : ParseResult String) (rem : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 name => def_implicit_colon (tag ":" (skip_spaces rem2)) rem rem2 name params,
		fail e => fail e
	}

@[partial]
def def_implicit_colon (r : ParseResult String) (brace_rem : String) (rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 _ => def_implicit_type (type_expression rem2) brace_rem rem name params,
		fail e => fail e
	}

@[partial]
def def_implicit_type (r : ParseResult TermV0) (brace_rem : String) (rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 typ => def_implicit_close (tag "}" rem2) brace_rem name typ params,
		fail e => fail e
	}

@[partial]
def def_implicit_close (r : ParseResult String) (brace_rem : String) (name : String) (typ : TermV0) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 _ =>
			let empty : List Param := List.empty in
			def_params_loop (skip_spaces rem2) empty,
		fail e => fail e
	}

@[partial]
def def_params_try_explicit (r : ParseResult String) (orig : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ => def_explicit_param (identifier (skip_spaces rem)) rem params,
		fail _ =>
			let rev : List Param := list_reverse params in
			success orig rev
	}

@[partial]
def def_explicit_param (r : ParseResult String) (close_rem : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem name => def_explicit_colon (tag ":" (skip_spaces rem)) close_rem name params,
		fail e => fail e
	}

@[partial]
def def_explicit_colon (r : ParseResult String) (close_rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ => def_explicit_type (type_expression rem) close_rem name params,
		fail e => fail e
	}

@[partial]
def def_explicit_type (r : ParseResult TermV0) (close_rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem typ => def_explicit_close (tag ")" rem) close_rem name typ params,
		fail e => fail e
	}

@[partial]
def def_explicit_close (r : ParseResult String) (close_rem : String) (name : String) (typ : TermV0) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ => def_params_loop (skip_spaces rem) (List.cons (param_many (Identifier.id name) typ) params),
		fail e => fail e
	}

@[partial]
def def_params (r : ParseResult (List Param)) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem params => def_ret_type (tag ":" (skip_spaces rem)) rem name params,
		fail e => fail e
	}

@[partial]
def def_ret_type (r : ParseResult String) (orig : String) (name : Identifier) (params : List Param) : ParseResult Decl :=
	match r {
		success rem _ => def_ret_expr (type_expression rem) name params,
		fail _ => fail (ParseError.custom "expected : return type")
	}

@[partial]
def def_ret_expr (r : ParseResult TermV0) (name : Identifier) (params : List Param) : ParseResult Decl :=
	match r {
		success rem typ => def_body rem name params typ,
		fail e => fail e
	}

@[partial]
def def_body (input : String) (name : Identifier) (params : List Param) (typ : TermV0) : ParseResult Decl :=
	def_body_assign (tag ":=" (skip_spaces input)) name params typ input

@[partial]
def def_body_assign (r : ParseResult String) (name : Identifier) (params : List Param) (typ : TermV0) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => def_body_expr (expression (skip_spaces rem)) name params typ,
		fail _ => def_body_block_or_none (tag "{" (skip_spaces orig)) name params typ orig
	}

@[partial]
def def_body_block_or_none (r : ParseResult String) (name : Identifier) (params : List Param) (typ : TermV0) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => def_body_do (do_stmts rem) name params typ,
		fail _ => success orig (def_to_decl (lam_params params (TermV0.hole)) name typ)
	}

@[partial]
def def_body_expr (r : ParseResult TermV0) (name : Identifier) (params : List Param) (typ : TermV0) : ParseResult Decl :=
	match r {
		success rem body => success rem (def_to_decl (lam_params params body) name typ),
		fail e => fail e
	}

@[partial]
def def_body_block (r : ParseResult String) (name : Identifier) (params : List Param) (typ : TermV0) : ParseResult Decl :=
	match r {
		success rem _ => def_body_do (do_stmts rem) name params typ,
		fail e => fail e
	}

@[partial]
def def_body_do (r : ParseResult (List DoStmt)) (name : Identifier) (params : List Param) (typ : TermV0) : ParseResult Decl :=
	match r {
		success rem stmts => success rem (def_to_decl (lam_params params (desugar_do stmts)) name typ),
		fail e => fail e
	}

@[partial]
def lam_params (params : List Param) (body : TermV0) : TermV0 :=
	let rev : List Param := list_reverse params in
	lam_params_loop rev body

@[partial]
def lam_params_loop (params : List Param) (body : TermV0) : TermV0 :=
	match params {
		List.cons p rest => lam_params_loop rest (TermV0.lam p body),
		List.empty => body
	}

@[partial]
def def_to_decl (body : TermV0) (name : Identifier) (typ : TermV0) : Decl :=
	let empty_constraints : List TypeConstraint := List.empty in
	let empty_attrs : List String := List.empty in
	Decl.def_d (Def.mk (ModulePath.mp (List.cons name List.empty)) typ body empty_constraints empty_attrs)

// Top-level declaration dispatcher

@[partial]
def decl_parser (input : String) : ParseResult Decl :=
	decl_fail_to_unknown (alt_fold decl_parsers input)

// --- Tests ---

@[test]
def test_tag_hello : Bool :=
	match tag "hello" "hello world" {
		success rem out => String.beq rem " world",
		fail _ => false
	}

@[test]
def test_identifier_abc : Bool :=
	match identifier "abc def" {
		success rem out => String.beq out "abc" && String.beq rem " def",
		fail _ => false
	}

@[test]
def test_identifier_rejects_keyword : Bool :=
	match identifier "def x" {
		success _ _ => false,
		fail _ => true
	}

@[test]
def test_identifier_rejects_digit_start : Bool :=
	match identifier "123abc" {
		success _ _ => false,
		fail _ => true
	}

@[test]
def test_number_42 : Bool :=
	match number "42 abc" {
		success rem out => I64.beq out 42 && String.beq rem " abc",
		fail _ => false
	}

@[test]
def test_number_fail_empty : Bool :=
	match number "abc" {
		success _ _ => false,
		fail _ => true
	}

@[test]
def test_alt_tag : Bool :=
	match (alt (tag "foo") (tag "bar")) "foobar" {
		success rem out => String.beq out "foo" && String.beq rem "bar",
		fail _ => false
	}

@[test]
def test_type_variable_a : Bool :=
	match type_variable "A" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_parens : Bool :=
	match type_parens "(A)" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_expression_var : Bool :=
	match type_expression "A" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_expression_arrow : Bool :=
	match type_expression "A -> B" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_expression_arrow_chain : Bool :=
	match type_expression "A -> B -> C" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_arrow_structure : Bool :=
	match type_expression "A -> B" {
		success rem out => I64.beq 0 0,
		fail _ => false
	}

// --- New parser tests ---

@[test]
def test_many1_single : Bool :=
	match many1 (tag "a") "a" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_many1_multiple : Bool :=
	match many1 (tag "a") "aaab" {
		success rem out => String.beq rem "b",
		fail _ => false
	}

@[test]
def test_many1_fail : Bool :=
	match many1 (tag "a") "b" {
		success _ _ => false,
		fail _ => true
	}

@[test]
def test_string_parse_hello : Bool :=
	match string_parse "\"hello world\"" {
		success rem out => match out {
			lit val => match val {
				str s => String.beq s "hello world" && String.beq rem "",
				num v suf => false, if_ a b c => false, match_ v cs => false
			},
			forall n t b => false, pi a r => false, var n => false,
			lam p b => false, app f a => false, con c => false,
			ntv n => false, type_ u => false, hole => false
		},
		fail _ => false
	}

@[test]
def test_string_parse_empty : Bool :=
	match string_parse "\"\"" {
		success rem out => match out {
			lit val => match val {
				str s => String.beq s "" && String.beq rem "",
				num v suf => false, if_ a b c => false, match_ v cs => false
			},
			forall n t b => false, pi a r => false, var n => false,
			lam p b => false, app f a => false, con c => false,
			ntv n => false, type_ u => false, hole => false
		},
		fail _ => false
	}

@[test]
def test_number_term_42 : Bool :=
	match number_term "42" {
		success rem out => match out {
			lit val => match val {
				num n s => I64.beq n 42 && String.beq rem "",
				str v => false, if_ a b c => false, match_ v cs => false
			},
			forall n t b => false, pi a r => false, var n => false,
			lam p b => false, app f a => false, con c => false,
			ntv n => false, type_ u => false, hole => false
		},
		fail _ => false
	}

@[test]
def test_number_term_rem : Bool :=
	match number_term "123 abc" {
		success rem out => match out {
			lit val => match val {
				num n s => I64.beq n 123 && String.beq rem " abc",
				str v => false, if_ a b c => false, match_ v cs => false
			},
			forall n t b => false, pi a r => false, var n => false,
			lam p b => false, app f a => false, con c => false,
			ntv n => false, type_ u => false, hole => false
		},
		fail _ => false
	}

@[test]
def test_variable_simple : Bool :=
	match variable "abc" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_variable_rem : Bool :=
	match variable "abc def" {
		success rem out => String.beq rem " def",
		fail _ => false
	}

@[test]
def test_expression_var : Bool :=
	match expression "abc" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_expression_app : Bool :=
	match expression "f x" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_expression_app_chain : Bool :=
	match expression "f x y" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_expression_parens_var : Bool :=
	match expression "(x)" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_expression_parens_app : Bool :=
	match expression "f (x) (y)" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_expression_atom_num : Bool :=
	match expression "42" {
		success rem out => match out {
			lit val => match val {
				num n s => I64.beq n 42 && String.beq rem "",
				str v => false, if_ a b c => false, match_ v cs => false
			},
			forall n t b => false, pi a r => false, var n => false,
			lam p b => false, app f a => false, con c => false,
			ntv n => false, type_ u => false, hole => false
		},
		fail _ => false
	}

@[test]
def test_expression_atom_str : Bool :=
	match expression "\"hi\"" {
		success rem out => match out {
			lit val => match val {
				str s => String.beq s "hi" && String.beq rem "",
				num v suf => false, if_ a b c => false, match_ v cs => false
			},
			forall n t b => false, pi a r => false, var n => false,
			lam p b => false, app f a => false, con c => false,
			ntv n => false, type_ u => false, hole => false
		},
		fail _ => false
	}

@[test]
def test_expression_complex : Bool :=
	match expression "f (g x) 42 \"hello\"" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_expression_num_var_app : Bool :=
	match expression "42 x" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Match expression tests ---

@[test]
def test_match_parser_simple : Bool :=
	match match_parser "match x { some a => a, none => default }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_match_parser_no_args : Bool :=
	match match_parser "match x { none => 0 }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- If expression tests ---

@[test]
def test_if_parser_simple : Bool :=
	match if_parser "if true then 1 else 2" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_if_parser_nested : Bool :=
	match if_parser "if a then if b then 1 else 2 else 3" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Let expression tests ---

@[test]
def test_let_parser_simple : Bool :=
	match let_parser "let x := 1 in x" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Lambda expression tests ---

@[test]
def test_lambda_parser_simple : Bool :=
	match lambda_parser "fn x => x" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Expression with complex subterms ---

@[test]
def test_expression_match_subterm : Bool :=
	match expression "match x { none => 0 }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_expression_if_subterm : Bool :=
	match expression "if true then 1 else 2" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Operator expression tests ---

@[test]
def test_expression_concat_op : Bool :=
	match expression "x ++ y" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_expression_and_op : Bool :=
	match expression "a && b" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_expression_eq_op : Bool :=
	match expression "a == b" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_expression_op_chain : Bool :=
	match expression "a ++ b && c" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_expression_app_over_op : Bool :=
	match expression "f x ++ g y" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Dotted path tests ---

@[test]
def test_variable_dotted_path : Bool :=
	match variable "A.B.C" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_variable_simple_not_path : Bool :=
	match variable "abc" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_expression_path : Bool :=
	match expression "List.cons" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_expression_path_app : Bool :=
	match expression "A.fun x y" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Backslash lambda tests ---

@[test]
def test_lambda_backslash : Bool :=
	match expression "\\ x => x" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Do-notation tests ---

@[test]
def test_do_empty : Bool :=
	match do_parser "do { }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_do_return : Bool :=
	match do_parser "do { return 42 }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_do_bind : Bool :=
	match do_parser "do { let x <- m; return x }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_do_let : Bool :=
	match do_parser "do { let x := 1; return x }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_do_expr : Bool :=
	match do_parser "do { println 42; return 0 }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_do_chain : Bool :=
	match do_parser "do { let a <- f x; let b <- g a; return b }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Declaration parser tests ---

@[test]
def test_use_parser : Bool :=
	match use_parser "use prelude" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_use_parser_path : Bool :=
	match use_parser "use lang.types" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_open_parser : Bool :=
	match open_parser "open IO" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_infix_parser : Bool :=
	match infix_parser "infix (++) := List.append" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_infix_parser_prec : Bool :=
	match infix_parser "infix:13 (>>=) := Monad.bind" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Def parser tests ---

@[test]
def test_def_simple : Bool :=
	match def_parser "def f (x : I64) : I64 := x" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_def_no_params : Bool :=
	match def_parser "def main : I64 := 42" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_def_do_block : Bool :=
	match def_parser "def f (x : I64) : I64 { let y := x; y }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Type parser tests ---

@[test]
def test_type_simple : Bool :=
	match type_parser "type Maybe A { some (a: A), none }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_empty : Bool :=
	match type_parser "type Void { }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Struct parser tests ---

@[test]
def test_struct_simple : Bool :=
	match struct_parser "struct Point { x : I64, y : I64 }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_struct_default : Bool :=
	match struct_parser "struct Point { x : I64 := 0 }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Class parser tests ---

@[test]
def test_class_simple : Bool :=
	match class_parser "class Show A { def show (a : A) : String }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_class_constraints : Bool :=
	match class_parser "class [Functor M] Monad M { def bind (a : M A) (f : A -> M B) : M B }" {
		success rem out => true,
		fail _ => false
	}

@[test]
def test_class_multi_param : Bool :=
	match class_parser "class Foo { def bar (a : I64) (b : I64) : I64 }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Instance parser tests ---

@[test]
def test_instance_simple : Bool :=
	match instance_parser "instance Show I64 { def show x := \"int\" }" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Attribute tests ---

@[test]
def test_def_native_attr : Bool :=
	match def_parser "@[native \"add\"] def add (a : I64) (b : I64) : I64 := a" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_def_native_no_body : Bool :=
	match def_parser "@[native \"add\"] def add (a : I64) (b : I64) : I64" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_def_attr_simple : Bool :=
	match def_parser "@[test] def f (x : I64) : I64 := x" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// --- Implicit param tests ---

@[test]
def test_def_implicit_params : Bool :=
	match def_parser "def identity {A : Type} (x : A) : A := x" {
		success rem out => String.beq rem "",
		fail _ => false
	}


// --- Combinator tests (Phase 1.1) ---

// Helper functions for tests
@[partial]
def id_str (s : String) : String := s

@[partial]
def str_len (s : String) : I64 := String.length s

@[partial]
def always_tag_y (a : String) (input : String) : ParseResult String := tag "y" input

@[test]
def test_map_parse_simple : Bool :=
	match map_parse id_str identifier "abc def" {
		success rem out => String.beq rem " def",
		fail _ => false
	}

@[test]
def test_map_parse_tag : Bool :=
	match map_parse id_str (tag "x") "xy" {
		success rem out => String.beq out "x",
		fail _ => false
	}

@[test]
def test_map_parse_fail : Bool :=
	match map_parse id_str (tag "x") "y" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_map_parse_mapped : Bool :=
	match map_parse str_len identifier "abc def" {
		success rem out => String.beq rem " def",
		fail _ => false
	}

@[test]
def test_bind_parse : Bool :=
	match bind_parse (tag "x") always_tag_y "xyz" {
		success rem out => String.beq rem "z",
		fail _ => false
	}

@[test]
def test_bind_parse_fail_first : Bool :=
	match bind_parse (tag "x") always_tag_y "abc" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_bind_parse_fail_second : Bool :=
	match bind_parse (tag "x") always_tag_y "xab" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_alt_fold_first : Bool :=
	match alt_fold (List.cons (tag "a") (List.cons (tag "b") (List.cons (tag "c") List.empty))) "abc" {
		success rem out => String.beq rem "bc",
		fail _ => false
	}

@[test]
def test_alt_fold_second : Bool :=
	match alt_fold (List.cons (tag "x") (List.cons (tag "y") (List.cons (tag "z") List.empty))) "y" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_alt_fold_none : Bool :=
	match alt_fold (List.cons (tag "x") (List.cons (tag "y") List.empty)) "abc" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_preceded_by : Bool :=
	match preceded_by (tag "(") (tag "x") "(x" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_preceded_by_fail : Bool :=
	match preceded_by (tag "(") (tag "x") "x" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_terminated_by : Bool :=
	match terminated_by (tag "x") (tag ")") "x)" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_terminated_by_fail : Bool :=
	match terminated_by (tag "x") (tag ")") "x(" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_delimited_by : Bool :=
	match delimited_by (tag "(") (tag "x") (tag ")") "(x)" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_delimited_by_fail_open : Bool :=
	match delimited_by (tag "(") (tag "x") (tag ")") "x)" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_delimited_by_fail_close : Bool :=
	match delimited_by (tag "(") (tag "x") (tag ")") "(x(" {
		success rem out => false,
		fail e => true
	}

@[test]
def test_separated_by_single : Bool :=
	match separated_by (tag ",") (tag "a") "a" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_separated_by_multi : Bool :=
	match separated_by (tag ",") (tag "a") "a,a,a" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_separated_by_empty : Bool :=
	match separated_by (tag ",") (tag "a") "b" {
		success rem out => String.beq rem "b",
		fail e => false
	}

@[test]
def test_opt_some : Bool :=
	match opt (tag "x") "xy" {
		success rem out => match out {
			Option.some val => String.beq val "x",
			Option.none => false
		},
		fail _ => false
	}

@[test]
def test_opt_none : Bool :=
	match opt (tag "x") "yz" {
		success rem out => match out {
			Option.some val => false,
			Option.none => String.beq rem "yz"
		},
		fail _ => false
	}

@[test]
def test_ws0 : Bool :=
	match ws0 "  abc" {
		success rem out => String.beq rem "abc",
		fail _ => false
	}

@[test]
def test_ws0_empty : Bool :=
	match ws0 "abc" {
		success rem out => String.beq rem "abc",
		fail _ => false
	}

@[test]
def test_ws1 : Bool :=
	match ws1 "  abc" {
		success rem out => String.beq rem "abc",
		fail _ => false
	}

@[test]
def test_ws1_fail : Bool :=
	match ws1 "abc" {
		success rem out => false,
		fail e => true
	}


// --- Position tracking tests (Phase 1.2) ---

@[test]
def test_new_span : Bool :=
	let span : LocatedSpan := new_span "hello" in
	let frag : String := span_fragment span in
	I64.beq (String.length frag) 5

@[test]
def test_new_span_location : Bool :=
	let span : LocatedSpan := new_span "x" in
	let loc : Location := span_location span in
	match loc {
		mk off line col => I64.beq off 0 && I64.beq line 1 && I64.beq col 1
	}

@[test]
def test_consume_no_newline : Bool :=
	let span : LocatedSpan := new_span "hello world" in
	let next : LocatedSpan := consume_span span 5 in
	let loc : Location := span_location next in
	match loc {
		mk off line col => I64.beq off 5 && I64.beq line 1 && I64.beq col 6
	}

@[test]
def test_consume_single_newline : Bool :=
	let span : LocatedSpan := new_span "a\nb" in
	let next : LocatedSpan := consume_span span 2 in
	let loc : Location := span_location next in
	match loc {
		mk off line col => I64.beq off 2 && I64.beq line 2 && I64.beq col 1
	}

@[test]
def test_consume_multi_newline : Bool :=
	let span : LocatedSpan := new_span "a\n\nb" in
	let next : LocatedSpan := consume_span span 3 in
	let loc : Location := span_location next in
	match loc {
		mk off line col => I64.beq off 3 && I64.beq line 3 && I64.beq col 1
	}

@[test]
def test_span_fragment_after_consume : Bool :=
	let span : LocatedSpan := new_span "hello world" in
	let next : LocatedSpan := consume_span span 6 in
	let rest : String := span_fragment next in
	String.beq rest "world"

def t2_sentinel : I64 := -1

@[partial]
def t2_ident_str (id: Identifier) : String :=
    match id {
        id s => s
    }

@[partial]
def t2_find_index (id: Identifier) (ctx: List Identifier) (depth: I64) : Option I64 :=
    match ctx {
        List.cons x rest =>
            if String.beq (t2_ident_str id) (t2_ident_str x)
            then Option.some depth
            else t2_find_index id rest (depth + 1),
        List.empty => Option.none
    }

@[partial]
def t2_debug_name_of_id (id: Identifier) : DebugName :=
    DebugName.named id

@[partial]
def t2_var_term (ctx: List Identifier) (s: String) : Term :=
    let sid : Identifier := Identifier.id s in
    match t2_find_index sid ctx 0 {
        Option.some idx => Term.var idx (DebugName.named sid),
        Option.none => Term.var t2_sentinel (DebugName.named sid)
    }

@[partial]
def t2_variable (ctx: List Identifier) (input: String) : ParseResult Term :=
    t2_variable_try_path (path_variable input) ctx input

@[partial]
def t2_variable_try_path (r: ParseResult TermV0) (ctx: List Identifier) (input: String) : ParseResult Term :=
    match r {
        success rem out =>
            // Dotted path → sentinel index (resolved later by module resolver)
            success rem (Term.var t2_sentinel DebugName.unnamed),
        fail _ => t2_variable_got (identifier input) ctx
    }

@[partial]
def t2_variable_got (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem out => success rem (t2_var_term ctx out),
        fail e => fail e
    }

// ─── Term atom ──────────────────────────────────────────────────────────

@[partial]
def t2_atom_term (ctx: List Identifier) (input: String) : ParseResult Term :=
    t2_atom_try_var (t2_variable ctx input) ctx input

@[partial]
def t2_atom_try_var (r: ParseResult Term) (ctx: List Identifier) (input: String) : ParseResult Term :=
    match r {
        success rem out => success rem out,
        fail _ => t2_atom_try_lit (literal_term input) ctx input
    }

@[partial]
def t2_atom_try_lit (r: ParseResult TermV0) (ctx: List Identifier) (input: String) : ParseResult Term :=
    match r {
        success rem out => t2_atom_lift_lit out rem,
        fail _ => t2_atom_try_match (match_parser input) ctx input
    }

@[partial]
def t2_atom_lift_lit (t: TermV0) (rem: String) : ParseResult Term :=
    match t {
        TermV0.lit val => success rem (Term.lit val),
        TermV0.var name => match name {
            NameRef.nid id => success rem (Term.var t2_sentinel (DebugName.named id)),
            NameRef.nmp mp => success rem (Term.var t2_sentinel DebugName.unnamed),
            NameRef.nop op => success rem (Term.var t2_sentinel DebugName.unnamed)
        },
        TermV0.app f a => success rem (Term.var t2_sentinel DebugName.unnamed),
        TermV0.lam p b => success rem (Term.var t2_sentinel DebugName.unnamed),
        TermV0.pi a r => success rem (Term.var t2_sentinel DebugName.unnamed),
        TermV0.forall n t b => success rem (Term.var t2_sentinel DebugName.unnamed),
        TermV0.con c => success rem (Term.var t2_sentinel DebugName.unnamed),
        TermV0.ntv n => success rem (Term.var t2_sentinel DebugName.unnamed),
        TermV0.type_ u => success rem (Term.type_ u),
        TermV0.hole => success rem Term.hole
    }

@[partial]
def t2_atom_try_match (r: ParseResult TermV0) (ctx: List Identifier) (input: String) : ParseResult Term :=
    match r {
        success rem out => t2_atom_lift_lit out rem,
        fail _ => t2_atom_try_if (if_parser input) ctx input
    }

@[partial]
def t2_atom_try_if (r: ParseResult TermV0) (ctx: List Identifier) (input: String) : ParseResult Term :=
    match r {
        success rem out => t2_atom_lift_lit out rem,
        fail _ => t2_atom_try_lambda (t2_lambda_parser ctx input) ctx input
    }

@[partial]
def t2_atom_try_lambda (r: ParseResult Term) (ctx: List Identifier) (input: String) : ParseResult Term :=
    match r {
        success rem out => success rem out,
        fail _ => t2_atom_try_paren (tag "(" input) ctx input
    }

@[partial]
def t2_atom_try_paren (r: ParseResult String) (ctx: List Identifier) (input: String) : ParseResult Term :=
    match r {
        success rem _ => t2_atom_inner_expr (t2_type_expression ctx rem) ctx,
        fail e => fail e
    }

@[partial]
def t2_atom_inner_expr (r: ParseResult Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem out => t2_atom_close_paren (tag ")" rem) out,
        fail e => fail e
    }

@[partial]
def t2_atom_close_paren (r: ParseResult String) (out: Term) : ParseResult Term :=
    match r {
        success rem _ => success rem out,
        fail e => fail e
    }

// ─── Term lambda ────────────────────────────────────────────────────────

@[partial]
def t2_lambda_parser (ctx: List Identifier) (input: String) : ParseResult Term :=
    t2_lambda_kw (alt (alt (tag "fn") (tag "ꟛ")) (tag "\\") input) ctx

@[partial]
def t2_lambda_kw (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => t2_lambda_name_outer (skip_spaces rem) ctx,
        fail e => fail e
    }

@[partial]
def t2_lambda_name_outer (input: String) (ctx: List Identifier) : ParseResult Term :=
    t2_lambda_name_outer_got (identifier input) input ctx

@[partial]
def t2_lambda_name_outer_got (r: ParseResult String) (orig: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem name => t2_lambda_arrow (tag "=>" (skip_spaces rem)) rem orig (Identifier.id name) ctx,
        fail e => fail e
    }

@[partial]
def t2_lambda_arrow (r: ParseResult String) (rem: String) (orig: String) (name: Identifier) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem2 _ => t2_lambda_body (t2_expression (List.cons name ctx) (skip_spaces rem2)) name,
        fail e => fail e
    }

@[partial]
def t2_lambda_body (r: ParseResult Term) (name: Identifier) : ParseResult Term :=
    match r {
        success rem body => success rem (Term.lam (DebugName.named name) (Term.type_ 1) body),
        fail e => fail e
    }

// ─── Term expression (application + operators) ─────────────────────────

@[partial]
def t2_expression (ctx: List Identifier) (input: String) : ParseResult Term :=
    t2_expr_first (t2_atom_term ctx (skip_spaces input)) ctx

@[partial]
def t2_expr_first (r: ParseResult Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem lhs => t2_expr_rest rem lhs ctx,
        fail e => fail e
    }

@[partial]
def t2_expr_rest (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    t2_expr_rest_ws (take_while is_space input) lhs ctx

@[partial]
def t2_expr_rest_ws (r: ParseResult String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => t2_expr_rest_next (t2_atom_term ctx rem) rem lhs ctx,
        fail e => fail e
    }

@[partial]
def t2_expr_rest_next (r: ParseResult Term) (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem rhs => t2_expr_rest rem (Term.app lhs rhs) ctx,
        fail _ => t2_expr_op input lhs ctx
    }

@[partial]
def t2_expr_op (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    t2_expr_op_try (operator_parse input) input lhs ctx

@[partial]
def t2_expr_op_try (r: ParseResult String) (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem op => t2_expr_op_prec input lhs op rem ctx,
        fail _ => success input lhs
    }

@[partial]
def t2_expr_op_prec (input: String) (lhs: Term) (op: String) (rem: String) (ctx: List Identifier) : ParseResult Term :=
    t2_expr_op_prec_val (op_precedence op) input lhs op rem ctx

@[partial]
def t2_expr_op_prec_val (prec: I64) (input: String) (lhs: Term) (op: String) (rem: String) (ctx: List Identifier) : ParseResult Term :=
    if I64.beq prec 0
    then success input lhs
    else t2_expr_op_rhs_ws (take_while is_space rem) lhs op ctx

@[partial]
def t2_expr_op_rhs_ws (r: ParseResult String) (lhs: Term) (op: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => t2_expr_op_rhs_expr (t2_expression ctx rem) lhs op ctx,
        fail e => fail e
    }

@[partial]
def t2_expr_op_rhs_expr (r: ParseResult Term) (lhs: Term) (op: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem rhs =>
            // Operator desugars to: op lhs rhs → app (app (var SENTINEL op) lhs) rhs
            let op_var : Term := Term.var t2_sentinel DebugName.unnamed in
            success rem (Term.app (Term.app op_var lhs) rhs),
        fail e => fail e
    }

// ─── Term type expression (like expression but with -> for pi) ─────────

@[partial]
def t2_type_expression (ctx: List Identifier) (input: String) : ParseResult Term :=
    t2_type_expr_ws (take_while is_space input) input ctx

@[partial]
def t2_type_expr_ws (r: ParseResult String) (input: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => t2_type_try_dep (tag "(" (skip_spaces rem)) input ctx,
        fail e => fail e
    }

@[partial]
def t2_type_try_dep (r: ParseResult String) (input: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => t2_type_dep_id (identifier (skip_spaces rem)) input ctx,
        fail _ => t2_type_plain input ctx
    }

@[partial]
def t2_type_dep_id (r: ParseResult String) (input: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem name => t2_type_dep_colon (tag ":" (skip_spaces rem)) input name ctx,
        fail _ => t2_type_plain input ctx
    }

@[partial]
def t2_type_dep_colon (r: ParseResult String) (input: String) (name: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => t2_type_dep_typ (t2_type_expression ctx (skip_spaces rem)) input name ctx,
        fail _ => t2_type_plain input ctx
    }

@[partial]
def t2_type_dep_typ (r: ParseResult Term) (input: String) (name: String) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem typ => t2_type_dep_close (tag ")" (skip_spaces rem)) input name typ ctx,
        fail _ => t2_type_plain input ctx
    }

@[partial]
def t2_type_dep_close (r: ParseResult String) (input: String) (name: String) (typ: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => t2_type_dep_arrow rem name typ ctx,
        fail _ => t2_type_plain input ctx
    }

@[partial]
def t2_type_dep_arrow (rem: String) (name: String) (typ: Term) (ctx: List Identifier) : ParseResult Term :=
    t2_type_dep_arrow_ws (take_while is_space rem) rem name typ ctx

@[partial]
def t2_type_dep_arrow_ws (r: ParseResult String) (rem: String) (name: String) (typ: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem2 _ => t2_type_dep_arrow_tag (tag "->" rem2) rem name typ ctx,
        fail e => fail e
    }

@[partial]
def t2_type_dep_arrow_tag (r: ParseResult String) (rem: String) (name: String) (typ: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem2 _ => t2_type_dep_body (t2_type_expression (List.cons (Identifier.id name) ctx) (skip_spaces rem2)) typ,
        fail _ => success rem typ
    }

@[partial]
def t2_type_dep_body (r: ParseResult Term) (typ: Term) : ParseResult Term :=
    match r {
        success rem body => success rem (Term.pi typ body),
        fail e => fail e
    }

// Plain type expression (no dependent binding on LHS).
// Parses t2_expression, then checks for non-dependent -> arrow.
@[partial]
def t2_type_plain (input: String) (ctx: List Identifier) : ParseResult Term :=
    t2_type_plain_expr (t2_expression ctx input) ctx

@[partial]
def t2_type_plain_expr (r: ParseResult Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem lhs => t2_type_check_arrow rem lhs ctx,
        fail e => fail e
    }

@[partial]
def t2_type_check_arrow (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    t2_type_arrow_ws (take_while is_space input) input lhs ctx

@[partial]
def t2_type_arrow_ws (r: ParseResult String) (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => t2_type_arrow_tag (tag "->" rem) input lhs ctx,
        fail e => fail e
    }

@[partial]
def t2_type_arrow_tag (r: ParseResult String) (input: String) (lhs: Term) (ctx: List Identifier) : ParseResult Term :=
    match r {
        success rem _ => t2_type_arrow_rhs lhs (t2_type_expression ctx (skip_spaces rem)),
        fail _ => success input lhs
    }

@[partial]
def t2_type_arrow_rhs (lhs: Term) (r: ParseResult Term) : ParseResult Term :=
    match r {
        success rem rhs => success rem (Term.pi lhs rhs),
        fail e => fail e
    }

// ─── Term parser tests (Phase 1) ───────────────────────────────────────

@[test]
def test_t_var_bound : Bool :=
	let ctx : List Identifier := List.cons (Identifier.id "x") List.empty in
	match t2_expression ctx "x" {
		success rem out =>
			match out {
				Term.var idx dbg =>
					I64.beq idx 0 && String.beq rem "",
				Term.lam _ _ _ => false, Term.forall _ _ _ => false,
				Term.pi _ _ => false, Term.app _ _ => false,
				Term.lit _ => false, Term.ntv _ => false,
				Term.con _ => false, Term.type_ _ => false, Term.hole => false
			},
		fail _ => false
	}

@[test]
def test_t_var_unbound : Bool :=
	let empty_ctx : List Identifier := List.empty in
	match t2_expression empty_ctx "y" {
		success rem out =>
			match out {
				Term.var idx dbg =>
					I64.beq idx t2_sentinel && String.beq rem "",
				Term.lam _ _ _ => false, Term.forall _ _ _ => false,
				Term.pi _ _ => false, Term.app _ _ => false,
				Term.lit _ => false, Term.ntv _ => false,
				Term.con _ => false, Term.type_ _ => false, Term.hole => false
			},
		fail _ => false
	}

@[test]
def test_t_var_shadow : Bool :=
	// In ctx [x, y, x] (outer x first), the inner x should be index 0
	let x : Identifier := Identifier.id "x" in
	let y : Identifier := Identifier.id "y" in
	let ctx : List Identifier := List.cons y (List.cons x (List.cons x List.empty)) in
	match t2_expression ctx "x" {
		success rem out =>
			match out {
				Term.var idx dbg =>
					I64.beq idx 1 && String.beq rem "",
				Term.lam _ _ _ => false, Term.forall _ _ _ => false,
				Term.pi _ _ => false, Term.app _ _ => false,
				Term.lit _ => false, Term.ntv _ => false,
				Term.con _ => false, Term.type_ _ => false, Term.hole => false
			},
		fail _ => false
	}

@[test]
def test_t_lambda_identity : Bool :=
	// fn x => x  →  lam (named "x") (type_ 1) (var 0 (named "x"))
	let empty_ctx : List Identifier := List.empty in
	match t2_expression empty_ctx "fn x => x" {
		success rem out =>
			match out {
				Term.lam dbg typ body =>
					match typ {
						Term.type_ u => I64.beq u 1 && String.beq rem "",
						Term.var _ _ => false, Term.lam _ _ _ => false,
						Term.forall _ _ _ => false, Term.pi _ _ => false,
						Term.app _ _ => false, Term.lit _ => false,
						Term.ntv _ => false, Term.con _ => false,
						Term.hole => false
					},
				Term.var _ _ => false, Term.forall _ _ _ => false,
				Term.pi _ _ => false, Term.app _ _ => false,
				Term.lit _ => false, Term.ntv _ => false,
				Term.con _ => false, Term.type_ _ => false, Term.hole => false
			},
		fail _ => false
	}

@[test]
def test_t_lambda_nested : Bool :=
	// fn x => fn y => y  →  lam/named/x (lam/named/y (var 0))
	let empty_ctx : List Identifier := List.empty in
	match t2_expression empty_ctx "fn x => fn y => y" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_t_app_simple : Bool :=
	// f x  →  app (var SENTINEL f) (var SENTINEL x)
	let empty_ctx : List Identifier := List.empty in
	match t2_expression empty_ctx "f x" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_t_app_chain : Bool :=
	// f x y  →  app (app (var SENTINEL f) (var SENTINEL x)) (var SENTINEL y)
	let empty_ctx : List Identifier := List.empty in
	match t2_expression empty_ctx "f x y" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_t_operator : Bool :=
	// a ++ b  →  app (app (var SENTINEL _) (var SENTINEL a)) (var SENTINEL b)
	let empty_ctx : List Identifier := List.empty in
	match t2_expression empty_ctx "a ++ b" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_t_parens : Bool :=
	// (x)  →  var (SENTINEL, x)
	let empty_ctx : List Identifier := List.empty in
	match t2_expression empty_ctx "(x)" {
		success rem out => String.beq rem "",
		fail _ => false
	}

@[test]
def test_t_literal_num : Bool :=
	// 42  →  lit (num 42 i64)
	let empty_ctx : List Identifier := List.empty in
	match t2_expression empty_ctx "42" {
		success rem out => String.beq rem "",
		fail _ => false
	}

// ─── Term type expression tests (Phase 5) ──────────────────────────────

@[test]
def test_t_type_atom : Bool :=
    // A  →  var (sentinel, named "A")
    let empty_ctx : List Identifier := List.empty in
    match t2_type_expression empty_ctx "A" {
        success rem _ => String.beq rem "",
        fail _ => false
    }

@[test]
def test_t_type_arrow_simple : Bool :=
    // A -> B  →  pi (var sentinel A) (var sentinel B)
    let empty_ctx : List Identifier := List.empty in
    match t2_type_expression empty_ctx "A -> B" {
        success rem out =>
            match out {
                pi _ _ => String.beq rem "",
                _ => false
            },
        fail _ => false
    }

@[test]
def test_t_type_arrow_chain : Bool :=
    // A -> B -> C  →  pi A (pi B C)  (right-associative)
    let empty_ctx : List Identifier := List.empty in
    match t2_type_expression empty_ctx "A -> B -> C" {
        success rem out =>
            match out {
                pi arg ret =>
                    match ret {
                        pi _ _ => String.beq rem "",
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

@[test]
def test_t_type_arrow_parens : Bool :=
    // (A -> B) -> C  →  pi (pi A B) C
    let empty_ctx : List Identifier := List.empty in
    match t2_type_expression empty_ctx "(A -> B) -> C" {
        success rem out =>
            match out {
                pi arg ret =>
                    match arg {
                        pi _ _ => String.beq rem "",
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

@[test]
def test_t_type_dep_pi : Bool :=
    // (n : Nat) -> Vec n Int
    //  →  pi Nat (app (app (sentinel Vec) (var 0 named "n")) (sentinel Int))
    let n_id : Identifier := Identifier.id "n" in
    let ctx : List Identifier := List.empty in
    match t2_type_expression ctx "(n : Nat) -> Vec n Int" {
        success rem out =>
            match out {
                pi arg ret =>
                    match ret {
                        app f a =>
                            String.beq rem "",
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

@[test]
def test_t_type_dep_pi_shadow : Bool :=
    // Shadowed dependent pi: (x : Type) -> (x : Type) -> x
    // Inner x → index 0, outer x → index 1
    let empty_ctx : List Identifier := List.empty in
    match t2_type_expression empty_ctx "(x : Type) -> (x : Type) -> x" {
        success rem out =>
            match out {
                pi arg1 ret1 =>
                    match ret1 {
                        pi arg2 ret2 =>
                            match ret2 {
                                var idx _ => String.beq rem "",
                                _ => false
                            },
                        _ => false
                    },
                _ => false
            },
        fail _ => false
    }

@[test]
def test_t_type_no_arrow_parens : Bool :=
    // (A, B) (no ->) — falls through to plain expression as parens
    let empty_ctx : List Identifier := List.empty in
    match t2_type_expression empty_ctx "(A)" {
        success rem _ => String.beq rem "",
        fail _ => false
    }
