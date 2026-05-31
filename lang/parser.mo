/// Self-hosted Monad grammar parser.

/// Self-contained: defines local types to avoid module loading issues.



use lang.types
use std.list



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

def is_digit (c : String) : Bool :=
	 ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"]
        |> List.any (fn a => a == c)



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





@[partial]

def many1 (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=

	match many0 p input {

		success rem out =>

			if List.is_empty out

			then fail (ParseError.custom "expected at least one")

			else success rem out,

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

def at_least_two (ids : List String) : Bool :=

	Bool.not (List.is_empty (List.tail ids))



@[partial]

def path_variable (input : String) : ParseResult TermV0 :=

	match separated_by (tag ".") identifier input {

		success rem ids =>

			if at_least_two ids

			then success rem (TermV0.var (NameRef.nmp (ModulePath.mp (List.map Identifier.id ids))))

			else fail (ParseError.custom "not a dotted path"),

		fail e => fail e

	}





@[partial]

def skip_spaces (input : String) : String :=

	skip_spaces_match (take_while is_space input) input



@[partial]

def skip_spaces_match (r : ParseResult String) (orig : String) : String :=

	match r {

		success rem _ => rem,

		fail _ => orig

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

def t2_do_stmt_return (ctx: List Identifier) (input: String) : ParseResult DoStmt :=

    t2_do_stmt_ret_kw (tag "return" input) input ctx



@[partial]

def t2_do_stmt_ret_kw (r: ParseResult String) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=

    match r {

        success rem _ => t2_do_stmt_ret_expr (t2_expression ctx (skip_spaces rem)),

        fail _ => t2_do_stmt_try_let (tag "let" (skip_spaces orig)) orig ctx

    }



@[partial]

def t2_do_stmt_ret_expr (r: ParseResult Term) : ParseResult DoStmt :=

    match r {

        success rem value => success rem (DoStmt.ret_s value),

        fail e => fail e

    }



@[partial]

def t2_do_stmt_try_let (r: ParseResult String) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=

    match r {

        success rem _ => t2_do_stmt_let_name (identifier (skip_spaces rem)) ctx,

        fail _ => t2_do_stmt_expr (t2_expression ctx (skip_spaces orig))

    }



@[partial]

def t2_do_stmt_let_name (r: ParseResult String) (ctx: List Identifier) : ParseResult DoStmt :=

    match r {

        success rem name => t2_do_stmt_let_kind rem (Identifier.id name) ctx,

        fail e => fail e

    }



@[partial]

def t2_do_stmt_let_kind (input: String) (name: Identifier) (ctx: List Identifier) : ParseResult DoStmt :=

    t2_do_stmt_let_kind_try (tag ":=" (skip_spaces input)) name input ctx



@[partial]

def t2_do_stmt_let_kind_try (r: ParseResult String) (name: Identifier) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=

    match r {

        success rem _ => t2_do_stmt_let_value (t2_expression ctx (skip_spaces rem)) name,

        fail _ => t2_do_stmt_bind_arrow (tag "<-" (skip_spaces orig)) name orig ctx

    }



@[partial]

def t2_do_stmt_let_value (r: ParseResult Term) (name: Identifier) : ParseResult DoStmt :=

    match r {

        success rem value => success rem (DoStmt.let_s name value),

        fail e => fail e

    }



@[partial]

def t2_do_stmt_bind_arrow (r: ParseResult String) (name: Identifier) (orig: String) (ctx: List Identifier) : ParseResult DoStmt :=

    match r {

        success rem _ => t2_do_stmt_bind_value (t2_expression ctx (skip_spaces rem)) name,

        fail _ => fail (ParseError.custom "expected := or <- after let in do block")

    }



@[partial]

def t2_do_stmt_bind_value (r: ParseResult Term) (name: Identifier) : ParseResult DoStmt :=

    match r {

        success rem value => success rem (DoStmt.bind_s name value),

        fail e => fail e

    }



@[partial]

def t2_do_stmt_expr (r: ParseResult Term) : ParseResult DoStmt :=

    match r {

        success rem value => success rem (DoStmt.expr_s value),

        fail e => fail e

    }



@[partial]

def t2_do_stmts_extend_ctx (stmt: DoStmt) (ctx: List Identifier) : List Identifier :=

    match stmt {

        bind_s name _ => List.cons name ctx,

        let_s name _ => List.cons name ctx,

        _ => ctx

    }



@[partial]

def t2_do_stmts (ctx: List Identifier) (input: String) : ParseResult (List DoStmt) :=

    t2_do_stmts_check_end (tag "}" (skip_spaces input)) input ctx



@[partial]

def t2_do_stmts_check_end (r: ParseResult String) (orig: String) (ctx: List Identifier) : ParseResult (List DoStmt) :=

    match r {

        success rem _ =>

            let empty : List DoStmt := List.empty in

            success rem empty,

        fail _ => t2_do_stmts_first (t2_do_stmt_return ctx (skip_spaces orig)) (skip_spaces orig) ctx

    }



@[partial]

def t2_do_stmts_first (r: ParseResult DoStmt) (orig: String) (ctx: List Identifier) : ParseResult (List DoStmt) :=

    match r {

        success rem stmt => t2_do_stmts_next2 (t2_do_stmts (t2_do_stmts_extend_ctx stmt ctx) (do_stmts_tail rem)) stmt,

        fail e => fail e

    }



@[partial]

def t2_do_stmts_next2 (r: ParseResult (List DoStmt)) (first: DoStmt) : ParseResult (List DoStmt) :=

    match r {

        success rem rest => success rem (List.cons first rest),

        fail e => fail e

    }



@[partial]

def t2_do_parser (ctx: List Identifier) (input: String) : ParseResult Term :=

    t2_do_parser_kw (tag "do" input) ctx



@[partial]

def t2_do_parser_kw (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=

    match r {

        success rem _ => t2_do_parser_open (tag "{" (skip_spaces rem)) ctx,

        fail e => fail e

    }



@[partial]

def t2_do_parser_open (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=

    match r {

        success rem _ => t2_do_parser_stmts (t2_do_stmts ctx rem) ctx,

        fail e => fail e

    }



@[partial]

def t2_do_parser_stmts (r: ParseResult (List DoStmt)) (ctx: List Identifier) : ParseResult Term :=

    match r {

        success rem stmts => t2_do_parser_desugar rem stmts,

        fail e => fail e

    }



@[partial]

def t2_do_parser_desugar (rem: String) (stmts: List DoStmt) : ParseResult Term :=

    success rem (desugar_do stmts)



@[partial]
def is_newline (c : String) : Bool :=
	String.beq c "\n"

@[partial]
def is_not_newline (c : String) : Bool :=
	if String.beq c "\n" then false
	else true

@[partial]
def is_close_curly (c : String) : Bool :=
	String.beq c "}"

@[partial]
def is_not_close_curly (c : String) : Bool :=
	if String.beq c "}" then false
	else true


@[partial]

def is_op_char (c : String) : Bool :=

	op_char_member c op_chars



@[partial]

def op_check (s : String) (rem : String) : ParseResult String :=

	if is_empty s

	then fail (ParseError.custom "expected operator")

	else if I64.beq 0 (op_precedence s)

		then fail (ParseError.custom "unknown operator")

		else success rem s



@[partial]

def operator_parse (input : String) : ParseResult String :=

	bind_parse (take_while is_op_char) op_check input



@[partial]

def op_precedence (op : String) : I64 :=

	op_lookup_prec op op_table



@[partial]

def op_is_right_assoc (op : String) : Bool :=

	op_lookup_rassoc op op_table





@[partial]

def ids_to_module_path (ids : List String) : ModulePath :=

	ModulePath.mp (List.map Identifier.id ids)



@[partial]

def module_path_parser (input : String) : ParseResult ModulePath :=

	map_parse ids_to_module_path (separated_by (tag ".") identifier) input



// use module.path



@[partial]

def is_not_bracket (c : String) : Bool :=

	if String.beq "]" c then false

	else true



@[partial]

def is_not_attr_end (c : String) : Bool :=

	if String.beq "]" c then false

	else true



@[partial]

def t2_lam_params (params : List Param) (body : Term) : Term :=

	let rev : List Param := list_reverse params in

	t2_lam_params_loop rev body



@[partial]

def t2_lam_params_loop (params : List Param) (body : Term) : Term :=

	match params {

		List.cons p rest =>

			match p {

				Param.mk name type_ mult default =>

					t2_lam_params_loop rest (Term.lam (DebugName.named name) type_ body)

			},

		List.empty => body

	}



@[partial]

def t2_def_to_decl (body : Term) (name : Identifier) (typ : Term) : Decl :=

	let empty_constraints : List TypeConstraint := List.empty in

	let empty_attrs : List String := List.empty in

	Decl.def_d (Def.mk (ModulePath.mp (List.cons name List.empty)) typ body empty_constraints empty_attrs)



// --- Canonical declaration parsers (de Bruijn Term) ---



// Helper: build de Bruijn binding context from param names (reversed = innermost first).

@[partial]

def ctx_of_params (params : List Param) : List Identifier :=

	let empty_ctx : List Identifier := List.empty in

	ctx_of_params_loop params empty_ctx



@[partial]

def ctx_of_params_loop (params : List Param) (acc : List Identifier) : List Identifier :=

	match params {

		List.cons p rest =>

			match p {

				Param.mk name type_ mult default =>

					ctx_of_params_loop rest (List.cons name acc)

			},

		List.empty => acc

	}



// t2_use module.path

@[partial]

def t2_use_parser (input : String) : ParseResult Decl :=

	match tag "use" input {

		success rem _ => match module_path_parser (skip_spaces rem) {

			success rem2 path => success rem2 (Decl.use_d path),

			fail e => fail e

		},

		fail e => fail e

	}



// t2_open module.path

@[partial]

def t2_open_parser (input : String) : ParseResult Decl :=

	match tag "open" input {

		success rem _ => match module_path_parser (skip_spaces rem) {

			success rem2 path => success rem2 (Decl.open_d path),

			fail e => fail e

		},

		fail e => fail e

	}



// t2_infix:prec (op) := path

@[partial]

def t2_infix_parser (input : String) : ParseResult Decl :=

	t2_infix_kw (tag "infix" input)



@[partial]

def t2_infix_kw (r : ParseResult String) : ParseResult Decl :=

	match r {

		success rem _ => t2_infix_colon (tag ":" (skip_spaces rem)) rem,

		fail e => fail e

	}



@[partial]

def t2_infix_colon (r : ParseResult String) (orig : String) : ParseResult Decl :=

	match r {

		success rem _ => t2_infix_prec (number rem),

		fail _ => t2_infix_paren (tag "(" (skip_spaces orig)) orig

	}



@[partial]

def t2_infix_prec (r : ParseResult I64) : ParseResult Decl :=

	match r {

		success rem _ => t2_infix_paren (tag "(" (skip_spaces rem)) rem,

		fail e => fail e

	}



@[partial]

def t2_infix_paren (r : ParseResult String) (orig : String) : ParseResult Decl :=

	match r {

		success rem _ => t2_infix_op (operator_parse (skip_spaces rem)),

		fail e => fail e

	}



@[partial]

def t2_infix_op (r : ParseResult String) : ParseResult Decl :=

	match r {

		success rem op => t2_infix_close (tag ")" (skip_spaces rem)) op,

		fail e => fail e

	}



@[partial]

def t2_infix_close (r : ParseResult String) (op : String) : ParseResult Decl :=

	match r {

		success rem _ => t2_infix_assign (tag ":=" (skip_spaces rem)) op,

		fail e => fail e

	}



@[partial]

def t2_infix_assign (r : ParseResult String) (op : String) : ParseResult Decl :=

	match r {

		success rem _ => t2_infix_path (module_path_parser (skip_spaces rem)) op,

		fail e => fail e

	}



@[partial]

def t2_infix_path (r : ParseResult ModulePath) (op : String) : ParseResult Decl :=

	match r {

		success rem path => success rem (Decl.infix_d (Operator.operator op) path),

		fail e => fail e

	}



// t2_struct Name { field1 : Type, field2 : Type := default }

@[partial]

def t2_struct_parser (input : String) : ParseResult Decl :=

	t2_struct_kw (tag "struct" input)



@[partial]

def t2_struct_kw (r : ParseResult String) : ParseResult Decl :=

	match r {

		success rem _ => t2_struct_name (identifier (skip_spaces rem)),

		fail e => fail e

	}



@[partial]

def t2_struct_name (r : ParseResult String) : ParseResult Decl :=

	match r {

		success rem name => t2_struct_brace (tag "{" (skip_spaces rem)) (Identifier.id name),

		fail e => fail e

	}



@[partial]

def t2_struct_brace (r : ParseResult String) (name : Identifier) : ParseResult Decl :=

	match r {

		success rem _ => t2_struct_fields rem name,

		fail e => fail e

	}



@[partial]

def t2_struct_fields (input : String) (name : Identifier) : ParseResult Decl :=

	let empty_ctx : List Identifier := List.empty in

	match separated_by (tag ",") (preceded_by ws0 (t2_struct_one_field empty_ctx)) input {

		success rem fields =>

			match tag "}" (skip_spaces rem) {

				success rem2 _ => success rem2 (Decl.struct_d (Struct.mk name fields)),

				fail e => fail (ParseError.custom "expected }")

			},

		fail e => fail e

	}



@[partial]

def t2_struct_one_field (ctx : List Identifier) (input : String) : ParseResult StructField :=

	t2_struct_field_name (identifier input) ctx



@[partial]

def t2_struct_field_name (r : ParseResult String) (ctx : List Identifier) : ParseResult StructField :=

	match r {

		success rem name => t2_struct_field_colon (tag ":" (skip_spaces rem)) (Identifier.id name) ctx,

		fail e => fail e

	}



@[partial]

def t2_struct_field_colon (r : ParseResult String) (name : Identifier) (ctx : List Identifier) : ParseResult StructField :=

	match r {

		success rem _ => t2_struct_field_type (t2_type_expression ctx (skip_spaces rem)) name ctx,

		fail e => fail e

	}



@[partial]

def t2_struct_field_type (r : ParseResult Term) (name : Identifier) (ctx : List Identifier) : ParseResult StructField :=

	match r {

		success rem typ => t2_struct_field_default (tag ":=" (skip_spaces rem)) rem name typ ctx,

		fail e => fail e

	}



@[partial]

def t2_struct_field_default (r : ParseResult String) (orig : String) (name : Identifier) (typ : Term) (ctx : List Identifier) : ParseResult StructField :=

	match r {

		success rem _ => t2_struct_field_default_val (t2_expression ctx (skip_spaces rem)) name typ,

		fail _ =>

			let none : Option Term := Option.none in

			success orig (StructField.mk name typ none)

	}



@[partial]

def t2_struct_field_default_val (r : ParseResult Term) (name : Identifier) (typ : Term) : ParseResult StructField :=

	match r {

		success rem defval =>

			let some_val : Option Term := Option.some defval in

			success rem (StructField.mk name typ some_val),

		fail e => fail e

	}



// t2_type Name { constructor1 (args), constructor2 }

@[partial]

def t2_type_parser (input : String) : ParseResult Decl :=

	t2_type_kw (tag "type" input)



@[partial]

def t2_type_kw (r : ParseResult String) : ParseResult Decl :=

	match r {

		success rem _ => t2_type_name (identifier (skip_spaces rem)),

		fail e => fail e

	}



@[partial]

def t2_type_name (r : ParseResult String) : ParseResult Decl :=

	match r {

		success rem name =>

			let empty_params : List Identifier := List.empty in

			t2_type_params_skip rem (Identifier.id name) empty_params,

		fail e => fail e

	}



@[partial]

def t2_type_params_skip (input : String) (name : Identifier) (params : List Identifier) : ParseResult Decl :=

	t2_type_params_skip_try (identifier (skip_spaces input)) input name params



@[partial]

def t2_type_params_skip_try (r : ParseResult String) (orig : String) (name : Identifier) (params : List Identifier) : ParseResult Decl :=

	match r {

		success rem next => t2_type_params_skip rem name (List.cons (Identifier.id next) params),

		fail _ => t2_type_brace (tag "{" (skip_spaces orig)) name

	}



@[partial]

def t2_type_brace (r : ParseResult String) (name : Identifier) : ParseResult Decl :=

	match r {

		success rem _ => t2_type_constructors rem name,

		fail e => fail e

	}



@[partial]

def t2_type_constructors (input : String) (name : Identifier) : ParseResult Decl :=

	let empty_ctx : List Identifier := List.empty in

	match separated_by (tag ",") (preceded_by ws0 (t2_type_one_constructor empty_ctx)) input {

		success rem cons =>

			match tag "}" (skip_spaces rem) {

				success rem2 _ => success rem2 (t2_type_to_decl name cons),

				fail e => fail (ParseError.custom "expected }")

			},

		fail e => fail e

	}



@[partial]

def t2_type_one_constructor (ctx : List Identifier) (input : String) : ParseResult InductConstructor :=

	t2_type_cons_name (identifier input) ctx



@[partial]

def t2_type_cons_name (r : ParseResult String) (ctx : List Identifier) : ParseResult InductConstructor :=

	match r {

		success rem name => t2_type_cons_paren_or_nil (tag "(" (skip_spaces rem)) rem (Identifier.id name) ctx,

		fail e => fail e

	}



@[partial]

def t2_type_cons_paren_or_nil (r : ParseResult String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=

	match r {

		success rem _ => t2_type_cons_params (t2_type_param_list ctx rem) name,

		fail _ => t2_type_cons_implicit (tag "{" (skip_spaces orig)) orig name ctx

	}



@[partial]

def t2_type_cons_implicit (r : ParseResult String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=

	match r {

		success rem _ => t2_type_cons_implicit_skip (take_while is_not_close_curly rem) rem orig name ctx,

		fail _ =>

			let empty_params : List Param := List.empty in

			success orig (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) empty_params (Term.hole))

	}



@[partial]

def t2_type_cons_implicit_skip (r : ParseResult String) (rem : String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=

	match r {

		success after_bracket _ => t2_type_cons_implicit_close (tag "}" (skip_spaces after_bracket)) after_bracket orig name ctx,

		fail _ =>

			let empty_params : List Param := List.empty in

			success orig (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) empty_params (Term.hole))

	}



@[partial]

def t2_type_cons_implicit_close (r : ParseResult String) (after_bracket : String) (orig : String) (name : Identifier) (ctx : List Identifier) : ParseResult InductConstructor :=

	match r {

		success rem _ => t2_type_cons_paren_or_nil (tag "(" (skip_spaces rem)) rem name ctx,

		fail _ =>

			let empty_params : List Param := List.empty in

			success after_bracket (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) empty_params (Term.hole))

	}



@[partial]

def t2_type_cons_params (r : ParseResult (List Param)) (name : Identifier) : ParseResult InductConstructor :=

	match r {

		success rem params => t2_type_cons_close_paren (tag ")" (skip_spaces rem)) name params,

		fail e => fail e

	}



@[partial]

def t2_type_cons_close_paren (r : ParseResult String) (name : Identifier) (params : List Param) : ParseResult InductConstructor :=

	match r {

		success rem _ => success rem (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) params (Term.hole)),

		fail e => fail e

	}



@[partial]

def t2_type_param_list (ctx : List Identifier) (input : String) : ParseResult (List Param) :=

	separated_by (tag ",") (preceded_by ws0 (t2_type_one_param ctx)) input



@[partial]

def t2_type_one_param (ctx : List Identifier) (input : String) : ParseResult Param :=

	t2_type_one_param_name (identifier input) ctx



@[partial]

def t2_type_one_param_name (r : ParseResult String) (ctx : List Identifier) : ParseResult Param :=

	match r {

		success rem name => t2_type_one_param_type (tag ":" (skip_spaces rem)) (Identifier.id name) ctx,

		fail e => fail e

	}



@[partial]

def t2_type_one_param_type (r : ParseResult String) (name : Identifier) (ctx : List Identifier) : ParseResult Param :=

	match r {

		success rem _ => t2_type_one_param_val (t2_type_expression ctx (skip_spaces rem)) name,

		fail e => fail e

	}



@[partial]

def t2_type_one_param_val (r : ParseResult Term) (name : Identifier) : ParseResult Param :=

	match r {

		success rem typ => success rem (param_many name typ),

		fail e => fail e

	}



@[partial]

def t2_type_to_decl (name : Identifier) (cons : List InductConstructor) : Decl :=

	let empty_params : List Param := List.empty in

	let empty_attrs : List String := List.empty in

	Decl.inductive_d (Inductive.mk (ModulePath.mp (List.cons name List.empty)) empty_params (Term.type_ 1) cons empty_attrs)



// t2_def [@attrs] name {implicit} (explicit) : ret_type := body

@[partial]

def t2_def_parser (input : String) : ParseResult Decl :=

	t2_def_try_attrs (tag "@[" (skip_spaces input)) input



@[partial]

def t2_def_try_attrs (r : ParseResult String) (orig : String) : ParseResult Decl :=

	match r {

		success rem _ => t2_def_attr_skip (take_while is_not_attr_end rem) rem,

		fail _ => t2_def_kw (tag "def" (skip_spaces orig))

	}



@[partial]

def t2_def_attr_skip (r : ParseResult String) (rest : String) : ParseResult Decl :=

	match r {

		success rem _ => t2_def_attr_close (tag "]" rem),

		fail _ => fail (ParseError.custom "expected ]")

	}



@[partial]

def t2_def_attr_close (r : ParseResult String) : ParseResult Decl :=

	match r {

		success rem _ => t2_def_kw (tag "def" (skip_spaces rem)),

		fail e => fail e

	}



@[partial]

def t2_def_kw (r : ParseResult String) : ParseResult Decl :=

	match r {

		success rem _ => t2_def_name (identifier (skip_spaces rem)),

		fail e => fail e

	}



@[partial]

def t2_def_name (r : ParseResult String) : ParseResult Decl :=

	match r {

		success rem name =>

			let empty : List Param := List.empty in

			t2_def_params (t2_def_params_loop (skip_spaces rem) empty) (Identifier.id name),

		fail e => fail e

	}



@[partial]

def t2_def_params_loop (input : String) (params : List Param) : ParseResult (List Param) :=

	t2_def_params_try_implicit (tag "{" input) input params



@[partial]

def t2_def_params_try_implicit (r : ParseResult String) (orig : String) (params : List Param) : ParseResult (List Param) :=

	match r {

		success rem _ => t2_def_implicit_param (identifier (skip_spaces rem)) rem params,

		fail _ => t2_def_params_try_explicit (tag "(" orig) orig params

	}



@[partial]

def t2_def_implicit_param (r : ParseResult String) (rem : String) (params : List Param) : ParseResult (List Param) :=

	match r {

		success rem2 name => t2_def_implicit_colon (tag ":" (skip_spaces rem2)) rem rem2 name params,

		fail e => fail e

	}



@[partial]

def t2_def_implicit_colon (r : ParseResult String) (brace_rem : String) (rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=

	match r {

		success rem2 _ =>

			let empty_ctx : List Identifier := List.empty in

			t2_def_implicit_type (t2_type_expression empty_ctx rem2) brace_rem rem name params,

		fail e => fail e

	}



@[partial]

def t2_def_implicit_type (r : ParseResult Term) (brace_rem : String) (rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=

	match r {

		success rem2 typ => t2_def_implicit_close (tag "}" rem2) brace_rem name typ params,

		fail e => fail e

	}



@[partial]

def t2_def_implicit_close (r : ParseResult String) (brace_rem : String) (name : String) (typ : Term) (params : List Param) : ParseResult (List Param) :=

	match r {

		success rem2 _ =>

			let empty : List Param := List.empty in

			t2_def_params_loop (skip_spaces rem2) empty,

		fail e => fail e

	}



@[partial]

def t2_def_params_try_explicit (r : ParseResult String) (orig : String) (params : List Param) : ParseResult (List Param) :=

	match r {

		success rem _ => t2_def_explicit_param (identifier (skip_spaces rem)) rem params,

		fail _ =>

			let rev : List Param := list_reverse params in

			success orig rev

	}



@[partial]

def t2_def_explicit_param (r : ParseResult String) (close_rem : String) (params : List Param) : ParseResult (List Param) :=

	match r {

		success rem name => t2_def_explicit_colon (tag ":" (skip_spaces rem)) close_rem name params,

		fail e => fail e

	}



@[partial]

def t2_def_explicit_colon (r : ParseResult String) (close_rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=

	match r {

		success rem _ =>

			let empty_ctx : List Identifier := List.empty in

			t2_def_explicit_type (t2_type_expression empty_ctx rem) close_rem name params,

		fail e => fail e

	}



@[partial]

def t2_def_explicit_type (r : ParseResult Term) (close_rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=

	match r {

		success rem typ => t2_def_explicit_close (tag ")" rem) close_rem name typ params,

		fail e => fail e

	}



@[partial]

def t2_def_explicit_close (r : ParseResult String) (close_rem : String) (name : String) (typ : Term) (params : List Param) : ParseResult (List Param) :=

	match r {

		success rem _ => t2_def_params_loop (skip_spaces rem) (List.cons (param_many (Identifier.id name) typ) params),

		fail e => fail e

	}



@[partial]

def t2_def_params (r : ParseResult (List Param)) (name : Identifier) : ParseResult Decl :=

	match r {

		success rem params => t2_def_ret_type (tag ":" (skip_spaces rem)) rem name params,

		fail e => fail e

	}



@[partial]

def t2_def_ret_type (r : ParseResult String) (orig : String) (name : Identifier) (params : List Param) : ParseResult Decl :=

	match r {

		success rem _ =>

			let empty_ctx : List Identifier := List.empty in

			t2_def_ret_expr (t2_type_expression empty_ctx rem) name params,

		fail _ => fail (ParseError.custom "expected : return type")

	}



@[partial]

def t2_def_ret_expr (r : ParseResult Term) (name : Identifier) (params : List Param) : ParseResult Decl :=

	match r {

		success rem typ => t2_def_body rem name params typ,

		fail e => fail e

	}



@[partial]

def t2_def_body (input : String) (name : Identifier) (params : List Param) (typ : Term) : ParseResult Decl :=

	t2_def_body_assign (tag ":=" (skip_spaces input)) name params typ input



@[partial]

def t2_def_body_assign (r : ParseResult String) (name : Identifier) (params : List Param) (typ : Term) (orig : String) : ParseResult Decl :=

	match r {

		success rem _ => t2_def_body_expr (t2_expression (ctx_of_params params) (skip_spaces rem)) name params typ,

		fail _ => t2_def_body_block_or_none (tag "{" (skip_spaces orig)) name params typ orig

	}



@[partial]

def t2_def_body_block_or_none (r : ParseResult String) (name : Identifier) (params : List Param) (typ : Term) (orig : String) : ParseResult Decl :=

	match r {

		success rem _ => t2_def_body_do (t2_do_stmts (ctx_of_params params) rem) name params typ,

		fail _ => success orig (t2_def_to_decl (t2_lam_params params (Term.hole)) name typ)

	}



@[partial]

def t2_def_body_expr (r : ParseResult Term) (name : Identifier) (params : List Param) (typ : Term) : ParseResult Decl :=

	match r {

		success rem body => success rem (t2_def_to_decl (t2_lam_params params body) name typ),

		fail e => fail e

	}



@[partial]

def t2_def_body_block (r : ParseResult String) (name : Identifier) (params : List Param) (typ : Term) : ParseResult Decl :=

	match r {

		success rem _ => t2_def_body_do (t2_do_stmts (ctx_of_params params) rem) name params typ,

		fail e => fail e

	}



@[partial]

def t2_def_body_do (r : ParseResult (List DoStmt)) (name : Identifier) (params : List Param) (typ : Term) : ParseResult Decl :=

	match r {

		success rem stmts => success rem (t2_def_to_decl (t2_lam_params params (desugar_do stmts)) name typ),

		fail e => fail e

	}




// ---------- TypeConstraint parser ----------

@[partial]
def t2_type_constraint_one (input : String) : ParseResult TypeConstraint :=
	t2_type_constraint_one_name (module_path_parser input) input

@[partial]
def t2_type_constraint_one_name (r : ParseResult ModulePath) (orig : String) : ParseResult TypeConstraint :=
	match r {
		success rem cls =>
			let empty_vars : List Identifier := List.empty in
			t2_type_constraint_vars (take_while is_ident_char (skip_spaces rem)) cls empty_vars rem,
		fail _ => fail (ParseError.custom "expected class name in constraint")
	}

@[partial]
def t2_type_constraint_vars (r : ParseResult String) (cls : ModulePath) (acc : List Identifier) (orig : String) : ParseResult TypeConstraint :=
	match r {
		success rest ident =>
			if is_empty ident
			then success rest (TypeConstraint.mk cls (list_reverse acc))
			else t2_type_constraint_vars (take_while is_ident_char (skip_spaces rest)) cls (List.cons (Identifier.id ident) acc) orig,
		fail _ => success orig (TypeConstraint.mk cls (list_reverse acc))
	}

@[partial]
def t2_type_constraint_list (input : String) : ParseResult (List TypeConstraint) :=
	t2_type_constraint_list_loop (skip_spaces input) List.empty

@[partial]
def t2_type_constraint_list_loop (input : String) (acc : List TypeConstraint) : ParseResult (List TypeConstraint) :=
	t2_type_constraint_list_try (t2_type_constraint_one input) input acc

@[partial]
def t2_type_constraint_list_try (r : ParseResult TypeConstraint) (orig : String) (acc : List TypeConstraint) : ParseResult (List TypeConstraint) :=
	match r {
		success rem constraint =>
			t2_type_constraint_list_comma (tag "," (skip_spaces rem)) rem constraint acc,
		fail _ => success orig (list_reverse acc)
	}

@[partial]
def t2_type_constraint_list_comma (r : ParseResult String) (rem : String) (constraint : TypeConstraint) (acc : List TypeConstraint) : ParseResult (List TypeConstraint) :=
	match r {
		success after_comma _ =>
			t2_type_constraint_list_loop (skip_spaces after_comma) (List.cons constraint acc),
		fail _ => success rem (list_reverse (List.cons constraint acc))
	}


// t2_class [constraints] Name params { def method sig, def method sig := default }

@[partial]

def t2_class_parser (input : String) : ParseResult Decl :=

	t2_class_kw (tag "class" input)



@[partial]

def t2_class_kw (r : ParseResult String) : ParseResult Decl :=

	match r {

		success rem _ => t2_class_constraints_or_name rem,

		fail e => fail e

	}



@[partial]

def t2_class_constraints_or_name (input : String) : ParseResult Decl :=

	t2_class_try_constraints (tag "[" (skip_spaces input)) input



@[partial]

def t2_class_try_constraints (r : ParseResult String) (orig : String) : ParseResult Decl :=

	match r {

		success rem _ => t2_class_name_after_bracket rem,

		fail _ => t2_class_name (identifier (skip_spaces orig))

	}



@[partial]

def t2_class_name_after_bracket (input : String) : ParseResult Decl :=

	t2_class_find_bracket_close (take_while is_not_bracket input) input



@[partial]

def t2_class_find_bracket_close (r : ParseResult String) (orig : String) : ParseResult Decl :=

	match r {

		success rem _ => t2_class_name_after_close (tag "]" rem) orig,

		fail _ => fail (ParseError.custom "expected ]")

	}



@[partial]

def t2_class_name_after_close (r : ParseResult String) (orig : String) : ParseResult Decl :=

	match r {

		success rem _ => t2_class_name (identifier (skip_spaces rem)),

		fail _ => t2_class_name (identifier (skip_spaces orig))

	}



@[partial]

def t2_class_name (r : ParseResult String) : ParseResult Decl :=

	match r {

		success rem name =>

			let empty_params : List Identifier := List.empty in

			t2_class_params rem (Identifier.id name) empty_params,

		fail e => fail e

	}



@[partial]

def t2_class_params (input : String) (name : Identifier) (params : List Identifier) : ParseResult Decl :=

	t2_class_params_try (identifier (skip_spaces input)) input name params



@[partial]

def t2_class_params_try (r : ParseResult String) (orig : String) (name : Identifier) (params : List Identifier) : ParseResult Decl :=

	match r {

		success rem next => t2_class_params rem name (List.cons (Identifier.id next) params),

		fail _ => t2_class_brace (tag "{" (skip_spaces orig)) name

	}



@[partial]

def t2_class_brace (r : ParseResult String) (name : Identifier) : ParseResult Decl :=

	match r {

		success rem _ =>

			let empty_methods : List ClassDef := List.empty in

			t2_class_methods rem name empty_methods,

		fail e => fail e

	}



@[partial]

def t2_class_methods (input : String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	t2_class_try_close_or_method (tag "def" (skip_spaces input)) input name methods



@[partial]

def t2_class_try_close_or_method (r : ParseResult String) (orig : String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	match r {

		success rem _ => t2_class_methods_single rem name methods,

		fail _ => t2_class_close (tag "}" (skip_spaces orig)) name methods

	}



@[partial]

def t2_class_methods_single (input : String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	t2_class_method_name (identifier (skip_spaces input)) name methods



@[partial]

def t2_class_method_name (r : ParseResult String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	match r {

		success rem mname => t2_class_method_colon_or_sig rem (Identifier.id mname) name methods,

		fail e => fail e

	}



@[partial]

def t2_class_method_colon_or_sig (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	t2_class_method_params_try (tag "(" (skip_spaces input)) input mname name methods



@[partial]

def t2_class_method_params_try (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	match r {

		success rem _ => t2_class_method_param_loop rem mname name methods,

		fail _ => t2_class_method_ret_type (tag ":" (skip_spaces orig)) mname name methods

	}



@[partial]

def t2_class_method_param_loop (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	t2_class_method_one_param (identifier (skip_spaces input)) input mname name methods



@[partial]

def t2_class_method_one_param (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	match r {

		success rem pname => t2_class_method_param_colon (tag ":" (skip_spaces rem)) mname name methods orig,

		fail e => fail e

	}



@[partial]

def t2_class_method_param_colon (r : ParseResult String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (orig : String) : ParseResult Decl :=

	match r {

		success rem _ =>

			let empty_ctx : List Identifier := List.empty in

			t2_class_method_param_type (t2_type_expression empty_ctx rem) mname name methods orig,

		fail e => fail e

	}



@[partial]

def t2_class_method_param_type (r : ParseResult Term) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (orig : String) : ParseResult Decl :=

	match r {

		success rem _ => t2_class_method_close_or_next rem mname name methods orig,

		fail e => fail e

	}



@[partial]

def t2_class_method_close_or_next (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) (orig : String) : ParseResult Decl :=

	t2_class_method_try_close_param (tag ")" (skip_spaces input)) input mname name methods



@[partial]

def t2_class_method_try_close_param (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	match r {

		success rem _ => t2_class_method_ret_or_more rem mname name methods,

		fail _ => t2_class_method_next_param (tag "(" (skip_spaces orig)) orig mname name methods

	}



@[partial]

def t2_class_method_ret_or_more (input : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	t2_class_method_try_ret_type (tag ":" (skip_spaces input)) input mname name methods



@[partial]

def t2_class_method_try_ret_type (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	match r {

		success rem _ =>

			let empty_ctx : List Identifier := List.empty in

			t2_class_method_ret_type_val (t2_type_expression empty_ctx rem) mname name methods,

		fail _ => t2_class_method_next_param (tag "(" (skip_spaces orig)) orig mname name methods

	}



@[partial]

def t2_class_method_ret_type_val (r : ParseResult Term) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	match r {

		success rem typ => t2_class_method_default_or_done rem mname typ name methods,

		fail e => fail e

	}



@[partial]

def t2_class_method_next_param (r : ParseResult String) (orig : String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	match r {

		success rem _ => t2_class_method_param_loop rem mname name methods,

		fail _ => fail (ParseError.custom "expected ) or another parameter")

	}



@[partial]

def t2_class_method_ret_type (r : ParseResult String) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	match r {

		success rem _ =>

			let empty_ctx : List Identifier := List.empty in

			t2_class_method_sig_type (t2_type_expression empty_ctx rem) mname name methods,

		fail _ => fail (ParseError.custom "expected : return type")

	}



@[partial]

def t2_class_method_sig_type (r : ParseResult Term) (mname : Identifier) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	match r {

		success rem typ => t2_class_method_default_or_done rem mname typ name methods,

		fail e => fail e

	}



@[partial]

def t2_class_method_default_or_done (input : String) (mname : Identifier) (typ : Term) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	t2_class_method_try_default (tag ":=" (skip_spaces input)) input mname typ name methods



@[partial]

def t2_class_method_try_default (r : ParseResult String) (orig : String) (mname : Identifier) (typ : Term) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	match r {

		success rem _ =>

			let empty_ctx : List Identifier := List.empty in

			t2_class_method_default_val (t2_expression empty_ctx (skip_spaces rem)) orig mname typ name methods,

		fail _ =>

			let none_val : Option Term := Option.none in

			t2_class_methods orig name (List.cons (ClassDef.mk mname typ none_val) methods)

	}



@[partial]

def t2_class_method_default_val (r : ParseResult Term) (orig : String) (mname : Identifier) (typ : Term) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	match r {

		success rem defval =>

			let some_val : Option Term := Option.some defval in

			t2_class_methods rem name (List.cons (ClassDef.mk mname typ some_val) methods),

		fail e => fail e

	}



@[partial]

def t2_class_close (r : ParseResult String) (name : Identifier) (methods : List ClassDef) : ParseResult Decl :=

	match r {

		success rem _ =>

			let rev_methods : List ClassDef := list_reverse methods in

			let empty_params : List Param := List.empty in

			let empty_constraints : List TypeConstraint := List.empty in

			success rem (Decl.class_d (Class.mk name empty_params empty_constraints rev_methods)),

		fail e => fail e

	}



// t2_instance [constraints] Class args { def method := body }

@[partial]

def t2_instance_parser (input : String) : ParseResult Decl :=

	t2_instance_kw (tag "instance" input)



@[partial]

def t2_instance_kw (r : ParseResult String) : ParseResult Decl :=

	match r {

		success rem _ => t2_instance_try_constraints (tag "[" (skip_spaces rem)) rem,

		fail e => fail e

	}



@[partial]

def t2_instance_try_constraints (r : ParseResult String) (orig : String) : ParseResult Decl :=

	match r {

		success rem _ => t2_instance_parse_bracket rem,

		fail _ => t2_instance_name (module_path_parser (skip_spaces orig))

	}




@[partial]

def t2_instance_parse_bracket (input : String) : ParseResult Decl :=

	t2_instance_constraints_with_bracket (take_while is_not_bracket input) input



@[partial]

def t2_instance_constraints_with_bracket (r : ParseResult String) (orig : String) : ParseResult Decl :=

	match r {

		success rem content =>

			t2_instance_constraints_then_name (t2_type_constraint_list content) rem,

		fail _ => fail (ParseError.custom "expected ]")

	}



@[partial]

def t2_instance_constraints_then_name (cr : ParseResult (List TypeConstraint)) (input : String) : ParseResult Decl :=

	match cr {

		success _ constraints =>

			t2_instance_constraints_close_bracket (tag "]" input) constraints,

		fail _ =>

			let empty_cs : List TypeConstraint := List.empty in

			t2_instance_constraints_close_bracket (tag "]" input) empty_cs

	}



@[partial]

def t2_instance_constraints_close_bracket (r : ParseResult String) (constraints : List TypeConstraint) : ParseResult Decl :=

	match r {

		success rem _ =>

			t2_instance_set_constraints (t2_instance_name (module_path_parser (skip_spaces rem))) constraints,

		fail _ => fail (ParseError.custom "expected ] after instance constraint")

	}



@[partial]

def t2_instance_set_constraints (dr : ParseResult Decl) (constraints : List TypeConstraint) : ParseResult Decl :=

	match dr {

		success rem decl =>

			match decl {

				instance_d inst =>

					match inst {

						Instance.mk name cls _ args =>

							success rem (Decl.instance_d (Instance.mk name cls constraints args))

					},

				_ => success rem decl

			},

		fail e => fail e

	}



@[partial]

def t2_instance_name (r : ParseResult ModulePath) : ParseResult Decl :=

	match r {

		success rem path =>

			let empty_args : List Term := List.empty in

			t2_instance_args_or_brace rem path empty_args,

		fail e => fail e

	}



@[partial]

def t2_instance_args_or_brace (input : String) (cls : ModulePath) (args : List Term) : ParseResult Decl :=

	let empty_ctx : List Identifier := List.empty in

	t2_instance_try_arg (t2_atom_term empty_ctx (skip_spaces input)) input cls args



@[partial]

def t2_instance_try_arg (r : ParseResult Term) (orig : String) (cls : ModulePath) (args : List Term) : ParseResult Decl :=

	match r {

		success rem arg => t2_instance_args_or_brace rem cls (List.cons arg args),

		fail _ => t2_instance_brace (tag "{" (skip_spaces orig)) cls args

	}



@[partial]

def t2_instance_brace (r : ParseResult String) (cls : ModulePath) (args : List Term) : ParseResult Decl :=

	match r {

		success rem _ =>

			let empty_methods : List Def := List.empty in

			t2_instance_methods rem cls args empty_methods,

		fail e => fail e

	}



@[partial]

def t2_instance_methods (input : String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=

	t2_instance_try_close_or_def (tag "def" (skip_spaces input)) input cls args methods



@[partial]

def t2_instance_try_close_or_def (r : ParseResult String) (orig : String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=

	match r {

		success rem _ => t2_instance_method_single rem cls args methods,

		fail _ => t2_instance_close (tag "}" (skip_spaces orig)) cls args methods

	}



@[partial]

def t2_instance_method_single (input : String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=

	t2_instance_method_name (identifier (skip_spaces input)) cls args methods



@[partial]

def t2_instance_method_name (r : ParseResult String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=

	match r {

		success rem name => t2_instance_method_params_or_body rem (Identifier.id name) cls args methods,

		fail e => fail e

	}



@[partial]

def t2_instance_method_params_or_body (input : String) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=

	let empty_ctx : List Identifier := List.empty in

	t2_instance_method_try_body (t2_atom_term empty_ctx (skip_spaces input)) input name cls args methods



@[partial]

def t2_instance_method_try_body (r : ParseResult Term) (orig : String) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=

	match r {

		success rem arg =>

			let start_args : List Term := List.cons arg List.empty in

			t2_instance_method_body_loop rem start_args name cls args methods,

		fail _ => t2_instance_method_finish (tag ":=" (skip_spaces orig)) name cls args methods

	}



@[partial]

def t2_instance_method_body_loop (input : String) (body_args : List Term) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=

	let empty_ctx : List Identifier := List.empty in

	t2_instance_method_body_next (t2_atom_term empty_ctx (skip_spaces input)) input body_args name cls args methods



@[partial]

def t2_instance_method_body_next (r : ParseResult Term) (orig : String) (body_args : List Term) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=

	match r {

		success rem arg => t2_instance_method_body_loop rem (List.cons arg body_args) name cls args methods,

		fail _ => t2_instance_method_finish (tag ":=" (skip_spaces orig)) name cls args methods

	}



@[partial]

def t2_instance_method_finish (r : ParseResult String) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=

	match r {

		success rem _ =>

			let empty_ctx : List Identifier := List.empty in

			t2_instance_method_body (t2_expression empty_ctx (skip_spaces rem)) name cls args methods,

		fail _ => fail (ParseError.custom "expected := in instance method")

	}



@[partial]

def t2_instance_method_body (r : ParseResult Term) (name : Identifier) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=

	match r {

		success rem body =>

			let empty_constraints : List TypeConstraint := List.empty in

			let empty_attrs : List String := List.empty in

			let d : Def := Def.mk (ModulePath.mp (List.cons name List.empty)) (Term.hole) body empty_constraints empty_attrs in

			t2_instance_methods rem cls args (List.cons d methods),

		fail e => fail e

	}



@[partial]

def t2_instance_close (r : ParseResult String) (cls : ModulePath) (args : List Term) (methods : List Def) : ParseResult Decl :=

	match r {

		success rem _ =>

			let rev_methods : List Def := list_reverse methods in

			let rev_args : List Term := list_reverse args in

			let empty_constraints : List TypeConstraint := List.empty in

			success rem (Decl.instance_d (Instance.mk (Identifier.id "_") cls empty_constraints rev_args)),

		fail e => fail e

	}



// Canonical decl dispatcher

def t2_decl_parsers : List (String -> ParseResult Decl) :=

	[t2_use_parser, t2_open_parser, t2_infix_parser, t2_def_parser,

	 t2_struct_parser, t2_type_parser, t2_class_parser, t2_instance_parser]



@[partial]

def t2_decl_parser (input : String) : ParseResult Decl :=

	t2_decl_fail_to_unknown (alt_fold t2_decl_parsers input)



@[partial]

def t2_decl_fail_to_unknown (r : ParseResult Decl) : ParseResult Decl :=

	match r {

		success rem out => success rem out,

		fail _ => fail (ParseError.custom "unknown declaration")

	}



// ─── Multiple declaration parser (file-level) ──────────────────────────



@[partial]

def t2_decls_parser (input : String) : ParseResult (List Decl) :=

	t2_decls_skip (skip_docstrings (skip_spaces input)) List.empty



@[partial]

def t2_decls_skip (input : String) (acc : List Decl) : ParseResult (List Decl) :=

	t2_decls_try (t2_decl_parser input) input acc



@[partial]

def t2_decls_try (r : ParseResult Decl) (orig : String) (acc : List Decl) : ParseResult (List Decl) :=

	match r {

		success rem decl => t2_decls_skip (skip_spaces rem) (List.cons decl acc),

		fail _ => success orig (list_reverse acc)

	}



// Top-level declaration dispatcher



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

def test_t2_do_empty : Bool :=

    let empty_ctx : List Identifier := List.empty in

    match t2_do_parser empty_ctx "do { }" {

        success rem _ => String.beq rem "",

        fail _ => false

    }



@[test]

def test_t2_do_return : Bool :=

    let empty_ctx : List Identifier := List.empty in

    match t2_do_parser empty_ctx "do { return 42 }" {

        success rem _ => String.beq rem "",

        fail _ => false

    }



@[test]

def test_t2_do_bind : Bool :=

    let empty_ctx : List Identifier := List.empty in

    match t2_do_parser empty_ctx "do { let x <- m; return x }" {

        success rem _ => String.beq rem "",

        fail _ => false

    }



@[test]

def test_t2_do_let : Bool :=

    let empty_ctx : List Identifier := List.empty in

    match t2_do_parser empty_ctx "do { let x := 1; return x }" {

        success rem _ => String.beq rem "",

        fail _ => false

    }



@[test]

def test_t2_do_expr : Bool :=

    let empty_ctx : List Identifier := List.empty in

    match t2_do_parser empty_ctx "do { println 42; return 0 }" {

        success rem _ => String.beq rem "",

        fail _ => false

    }



@[test]

def test_t2_do_chain : Bool :=

    let empty_ctx : List Identifier := List.empty in

    match t2_do_parser empty_ctx "do { let a <- f x; let b <- g a; return b }" {

        success rem _ => String.beq rem "",

        fail _ => false

    }



@[test]

def test_t2_do_desugar_structure : Bool :=

    // Verify desugaring produces the right Term structure

    // do { return x }  →  app (var sentinel Monad.pure) x

    // But x is unbound, so it's var(sentinel, named "x")

    let empty_ctx : List Identifier := List.empty in

    match t2_do_parser empty_ctx "do { return x }" {

        success rem out =>

            match out {

                app f a => String.beq rem "",

                _ => false

            },

        fail _ => false

    }





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



// ─── Canonical literal parser (Phase 10) ───────────────────────────────



@[partial]

def t2_string_parse (input: String) : ParseResult Term :=

    match tag "\"" input {

        success rem _ =>

            match take_while is_not_quote rem {

                success rem2 content =>

                    match tag "\"" rem2 {

                        success rem3 _ => success rem3 (Term.lit (Literal.str content)),

                        fail e => fail e

                    },

                fail e => fail e

            },

        fail e => fail e

    }



def t2_num_to_term (n: I64) : Term :=

    Term.lit (Literal.num n NumSuffix.i64)



@[partial]

def t2_number_term (input: String) : ParseResult Term :=

    map_parse t2_num_to_term number input



@[partial]

def t2_literal_parser (input: String) : ParseResult Term :=

    alt_fold [t2_string_parse, t2_number_term] input



// Skip /// docstring lines (consumed as whitespace).
@[partial]
def skip_docstrings (input : String) : String :=
	skip_docstrings_try (tag "///" input) input

@[partial]
def skip_docstrings_try (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ => skip_docstrings_eol (take_while is_not_newline rem) rem,
		fail _ => orig
	}

@[partial]
def skip_docstrings_eol (r : ParseResult String) (orig : String) : String :=
	let after_eol : String := skip_spaces_match r orig in
	skip_docstrings_try_newline (tag "\n" after_eol) after_eol

@[partial]
def skip_docstrings_try_newline (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ => skip_docstrings (skip_spaces rem),
		fail _ => orig
	}

// ─── Term atom ──────────────────────────────────────────────────────────



@[partial]

def t2_atom_term (ctx: List Identifier) (input: String) : ParseResult Term :=

    t2_atom_try_var (t2_variable ctx input) ctx input



@[partial]

def t2_atom_try_var (r: ParseResult Term) (ctx: List Identifier) (input: String) : ParseResult Term :=

    match r {

        success rem out => success rem out,

        fail _ => t2_atom_try_lit ctx input

    }



@[partial]

def t2_atom_try_lit (ctx: List Identifier) (input: String) : ParseResult Term :=

    match t2_literal_parser input {

        success rem out => success rem out,

        fail _ => t2_atom_try_match ctx input

    }



// ─── Canonical match case parser (Phase 9) ─────────────────────────────



@[partial]

def t2_match_case_parser (ctx: List Identifier) (input: String) : ParseResult MatchCase :=

    t2_match_case_name (identifier (skip_spaces input)) ctx



@[partial]

def t2_match_case_name (r: ParseResult String) (ctx: List Identifier) : ParseResult MatchCase :=

    match r {

        success rem name =>

            t2_match_case_args (many0 identifier (skip_spaces rem)) (Identifier.id name) ctx,

        fail e => fail e

    }



@[partial]

def t2_match_case_args (r: ParseResult (List String)) (name: Identifier) (ctx: List Identifier) : ParseResult MatchCase :=

    match r {

        success rem _ => t2_match_case_arrow (tag "=>" (skip_spaces rem)) name ctx,

        fail e => fail e

    }



@[partial]

def t2_match_case_arrow (r: ParseResult String) (name: Identifier) (ctx: List Identifier) : ParseResult MatchCase :=

    match r {

        success rem _ => t2_match_case_body (t2_expression ctx (skip_spaces rem)) name,

        fail e => fail e

    }



@[partial]

def t2_match_case_body (r: ParseResult Term) (name: Identifier) : ParseResult MatchCase :=

    match r {

        success rem body =>

            let empty_args : List Identifier := List.empty in

            success (t2_match_case_tail rem) (MatchCase.mc name empty_args body),

        fail e => fail e

    }



@[partial]

def t2_match_case_tail (input: String) : String :=

    t2_match_case_tail_sp (take_while is_space input) input



@[partial]

def t2_match_case_tail_sp (r: ParseResult String) (orig: String) : String :=

    match r {

        success after_sp _ => t2_match_case_tail_cm (tag "," after_sp) after_sp,

        fail _ => orig

    }



@[partial]

def t2_match_case_tail_cm (r: ParseResult String) (after_sp: String) : String :=

    match r {

        success rem _ => skip_spaces rem,

        fail _ => after_sp

    }



// ─── Canonical match expression parser (Phase 9) ───────────────────────



@[partial]

def t2_match_parser (ctx: List Identifier) (input: String) : ParseResult Term :=

    t2_match_kw (tag "match" input) ctx



@[partial]

def t2_match_kw (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=

    match r {

        success rem _ => t2_match_scrutinee (t2_expression ctx (skip_spaces rem)) ctx,

        fail e => fail e

    }



@[partial]

def t2_match_scrutinee (r: ParseResult Term) (ctx: List Identifier) : ParseResult Term :=

    match r {

        success rem scrutinee => t2_match_brace_open (tag "{" (skip_spaces rem)) scrutinee ctx,

        fail e => fail e

    }



@[partial]

def t2_match_brace_open (r: ParseResult String) (scrutinee: Term) (ctx: List Identifier) : ParseResult Term :=

    match r {

        success rem _ => t2_match_cases_parse (many1 (t2_match_case_parser ctx) rem) scrutinee,

        fail e => fail e

    }



@[partial]

def t2_match_cases_parse (r: ParseResult (List MatchCase)) (scrutinee: Term) : ParseResult Term :=

    match r {

        success rem cases => t2_match_close (tag "}" (skip_spaces rem)) scrutinee cases,

        fail e => fail e

    }



@[partial]

def t2_match_close (r: ParseResult String) (scrutinee: Term) (cases: List MatchCase) : ParseResult Term :=

    match r {

        success rem _ => success rem (Term.lit (Literal.match_ scrutinee cases)),

        fail e => fail e

    }



// ─── Canonical if expression parser (Phase 9) ─────────────────────────



@[partial]

def t2_if_parser (ctx: List Identifier) (input: String) : ParseResult Term :=

    t2_if_kw (tag "if" input) ctx



@[partial]

def t2_if_kw (r: ParseResult String) (ctx: List Identifier) : ParseResult Term :=

    match r {

        success rem _ => t2_if_cond (t2_expression ctx (skip_spaces rem)) ctx,

        fail e => fail e

    }



@[partial]

def t2_if_cond (r: ParseResult Term) (ctx: List Identifier) : ParseResult Term :=

    match r {

        success rem cond => t2_if_then_kw (tag "then" (skip_spaces rem)) cond ctx,

        fail e => fail e

    }



@[partial]

def t2_if_then_kw (r: ParseResult String) (cond: Term) (ctx: List Identifier) : ParseResult Term :=

    match r {

        success rem _ => t2_if_then_branch (t2_expression ctx (skip_spaces rem)) cond ctx,

        fail e => fail e

    }



@[partial]

def t2_if_then_branch (r: ParseResult Term) (cond: Term) (ctx: List Identifier) : ParseResult Term :=

    match r {

        success rem then_b => t2_if_else_kw (tag "else" (skip_spaces rem)) cond then_b ctx,

        fail e => fail e

    }



@[partial]

def t2_if_else_kw (r: ParseResult String) (cond: Term) (then_b: Term) (ctx: List Identifier) : ParseResult Term :=

    match r {

        success rem _ => t2_if_else_branch (t2_expression ctx (skip_spaces rem)) cond then_b,

        fail e => fail e

    }



@[partial]

def t2_if_else_branch (r: ParseResult Term) (cond: Term) (then_b: Term) : ParseResult Term :=

    match r {

        success rem else_b => success rem (Term.lit (Literal.if_ cond then_b else_b)),

        fail e => fail e

    }



@[partial]

def t2_atom_try_match (ctx: List Identifier) (input: String) : ParseResult Term :=

    match t2_match_parser ctx input {

        success rem out => success rem out,

        fail _ => t2_atom_try_if ctx input

    }



@[partial]

def t2_atom_try_if (ctx: List Identifier) (input: String) : ParseResult Term :=

    match t2_if_parser ctx input {

        success rem out => success rem out,

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



// ─── Phase 1.5: docstring and implicit params tests ───────────────────────────────

@[test]
def test_skip_docstrings_none : Bool :=
	let rem : String := skip_docstrings "use prelude" in
	String.beq rem "use prelude"

@[test]
def test_skip_docstrings_one : Bool :=
	let rem : String := skip_docstrings "/// doc\nuse prelude" in
	String.beq rem "use prelude"

@[test]
def test_skip_docstrings_multi : Bool :=
	let rem : String := skip_docstrings "/// line1\n/// line2\n\ndef x := 1" in
	String.beq rem "def x := 1"

@[test]
def test_t2_decls_with_docstring : Bool :=
	match t2_decls_parser "/// A test declaration\ndef x : I64 := 42" {
		success rem decls =>
			let rem_stripped : String := skip_spaces rem in
			String.beq rem_stripped "" && I64.beq (debug_decl_count decls) 1,
		fail _ => false
	}

@[test]
def test_t2_type_implicit_params : Bool :=
	match t2_type_parser "type Any { any {A : Type} (value : A) }" {
		success rem decl => String.beq rem "",
		fail _ => false
	}

@[test]
def test_t2_type_implicit_no_parens : Bool :=
	match t2_type_parser "type All { mk {A : Type} (val : A) }" {
		success rem decl => String.beq rem "",
		fail _ => false
	}

// --- TypeConstraint parsing tests ---

@[test]
def test_type_constraint_one_simple : Bool :=
	match t2_type_constraint_one "Functor F" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_constraint_one_two_vars : Bool :=
	match t2_type_constraint_one "HAdd A A A" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_constraint_one_no_vars : Bool :=
	match t2_type_constraint_one "Show" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_constraint_list_single : Bool :=
	match t2_type_constraint_list "Functor F" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_constraint_list_multi : Bool :=
	match t2_type_constraint_list "Functor F, Applicative M" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

@[test]
def test_type_constraint_list_empty : Bool :=
	match t2_type_constraint_list "" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

@[test]
def test_class_with_constraints : Bool :=
	match t2_class_parser "class [Functor F] Applicative F { def pure (a : A) : F A }" {
		success rem _ => String.beq rem "",
		fail _ => false
	}

@[test]
def test_instance_with_constraints : Bool :=
	match t2_instance_parser "instance [Show A] Show A { def m := a }" {
		success rem _ => String.beq rem "",
		fail _ => false
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





@[test]

def test_t2_match_simple : Bool :=

    let empty_ctx : List Identifier := List.empty in

    match t2_match_parser empty_ctx "match x { some a => a, none => 0 }" {

        success rem out =>

            match out {

                lit val =>

                    match val {

                        match_ scrutinee cases => String.beq rem "",

                        _ => false

                    },

                _ => false

            },

        fail _ => false

    }



@[test]

def test_t2_match_multi : Bool :=

    let empty_ctx : List Identifier := List.empty in

    match t2_match_parser empty_ctx "match x { zero => 0, one => 1 }" {

        success rem out =>

            match out {

                lit val =>

                    match val {

                        match_ scrutinee cases => String.beq rem "",

                        _ => false

                    },

                _ => false

            },

        fail _ => false

    }



@[test]

def test_t2_if_simple : Bool :=

    let empty_ctx : List Identifier := List.empty in

    match t2_if_parser empty_ctx "if true then 1 else 2" {

        success rem out =>

            match out {

                lit val =>

                    match val {

                        if_ cond then_b else_b => String.beq rem "",

                        _ => false

                    },

                _ => false

            },

        fail _ => false

    }



@[test]

def test_t2_if_nested : Bool :=

    let empty_ctx : List Identifier := List.empty in

    match t2_if_parser empty_ctx "if a then if b then 1 else 2 else 3" {

        success rem out =>

            match out {

                lit val =>

                    match val {

                        if_ cond then_b else_b => String.beq rem "",

                        _ => false

                    },

                _ => false

            },

        fail _ => false

    }



@[test]

def test_t2_if_bound_var : Bool :=

    let x : Identifier := Identifier.id "x" in

    let ctx : List Identifier := List.cons x List.empty in

    match t2_if_parser ctx "if x then 1 else x" {

        success rem out =>

            match out {

                lit val =>

                    match val {

                        if_ cond then_b else_b =>

                            String.beq rem "",

                        _ => false

                    },

                _ => false

            },

        fail _ => false

    }



@[test]

def test_t2_match_bound_var : Bool :=

    let x : Identifier := Identifier.id "x" in

    let ctx : List Identifier := List.cons x List.empty in

    match t2_match_parser ctx "match x { none => 0 }" {

        success rem out =>

            match out {

                lit val =>

                    match val {

                        match_ scrutinee cases =>

                            String.beq rem "",

                        _ => false

                    },

                _ => false

            },

        fail _ => false

    }



// ─── Canonical decl parser smoke tests (Phase 8) ─────────────────────



@[test]

def test_t2_use_parser : Bool :=

    match t2_use_parser "use prelude" {

        success rem out =>

            match out {

                use_d path => String.beq rem "",

                _ => false

            },

        fail _ => false

    }



@[test]

def test_t2_open_parser : Bool :=

    match t2_open_parser "open IO" {

        success rem out =>

            match out {

                open_d path => String.beq rem "",

                _ => false

            },

        fail _ => false

    }



@[test]

def test_t2_infix_parser : Bool :=

    match t2_infix_parser "infix (++) := List.append" {

        success rem out =>

            match out {

                infix_d op path => String.beq rem "",

                _ => false

            },

        fail _ => false

    }



@[test]

def test_t2_struct_parser : Bool :=

    match t2_struct_parser "struct Point { x : I64, y : I64 }" {

        success rem out =>

            match out {

                struct_d s => String.beq rem "",

                _ => false

            },

        fail _ => false

    }



@[test]

def test_t2_def_parser : Bool :=

    match t2_def_parser "@[test] def f (x : I64) : I64 := x" {

        success rem out =>

            match out {

                def_d d => String.beq rem "",

                _ => false

            },

        fail _ => false

    }



@[test]

def test_t2_def_do_block : Bool :=

    match t2_def_parser "def main : Unit { return 0 }" {

        success rem out =>

            match out {

                def_d d => String.beq rem "",

                _ => false

            },

        fail _ => false

    }



@[test]

def test_t2_class_parser : Bool :=

    match t2_class_parser "class Show A { def show (a : A) : String }" {

        success rem out =>

            match out {

                class_d c => String.beq rem "",

                _ => false

            },

        fail _ => false

    }



@[test]

def test_t2_instance_parser : Bool :=

    match t2_instance_parser "instance Functor Maybe { def map f m := match m { some a => a, none => none } }" {

        success rem out =>

            match out {

                instance_d i => String.beq rem "",

                _ => false

            },

        fail _ => false

    }



@[test]

def test_t2_decl_parser_def : Bool :=

    match t2_decl_parser "def add (a: I64) (b: I64) : I64 := a + b" {

        success rem out =>

            match out {

                def_d d => String.beq rem "",

                _ => false

            },

        fail _ => false

    }



@[test]

def test_t2_decl_parser_fail : Bool :=

    match t2_decl_parser "foobar" {

        success rem out => false,

        fail _ => true

    }






// ─── AST debug helpers ───────────────────────────────────────────────────



@[partial]
def debug_decl_kind (d : Decl) : String :=
    match d {
        use_d _ => "use_d",
        open_d _ => "open_d",
        def_d _ => "def_d",
        infix_d _ _ => "infix_d",

        struct_d _ => "struct_d",
        class_d _ => "class_d",
        instance_d _ => "instance_d"
    }

@[partial]
def debug_decl_count (decls : List Decl) : I64 :=
    match decls {
        List.empty => 0,
        List.cons d rest => 1 + debug_decl_count rest
    }

// ─── Multi-declaration parser tests ──────────────────────────────────────────────────────



@[test]
def test_t2_decls_empty : Bool :=
    match t2_decls_parser "" {
        success rem decls =>
            String.beq rem "" && match decls {
                List.empty => true,
                List.cons _ _ => false
            },
        fail _ => false
    }

@[test]
def test_t2_decls_whitespace_only : Bool :=
    match t2_decls_parser "  " {
        success rem decls =>
            String.beq rem "" && match decls {
                List.empty => true,
                List.cons _ _ => false
            },
        fail _ => false
    }

@[test]
def test_t2_decls_one_use : Bool :=
    match t2_decls_parser "use prelude" {
        success rem decls => String.beq rem "",
        fail _ => false
    }

@[test]
def test_t2_decls_two_parsed : Bool :=
    match t2_decls_parser "use prelude open IO" {
        success rem decls => String.beq rem "",
        fail _ => false
    }

@[test]
def test_t2_decls_def : Bool :=
    match t2_decls_parser "def x : I64 := 42" {
        success rem decls => String.beq rem "",
        fail _ => false
    }

@[test]
def test_t2_decls_decl_plus_noise : Bool :=
    match t2_decls_parser "use prelude  garbage" {
        success rem decls => true,
        fail _ => false
    }


@[test]
def test_t2_decls_count_two : Bool :=
    match t2_decls_parser "use prelude open IO" {
        success rem decls =>
            String.beq rem "" && I64.beq (debug_decl_count decls) 2,
        fail _ => false
    }

@[test]
def test_t2_decls_count_one : Bool :=
    match t2_decls_parser "def x : I64 := 1" {
        success rem decls =>
            String.beq rem "" && I64.beq (debug_decl_count decls) 1,
        fail _ => false
    }

@[test]
def test_t2_decls_kind_use : Bool :=
    match t2_decls_parser "use prelude" {
        success rem decls =>
            match decls {
                List.cons d rest =>
                    match rest { List.empty => String.beq rem "", List.cons _ _ => false },
                List.empty => false
            },
        fail _ => false
    }


@[test]
def test_t2_decls_type_decl : Bool :=
    match t2_decls_parser "type Maybe A { some (a : A), none }" {
        success rem decls => String.beq rem "",
        fail _ => false
    }

@[test]
def test_t2_decls_class : Bool :=
    match t2_decls_parser "class Show A { def show (a : A) : String }" {
        success rem decls => String.beq rem "",
        fail _ => false
    }

@[test]
def test_t2_decls_struct : Bool :=
    match t2_decls_parser "struct Point { x : I64, y : I64 }" {
        success rem decls => String.beq rem "",
        fail _ => false
    }

@[test]
def test_t2_decls_mixed : Bool :=
    match t2_decls_parser "use prelude  open IO  def main : I64 := 42" {
        success rem decls =>
            String.beq rem "" && I64.beq (debug_decl_count decls) 3,
        fail _ => false
    }
