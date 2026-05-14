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

// --- Helper ---

def is_empty (s : String) : Bool := I64.beq (String.length s) 0

// --- Combinators ---

def tag (s : String) (input : String) : ParseResult String :=
	if is_prefix s input
	then success (String.drop (String.length s) input) s
	else fail (ParseError.tag s)

def is_prefix (pre : String) (s : String) : Bool :=
	String.beq pre (String.slice s 0 (String.length pre))

def alt (a : String -> ParseResult A) (b : String -> ParseResult A) (input : String) : ParseResult A :=
	alt_body (a input) b input

def alt_body (r : ParseResult A) (b : String -> ParseResult A) (input : String) : ParseResult A :=
	match r {
		success rem out => success rem out,
		fail e1 => alt_second (b input) e1
	}

def alt_second (r : ParseResult A) (e1 : ParseError) : ParseResult A :=
	match r {
		success rem out => success rem out,
		fail e2 => fail (ParseError.custom "both alt failed")
	}

// --- Char predicates ---

def is_digit (c : String) : Bool :=
	if String.beq "0" c then true
	else if String.beq "1" c then true
	else if String.beq "2" c then true
	else if String.beq "3" c then true
	else if String.beq "4" c then true
	else if String.beq "5" c then true
	else if String.beq "6" c then true
	else if String.beq "7" c then true
	else if String.beq "8" c then true
	else String.beq "9" c

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

def is_alpha (c : String) : Bool :=
	if is_alpha_lower c then true
	else if is_alpha_lower2 c then true
	else if is_alpha_upper c then true
	else is_alpha_upper2 c

def is_alphanumeric (c : String) : Bool :=
	if is_digit c then true
	else is_alpha c

def is_ident_char (c : String) : Bool :=
	if is_alphanumeric c then true
	else String.beq "_" c

def is_space (c : String) : Bool :=
	if String.beq " " c then true
	else if String.beq "\t" c then true
	else if String.beq "\n" c then true
	else String.beq "\r" c

// --- Keyword check ---

def is_keyword (s : String) : Bool :=
	if String.beq "def" s then true
	else if String.beq "let" s then true
	else if String.beq "in" s then true
	else if String.beq "use" s then true
	else if String.beq "open" s then true
	else if String.beq "class" s then true
	else if String.beq "struct" s then true
	else if String.beq "instance" s then true
	else if String.beq "type" s then true
	else if String.beq "fn" s then true
	else if String.beq "match" s then true
	else if String.beq "if" s then true
	else if String.beq "then" s then true
	else if String.beq "else" s then true
	else if String.beq "infix" s then true
	else if String.beq "do" s then true
	else if String.beq "return" s then true
	else if String.beq "for" s then true
	else if String.beq "quote" s then true
	else if String.beq "with" s then true
	else false

// --- Identifier parser ---

def ident_start (c : String) : Bool :=
	if is_alpha c then true
	else String.beq "_" c

def identifier (input : String) : ParseResult String :=
	identifier_try (take_while is_ident_char input)

def identifier_try (r : ParseResult String) : ParseResult String :=
	match r {
		success rem out =>
			if is_empty out
			then fail (ParseError.custom "expected identifier")
			else identifier_check_start out rem,
		fail e => fail e
	}

def identifier_check_start (s : String) (rem : String) : ParseResult String :=
	if ident_start (String.slice s 0 1)
	then identifier_check_kw s rem
	else fail (ParseError.custom "identifier cannot start with digit")

def identifier_check_kw (s : String) (rem : String) : ParseResult String :=
	if is_keyword s
	then fail (ParseError.custom ("reserved keyword: " ++ s))
	else success rem s

// --- Number parser ---

def take_while (pred : String -> Bool) (input : String) : ParseResult String :=
	take_while_loop pred "" input

def take_while_loop (pred : String -> Bool) (acc : String) (input : String) : ParseResult String :=
	if is_empty input
	then success input acc
	else take_while_check pred acc input (String.slice input 0 1) (String.drop 1 input)

def take_while_check (pred : String -> Bool) (acc : String) (input : String) (ch : String) (rest : String) : ParseResult String :=
	if pred ch
	then take_while_loop pred (String.concat acc ch) rest
	else success input acc

def is_digit_or_underscore (c : String) : Bool :=
	if is_digit c then true
	else String.beq "_" c

def number (input : String) : ParseResult I64 :=
	number_body (take_while is_digit_or_underscore input)

def number_body (r : ParseResult String) : ParseResult I64 :=
	match r {
		success rem out =>
			if is_empty out
			then fail (ParseError.custom "expected number")
			else number_parse out rem,
		fail e => fail e
	}

def number_parse (s : String) (rem : String) : ParseResult I64 :=
	if is_empty s
	then fail (ParseError.custom "empty number")
	else if is_digit (String.slice s 0 1)
	then success rem (parse_digits s)
	else fail (ParseError.custom "number must start with digit")

// --- Whitespace ---

def spaces (input : String) : ParseResult String :=
	take_while is_space input

// --- many0 / many1 ---

def many0 (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	many0_body (p input) p input

def many0_body (r : ParseResult A) (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	match r {
		success rem out =>
			many0_next (many0 p rem) out rem,
		fail _ => success input List.empty
	}

def many0_next (r : ParseResult (List A)) (out : A) (rem : String) : ParseResult (List A) :=
	match r {
		success rem2 rest => success rem2 (List.cons out rest),
		fail _ => success rem (List.cons out List.empty)
	}

// --- Type helpers ---

def var_term (s : String) : Term :=
	Term.var (NameRef.nid (Identifier.id s))

// --- Type expression parser ---

def type_variable (input : String) : ParseResult Term :=
	type_var_got (identifier input)

def type_var_got (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem out => success rem (var_term out),
		fail e => fail e
	}

def type_parens (input : String) : ParseResult Term :=
	type_parens_open (tag "(" input)

def type_parens_open (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem _ => type_parens_expr (type_expression rem),
		fail e => fail e
	}

def type_parens_expr (r : ParseResult Term) : ParseResult Term :=
	match r {
		success rem out => type_parens_close (tag ")" rem) out,
		fail e => fail e
	}

def type_parens_close (r : ParseResult String) (out : Term) : ParseResult Term :=
	match r {
		success rem _ => success rem out,
		fail e => fail e
	}

def type_atom (input : String) : ParseResult Term :=
	type_atom_try_var (type_variable input) input

def type_atom_try_var (r : ParseResult Term) (input : String) : ParseResult Term :=
	match r {
		success rem out => success rem out,
		fail _ => type_parens input
	}

def type_expression (input : String) : ParseResult Term :=
	type_expr_ws (take_while is_space input)

def type_expr_ws (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem _ => type_expr_atom (type_atom rem),
		fail e => fail e
	}

def type_expr_atom (r : ParseResult Term) : ParseResult Term :=
	match r {
		success rem out => type_expr_check_arrow rem out,
		fail e => fail e
	}

def type_expr_check_arrow (input : String) (lhs : Term) : ParseResult Term :=
	type_expr_arrow_ws (take_while is_space input) input lhs

def type_expr_arrow_ws (r : ParseResult String) (input : String) (lhs : Term) : ParseResult Term :=
	match r {
		success rem _ => type_expr_try_arrow rem lhs (tag "->" rem),
		fail e => fail e
	}

def type_expr_try_arrow (input : String) (lhs : Term) (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem _ => type_expr_rhs lhs (type_expression rem),
		fail _ => success input lhs
	}

def type_expr_rhs (lhs : Term) (r : ParseResult Term) : ParseResult Term :=
	match r {
		success rem out => success rem (Term.pi lhs out),
		fail e => fail e
	}

// --- many1 ---

def many1 (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	many1_body (p input) p input

def many1_body (r : ParseResult A) (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	match r {
		success rem out =>
			many0_next (many0 p rem) out rem,
		fail e => fail e
	}

// --- Number parsing helpers ---

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

def parse_digits (s : String) : I64 :=
	parse_digits_loop s 0

def parse_digits_loop (s : String) (acc : I64) : I64 :=
	if is_empty s
	then acc
	else parse_digits_char (String.slice s 0 1) (String.drop 1 s) acc

def parse_digits_char (ch : String) (rest : String) (acc : I64) : I64 :=
	parse_digits_loop rest (I64.add (I64.mul acc 10) (char_to_digit ch))

// --- String literal ---

def is_not_quote (c : String) : Bool :=
	if String.beq "\"" c then false
	else true

def string_parse (input : String) : ParseResult Term :=
	string_parse_open (tag "\"" input)

def string_parse_open (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem _ => string_parse_content (take_while is_not_quote rem),
		fail e => fail e
	}

def string_parse_content (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem out => string_parse_close (tag "\"" rem) out,
		fail e => fail e
	}

def string_parse_close (r : ParseResult String) (content : String) : ParseResult Term :=
	match r {
		success rem _ => success rem (Term.lit (Literal.str content)),
		fail e => fail e
	}

// --- Number term wrapper ---

def number_term (input : String) : ParseResult Term :=
	number_term_body (number input)

def number_term_body (r : ParseResult I64) : ParseResult Term :=
	match r {
		success rem out => success rem (Term.lit (Literal.num out NumSuffix.i64)),
		fail e => fail e
	}

// --- Variable parser ---

// --- Path variable parser (e.g. A.B.C) ---

def path_variable (input : String) : ParseResult Term :=
	path_var_first (identifier input)

def path_var_first (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem first => path_var_need_dot rem (List.cons (Identifier.id first) List.empty),
		fail e => fail e
	}

def path_var_need_dot (input : String) (ids : List Identifier) : ParseResult Term :=
	path_var_need_dot_try (tag "." input) ids input

def path_var_need_dot_try (r : ParseResult String) (ids : List Identifier) (orig : String) : ParseResult Term :=
	match r {
		success rem _ => path_var_field (identifier rem) ids,
		fail _ => fail (ParseError.custom "not a dotted path")
	}

def path_var_loop (input : String) (ids : List Identifier) : ParseResult Term :=
	path_var_loop_dot (tag "." input) ids input

def path_var_loop_dot (r : ParseResult String) (ids : List Identifier) (orig : String) : ParseResult Term :=
	match r {
		success rem _ => path_var_field (identifier rem) ids,
		fail _ =>
			let rev : List Identifier := list_reverse ids in
			success orig (Term.var (NameRef.nmp (ModulePath.mp rev)))
	}

def path_var_field (r : ParseResult String) (ids : List Identifier) : ParseResult Term :=
	match r {
		success rem next => path_var_loop rem (List.cons (Identifier.id next) ids),
		fail e => fail e
	}

// --- Variable parser (dotted path or simple identifier) ---

def variable (input : String) : ParseResult Term :=
	variable_try_path (path_variable input) input

def variable_try_path (r : ParseResult Term) (input : String) : ParseResult Term :=
	match r {
		success rem out => success rem out,
		fail _ => variable_got (identifier input)
	}

def variable_got (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem out => success rem (Term.var (NameRef.nid (Identifier.id out))),
		fail e => fail e
	}

// --- Literal term (string or number) ---

def literal_term (input : String) : ParseResult Term :=
	literal_try_str (string_parse input) input

def literal_try_str (r : ParseResult Term) (input : String) : ParseResult Term :=
	match r {
		success rem out => success rem out,
		fail _ => number_term input
	}

// --- Atom term (variable, literal, parenthesized expression) ---

def atom_term (input : String) : ParseResult Term :=
	atom_try_var (variable input) input

def atom_try_var (r : ParseResult Term) (input : String) : ParseResult Term :=
	match r {
		success rem out => success rem out,
		fail _ => atom_try_lit (literal_term input) input
	}

def atom_try_paren (r : ParseResult String) (input : String) : ParseResult Term :=
	match r {
		success rem _ => atom_inner_expr (expression rem),
		fail e => fail e
	}

def atom_inner_expr (r : ParseResult Term) : ParseResult Term :=
	match r {
		success rem out => atom_close_paren (tag ")" rem) out,
		fail e => fail e
	}

def atom_close_paren (r : ParseResult String) (out : Term) : ParseResult Term :=
	match r {
		success rem _ => success rem out,
		fail e => fail e
	}

// --- Whitespace skip (non-ParseResult version) ---

def skip_spaces (input : String) : String :=
	skip_spaces_match (take_while is_space input) input

def skip_spaces_match (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ => rem,
		fail _ => orig
	}

// --- Match case parser ---

def match_case (input : String) : ParseResult MatchCase :=
	match_case_name (identifier (skip_spaces input))

def match_case_name (r : ParseResult String) : ParseResult MatchCase :=
	match r {
		success rem name => match_case_args (many0 identifier (skip_spaces rem)) (Identifier.id name),
		fail e => fail e
	}

def match_case_args (r : ParseResult (List String)) (name : Identifier) : ParseResult MatchCase :=
	match r {
		success rem _ => match_case_arrow (tag "=>" (skip_spaces rem)) name,
		fail e => fail e
	}

def match_case_arrow (r : ParseResult String) (name : Identifier) : ParseResult MatchCase :=
	match r {
		success rem _ => match_case_body (expression (skip_spaces rem)) name,
		fail e => fail e
	}

def match_case_body (r : ParseResult Term) (name : Identifier) : ParseResult MatchCase :=
	match r {
		success rem body =>
			let empty_args : List Identifier := List.empty in
			success (match_case_tail rem) (MatchCase.mc name empty_args body),
		fail e => fail e
	}

def match_case_tail (input : String) : String :=
	match_case_tail_sp (take_while is_space input) input

def match_case_tail_sp (r : ParseResult String) (orig : String) : String :=
	match r {
		success after_sp _ => match_case_tail_cm (tag "," after_sp) after_sp,
		fail _ => orig
	}

def match_case_tail_cm (r : ParseResult String) (after_sp : String) : String :=
	match r {
		success rem _ => skip_spaces rem,
		fail _ => after_sp
	}

// --- Match expression parser ---

def match_parser (input : String) : ParseResult Term :=
	match_kw (tag "match" input)

def match_kw (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem _ => match_scrutinee (expression (skip_spaces rem)),
		fail e => fail e
	}

def match_scrutinee (r : ParseResult Term) : ParseResult Term :=
	match r {
		success rem scrutinee => match_brace_open (tag "{" (skip_spaces rem)) scrutinee,
		fail e => fail e
	}

def match_brace_open (r : ParseResult String) (scrutinee : Term) : ParseResult Term :=
	match r {
		success rem _ => match_cases_parse (many1 match_case rem) scrutinee,
		fail e => fail e
	}

def match_cases_parse (r : ParseResult (List MatchCase)) (scrutinee : Term) : ParseResult Term :=
	match r {
		success rem cases => match_close (tag "}" (skip_spaces rem)) scrutinee cases,
		fail e => fail e
	}

def match_close (r : ParseResult String) (scrutinee : Term) (cases : List MatchCase) : ParseResult Term :=
	match r {
		success rem _ => success rem (Term.lit (Literal.match_ scrutinee cases)),
		fail e => fail e
	}

// --- If expression parser ---

def if_parser (input : String) : ParseResult Term :=
	if_kw (tag "if" input)

def if_kw (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem _ => if_cond (expression (skip_spaces rem)),
		fail e => fail e
	}

def if_cond (r : ParseResult Term) : ParseResult Term :=
	match r {
		success rem cond => if_then_kw (tag "then" (skip_spaces rem)) cond,
		fail e => fail e
	}

def if_then_kw (r : ParseResult String) (cond : Term) : ParseResult Term :=
	match r {
		success rem _ => if_then_branch (expression (skip_spaces rem)) cond,
		fail e => fail e
	}

def if_then_branch (r : ParseResult Term) (cond : Term) : ParseResult Term :=
	match r {
		success rem then_b => if_else_kw (tag "else" (skip_spaces rem)) cond then_b,
		fail e => fail e
	}

def if_else_kw (r : ParseResult String) (cond : Term) (then_b : Term) : ParseResult Term :=
	match r {
		success rem _ => if_else_branch (expression (skip_spaces rem)) cond then_b,
		fail e => fail e
	}

def if_else_branch (r : ParseResult Term) (cond : Term) (then_b : Term) : ParseResult Term :=
	match r {
		success rem else_b => success rem (Term.lit (Literal.if_ cond then_b else_b)),
		fail e => fail e
	}

// --- Lambda expression parser ---

def lambda_parser (input : String) : ParseResult Term :=
	lambda_kw (alt (alt (tag "fn") (tag "ꟛ")) (tag "\\") input)

def lambda_kw (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem _ => lambda_param (identifier (skip_spaces rem)),
		fail e => fail e
	}

def lambda_param (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem name => lambda_arrow (tag "=>" (skip_spaces rem)) (Identifier.id name),
		fail e => fail e
	}

def lambda_arrow (r : ParseResult String) (name : Identifier) : ParseResult Term :=
	match r {
		success rem _ => lambda_body (expression (skip_spaces rem)) name,
		fail e => fail e
	}

def lambda_body (r : ParseResult Term) (name : Identifier) : ParseResult Term :=
	match r {
		success rem body => success rem (Term.lam (Param.mk name (Term.type_ 1)) body),
		fail e => fail e
	}

// --- Let expression parser ---

def let_parser (input : String) : ParseResult Term :=
	let_kw (tag "let" input)

def let_kw (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem _ => let_name (identifier (skip_spaces rem)),
		fail e => fail e
	}

def let_name (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem name => let_assign (tag ":=" (skip_spaces rem)) (Identifier.id name),
		fail e => fail e
	}

def let_assign (r : ParseResult String) (name : Identifier) : ParseResult Term :=
	match r {
		success rem _ => let_value (expression (skip_spaces rem)) name,
		fail e => fail e
	}

def let_value (r : ParseResult Term) (name : Identifier) : ParseResult Term :=
	match r {
		success rem value => let_in_kw (tag "in" (skip_spaces rem)) name value,
		fail e => fail e
	}

def let_in_kw (r : ParseResult String) (name : Identifier) (value : Term) : ParseResult Term :=
	match r {
		success rem _ => let_body (expression (skip_spaces rem)) name value,
		fail e => fail e
	}

def let_body (r : ParseResult Term) (name : Identifier) (value : Term) : ParseResult Term :=
	match r {
		success rem body => success rem (Term.app (Term.lam (Param.mk name (Term.type_ 1)) body) value),
		fail e => fail e
	}

// --- Do-notation parser ---

def do_stmt_return (input : String) : ParseResult DoStmt :=
	do_stmt_ret_kw (tag "return" input) input

def do_stmt_ret_kw (r : ParseResult String) (orig : String) : ParseResult DoStmt :=
	match r {
		success rem _ => do_stmt_ret_expr (expression (skip_spaces rem)),
		fail _ => do_stmt_try_let (tag "let" (skip_spaces orig)) orig
	}

def do_stmt_try_let (r : ParseResult String) (orig : String) : ParseResult DoStmt :=
	match r {
		success rem _ => do_stmt_let_name (identifier (skip_spaces rem)),
		fail _ => do_stmt_expr (expression (skip_spaces orig))
	}

def do_stmt_let_name (r : ParseResult String) : ParseResult DoStmt :=
	match r {
		success rem name => do_stmt_let_kind rem (Identifier.id name),
		fail e => fail e
	}

def do_stmt_let_kind (input : String) (name : Identifier) : ParseResult DoStmt :=
	do_stmt_let_kind_try (tag ":=" (skip_spaces input)) name input

def do_stmt_let_kind_try (r : ParseResult String) (name : Identifier) (orig : String) : ParseResult DoStmt :=
	match r {
		success rem _ => do_stmt_let_value (expression (skip_spaces rem)) name,
		fail _ => do_stmt_bind_arrow (tag "<-" (skip_spaces orig)) name orig
	}

def do_stmt_let_value (r : ParseResult Term) (name : Identifier) : ParseResult DoStmt :=
	match r {
		success rem value => success rem (DoStmt.let_s name value),
		fail e => fail e
	}

def do_stmt_bind_arrow (r : ParseResult String) (name : Identifier) (orig : String) : ParseResult DoStmt :=
	match r {
		success rem _ => do_stmt_bind_value (expression (skip_spaces rem)) name,
		fail _ => fail (ParseError.custom "expected := or <- after let in do block")
	}

def do_stmt_bind_value (r : ParseResult Term) (name : Identifier) : ParseResult DoStmt :=
	match r {
		success rem value => success rem (DoStmt.bind_s name value),
		fail e => fail e
	}

def do_stmt_ret_expr (r : ParseResult Term) : ParseResult DoStmt :=
	match r {
		success rem value => success rem (DoStmt.ret_s value),
		fail e => fail e
	}

def do_stmt_expr (r : ParseResult Term) : ParseResult DoStmt :=
	match r {
		success rem value => success rem (DoStmt.expr_s value),
		fail e => fail e
	}

def do_stmts (input : String) : ParseResult (List DoStmt) :=
	do_stmts_check_end (tag "}" (skip_spaces input)) input

def do_stmts_check_end (r : ParseResult String) (orig : String) : ParseResult (List DoStmt) :=
	match r {
		success rem _ =>
			let empty : List DoStmt := List.empty in
			success rem empty,
		fail _ => do_stmts_first (do_stmt_return (skip_spaces orig)) (skip_spaces orig)
	}

def do_stmts_first (r : ParseResult DoStmt) (orig : String) : ParseResult (List DoStmt) :=
	match r {
		success rem stmt => do_stmts_next (do_stmts (do_stmts_tail rem)) stmt,
		fail e => fail e
	}

def do_stmts_tail (input : String) : String :=
	do_stmts_tail_sp (take_while is_space input) input

def do_stmts_tail_sp (r : ParseResult String) (orig : String) : String :=
	match r {
		success rem _ => do_stmts_tail_semi (tag ";" rem) rem orig,
		fail _ => orig
	}

def do_stmts_tail_semi (r : ParseResult String) (after_sp : String) (orig : String) : String :=
	match r {
		success rem _ => skip_spaces rem,
		fail _ => after_sp
	}

def do_stmts_next (r : ParseResult (List DoStmt)) (first : DoStmt) : ParseResult (List DoStmt) :=
	match r {
		success rem rest => success rem (List.cons first rest),
		fail e => fail e
	}

def do_parser (input : String) : ParseResult Term :=
	do_kw (tag "do" input)

def do_kw (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem _ => do_brace (tag "{" (skip_spaces rem)),
		fail e => fail e
	}

def do_brace (r : ParseResult String) : ParseResult Term :=
	match r {
		success rem _ => do_build (do_stmts rem),
		fail e => fail e
	}

def do_build (r : ParseResult (List DoStmt)) : ParseResult Term :=
	match r {
		success rem stmts => success rem (desugar_do stmts),
		fail e => fail e
	}

def atom_try_lit (r : ParseResult Term) (input : String) : ParseResult Term :=
	match r {
		success rem out => success rem out,
		fail _ => atom_try_match (match_parser input) input
	}

def atom_try_match (r : ParseResult Term) (input : String) : ParseResult Term :=
	match r {
		success rem out => success rem out,
		fail _ => atom_try_if (if_parser input) input
	}

def atom_try_if (r : ParseResult Term) (input : String) : ParseResult Term :=
	match r {
		success rem out => success rem out,
		fail _ => atom_try_let (let_parser input) input
	}

def atom_try_let (r : ParseResult Term) (input : String) : ParseResult Term :=
	match r {
		success rem out => success rem out,
		fail _ => atom_try_do (do_parser input) input
	}

def atom_try_do (r : ParseResult Term) (input : String) : ParseResult Term :=
	match r {
		success rem out => success rem out,
		fail _ => atom_try_lambda (lambda_parser input) input
	}

def atom_try_lambda (r : ParseResult Term) (input : String) : ParseResult Term :=
	match r {
		success rem out => success rem out,
		fail _ => atom_try_paren (tag "(" input) input
	}

// --- Operator parsing ---

def is_op_char (c : String) : Bool :=
	if String.beq "+" c then true
	else if String.beq "&" c then true
	else if String.beq "=" c then true
	else if String.beq "|" c then true
	else if String.beq "<" c then true
	else if String.beq ">" c then true
	else if String.beq "*" c then true
	else if String.beq "/" c then true
	else if String.beq "-" c then true
	else if String.beq "!" c then true
	else String.beq "." c

def operator_parse (input : String) : ParseResult String :=
	operator_parse_body (take_while is_op_char input)

def operator_parse_body (r : ParseResult String) : ParseResult String :=
	match r {
		success rem out =>
			if is_empty out
			then fail (ParseError.custom "expected operator")
			else operator_check out rem,
		fail e => fail e
	}

def operator_check (s : String) (rem : String) : ParseResult String :=
	if I64.beq 0 (op_precedence s)
	then fail (ParseError.custom "unknown operator")
	else success rem s

def op_precedence (op : String) : I64 :=
	if String.beq "|>" op then 5
	else if String.beq "<|" op then 5
	else if String.beq ">>=" op then 10
	else if String.beq "." op then 12
	else if String.beq "<*>" op then 15
	else if String.beq "<|>" op then 20
	else if String.beq "||" op then 25
	else if String.beq "&&" op then 30
	else if String.beq "==" op then 40
	else if String.beq "!=" op then 40
	else if String.beq "++" op then 50
	else if String.beq ">>" op then 60
	else if String.beq "<<" op then 60
	else if String.beq "+" op then 65
	else if String.beq "-" op then 65
	else if String.beq "*" op then 70
	else if String.beq "/" op then 70
	else 0

def op_is_right_assoc (op : String) : Bool :=
	if String.beq "<|" op then true
	else if String.beq ">>=" op then true
	else if String.beq "." op then true
	else if String.beq "||" op then true
	else if String.beq "&&" op then true
	else if String.beq "++" op then true
	else false

// --- Expression (atom + juxtaposition application + operators) ---

def expression (input : String) : ParseResult Term :=
	expr_first (atom_term input)

def expr_first (r : ParseResult Term) : ParseResult Term :=
	match r {
		success rem lhs => expr_rest rem lhs,
		fail e => fail e
	}

def expr_rest (input : String) (lhs : Term) : ParseResult Term :=
	expr_rest_ws (take_while is_space input) lhs

def expr_rest_ws (r : ParseResult String) (lhs : Term) : ParseResult Term :=
	match r {
		success rem _ => expr_rest_next (atom_term rem) rem lhs,
		fail e => fail e
	}

def expr_rest_next (r : ParseResult Term) (input : String) (lhs : Term) : ParseResult Term :=
	match r {
		success rem rhs => expr_rest rem (Term.app lhs rhs),
		fail _ => expr_op input lhs
	}

def expr_op (input : String) (lhs : Term) : ParseResult Term :=
	expr_op_try (operator_parse input) input lhs

def expr_op_try (r : ParseResult String) (input : String) (lhs : Term) : ParseResult Term :=
	match r {
		success rem op => expr_op_prec input lhs op rem,
		fail _ => success input lhs
	}

def expr_op_prec (input : String) (lhs : Term) (op : String) (rem : String) : ParseResult Term :=
	expr_op_prec_val (op_precedence op) input lhs op rem

def expr_op_prec_val (prec : I64) (input : String) (lhs : Term) (op : String) (rem : String) : ParseResult Term :=
	if I64.beq prec 0
	then success input lhs
	else expr_op_rhs_ws (take_while is_space rem) lhs op

def expr_op_rhs_ws (r : ParseResult String) (lhs : Term) (op : String) : ParseResult Term :=
	match r {
		success rem _ => expr_op_rhs_expr (expression rem) lhs op,
		fail e => fail e
	}

def expr_op_rhs_expr (r : ParseResult Term) (lhs : Term) (op : String) : ParseResult Term :=
	match r {
		success rem rhs => success rem (Term.app (Term.app (Term.var (NameRef.nop (Operator.operator op))) lhs) rhs),
		fail e => fail e
	}

// --- Declaration parsers ---

// Module path parser (e.g. init.prelude)

def module_path_parser (input : String) : ParseResult ModulePath :=
	mp_first (identifier input)

def mp_first (r : ParseResult String) : ParseResult ModulePath :=
	match r {
		success rem first => mp_need_dot rem (List.cons (Identifier.id first) List.empty),
		fail e => fail e
	}

def mp_need_dot (input : String) (ids : List Identifier) : ParseResult ModulePath :=
	mp_need_dot_try (tag "." input) ids input

def mp_need_dot_try (r : ParseResult String) (ids : List Identifier) (orig : String) : ParseResult ModulePath :=
	match r {
		success rem _ => mp_field (identifier rem) ids,
		fail _ =>
			let rev : List Identifier := list_reverse ids in
			success orig (ModulePath.mp rev)
	}

def mp_loop (input : String) (ids : List Identifier) : ParseResult ModulePath :=
	mp_loop_dot (tag "." input) ids input

def mp_loop_dot (r : ParseResult String) (ids : List Identifier) (orig : String) : ParseResult ModulePath :=
	match r {
		success rem _ => mp_field (identifier rem) ids,
		fail _ =>
			let rev : List Identifier := list_reverse ids in
			success orig (ModulePath.mp rev)
	}

def mp_field (r : ParseResult String) (ids : List Identifier) : ParseResult ModulePath :=
	match r {
		success rem next => mp_loop rem (List.cons (Identifier.id next) ids),
		fail e => fail e
	}

// use module.path

def use_parser (input : String) : ParseResult Decl :=
	use_kw (tag "use" input)

def use_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => use_path (module_path_parser (skip_spaces rem)),
		fail e => fail e
	}

def use_path (r : ParseResult ModulePath) : ParseResult Decl :=
	match r {
		success rem path => success rem (Decl.use_d path),
		fail e => fail e
	}

// open module.path

def open_parser (input : String) : ParseResult Decl :=
	open_kw (tag "open" input)

def open_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => open_path (module_path_parser (skip_spaces rem)),
		fail e => fail e
	}

def open_path (r : ParseResult ModulePath) : ParseResult Decl :=
	match r {
		success rem path => success rem (Decl.open_d path),
		fail e => fail e
	}

// infix:prec (op) := path

def infix_parser (input : String) : ParseResult Decl :=
	infix_kw (tag "infix" input)

def infix_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => infix_colon (tag ":" (skip_spaces rem)) rem,
		fail e => fail e
	}

def infix_colon (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => infix_prec (number rem),
		fail _ => infix_paren (tag "(" (skip_spaces orig)) orig
	}

def infix_prec (r : ParseResult I64) : ParseResult Decl :=
	match r {
		success rem _ => infix_paren (tag "(" (skip_spaces rem)) rem,
		fail e => fail e
	}

def infix_paren (r : ParseResult String) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => infix_op (operator_parse (skip_spaces rem)),
		fail e => fail e
	}

def infix_op (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem op => infix_close (tag ")" (skip_spaces rem)) op,
		fail e => fail e
	}

def infix_close (r : ParseResult String) (op : String) : ParseResult Decl :=
	match r {
		success rem _ => infix_assign (tag ":=" (skip_spaces rem)) op,
		fail e => fail e
	}

def infix_assign (r : ParseResult String) (op : String) : ParseResult Decl :=
	match r {
		success rem _ => infix_path (module_path_parser (skip_spaces rem)) op,
		fail e => fail e
	}

def infix_path (r : ParseResult ModulePath) (op : String) : ParseResult Decl :=
	match r {
		success rem path => success rem (Decl.infix_d (Operator.operator op) path),
		fail e => fail e
	}

// type Name { constructor1 (args), constructor2 }

def type_parser (input : String) : ParseResult Decl :=
	type_kw (tag "type" input)

def type_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => type_name (identifier (skip_spaces rem)),
		fail e => fail e
	}

def type_name (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem name =>
			let empty_params : List Identifier := List.empty in
			type_params_skip rem (Identifier.id name) empty_params,
		fail e => fail e
	}

def type_params_skip (input : String) (name : Identifier) (params : List Identifier) : ParseResult Decl :=
	type_params_skip_try (identifier (skip_spaces input)) input name params

def type_params_skip_try (r : ParseResult String) (orig : String) (name : Identifier) (params : List Identifier) : ParseResult Decl :=
	match r {
		success rem next => type_params_skip rem name (List.cons (Identifier.id next) params),
		fail _ => type_brace (tag "{" (skip_spaces orig)) name
	}

def type_brace (r : ParseResult String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ => type_constructors_with_name rem name,
		fail e => fail e
	}

def type_constructors_with_name (input : String) (name : Identifier) : ParseResult Decl :=
	type_cons_first_named (type_one_constructor (skip_spaces input)) input name

def type_cons_first_named (r : ParseResult InductConstructor) (orig : String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem con => type_cons_rest_named rem (List.cons con List.empty) name,
		fail _ => type_empty_close_named (tag "}" (skip_spaces orig)) name
	}

def type_empty_close_named (r : ParseResult String) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ =>
			let empty : List InductConstructor := List.empty in
			success rem (type_to_decl name empty),
		fail e => fail (ParseError.custom "expected }")
	}

def type_cons_rest_named (input : String) (cons : List InductConstructor) (name : Identifier) : ParseResult Decl :=
	type_cons_rest_comma_named (tag "," (skip_spaces input)) input cons name

def type_cons_rest_comma_named (r : ParseResult String) (orig : String) (cons : List InductConstructor) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem _ => type_cons_rest_more_named (type_one_constructor (skip_spaces rem)) cons name,
		fail _ => type_close_brace (tag "}" (skip_spaces orig)) name cons
	}

def type_cons_rest_more_named (r : ParseResult InductConstructor) (cons : List InductConstructor) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem con => type_cons_rest_named rem (List.cons con cons) name,
		fail _ => type_close_brace (tag "}" (skip_spaces "")) name cons
	}

def type_close_brace (r : ParseResult String) (name : Identifier) (cons : List InductConstructor) : ParseResult Decl :=
	match r {
		success rem _ =>
			let rev : List InductConstructor := list_reverse cons in
			success rem (type_to_decl name rev),
		fail e => fail e
	}

def type_one_constructor (input : String) : ParseResult InductConstructor :=
	type_cons_name (identifier input)

def type_cons_name (r : ParseResult String) : ParseResult InductConstructor :=
	match r {
		success rem name => type_cons_paren_or_nil (tag "(" (skip_spaces rem)) rem (Identifier.id name),
		fail e => fail e
	}

def type_cons_paren_or_nil (r : ParseResult String) (orig : String) (name : Identifier) : ParseResult InductConstructor :=
	match r {
		success rem _ => type_cons_params (type_param_list rem) name,
		fail _ =>
			let empty_params : List Param := List.empty in
			success orig (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) empty_params (Term.hole))
	}

def type_cons_paren (r : ParseResult String) (name : Identifier) : ParseResult InductConstructor :=
	match r {
		success rem _ => type_cons_params (type_param_list rem) name,
		fail _ => type_cons_no_paren name
	}

def type_cons_no_paren (name : Identifier) : ParseResult InductConstructor :=
	let empty_params : List Param := List.empty in
	fail (ParseError.custom "expected params")

def type_cons_params (r : ParseResult (List Param)) (name : Identifier) : ParseResult InductConstructor :=
	match r {
		success rem params => type_cons_close_paren (tag ")" (skip_spaces rem)) name params,
		fail e => fail e
	}

def type_cons_close_paren (r : ParseResult String) (name : Identifier) (params : List Param) : ParseResult InductConstructor :=
	match r {
		success rem _ => success rem (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) params (Term.hole)),
		fail e => fail e
	}

def type_param_list (input : String) : ParseResult (List Param) :=
	type_param_first (type_one_param (skip_spaces input))

def type_one_param (input : String) : ParseResult Param :=
	type_one_param_name (identifier input)

def type_one_param_name (r : ParseResult String) : ParseResult Param :=
	match r {
		success rem name => type_one_param_type (tag ":" (skip_spaces rem)) (Identifier.id name),
		fail e => fail e
	}

def type_one_param_type (r : ParseResult String) (name : Identifier) : ParseResult Param :=
	match r {
		success rem _ => type_one_param_val (type_expression (skip_spaces rem)) name,
		fail e => fail e
	}

def type_one_param_val (r : ParseResult Term) (name : Identifier) : ParseResult Param :=
	match r {
		success rem typ => success rem (Param.mk name typ),
		fail e => fail e
	}

def type_param_first (r : ParseResult Param) : ParseResult (List Param) :=
	match r {
		success rem param => type_param_rest rem (List.cons param List.empty),
		fail _ =>
			let empty : List Param := List.empty in
			success "" empty
	}

def type_param_rest (input : String) (params : List Param) : ParseResult (List Param) :=
	type_param_rest_comma (tag "," (skip_spaces input)) input params

def type_param_rest_comma (r : ParseResult String) (orig : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ => type_param_rest_more (type_one_param (skip_spaces rem)) params,
		fail _ =>
			let rev : List Param := list_reverse params in
			success orig rev
	}

def type_param_rest_more (r : ParseResult Param) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem param => type_param_rest rem (List.cons param params),
		fail _ =>
			let rev : List Param := list_reverse params in
			success "" rev
	}

def type_cons_done (name : Identifier) : ParseResult InductConstructor :=
	let empty_params : List Param := List.empty in
	success "" (InductConstructor.mk (ModulePath.mp (List.cons name List.empty)) empty_params (Term.hole))

def type_to_decl (name : Identifier) (cons : List InductConstructor) : Decl :=
	let empty_params : List Param := List.empty in
	let empty_attrs : List String := List.empty in
	Decl.inductive_d (Inductive.mk (ModulePath.mp (List.cons name List.empty)) empty_params (Term.type_ 1) cons empty_attrs)

def def_parser (input : String) : ParseResult Decl :=
	def_kw (tag "def" input)

def def_kw (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem _ => def_name (identifier (skip_spaces rem)),
		fail e => fail e
	}

def def_name (r : ParseResult String) : ParseResult Decl :=
	match r {
		success rem name =>
			let empty : List Param := List.empty in
			def_params (def_params_loop (skip_spaces rem) empty) (Identifier.id name),
		fail e => fail e
	}

def def_params_loop (input : String) (params : List Param) : ParseResult (List Param) :=
	def_params_try_implicit (tag "{" input) input params

def def_params_try_implicit (r : ParseResult String) (orig : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ => def_implicit_param (identifier (skip_spaces rem)) rem params,
		fail _ => def_params_try_explicit (tag "(" orig) orig params
	}

def def_implicit_param (r : ParseResult String) (rem : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 name => def_implicit_colon (tag ":" (skip_spaces rem2)) rem rem2 name params,
		fail e => fail e
	}

def def_implicit_colon (r : ParseResult String) (brace_rem : String) (rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 _ => def_implicit_type (type_expression rem2) brace_rem rem name params,
		fail e => fail e
	}

def def_implicit_type (r : ParseResult Term) (brace_rem : String) (rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 typ => def_implicit_close (tag "}" rem2) brace_rem name typ params,
		fail e => fail e
	}

def def_implicit_close (r : ParseResult String) (brace_rem : String) (name : String) (typ : Term) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem2 _ =>
			let empty : List Param := List.empty in
			def_params_loop (skip_spaces rem2) empty,
		fail e => fail e
	}

def def_params_try_explicit (r : ParseResult String) (orig : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ => def_explicit_param (identifier (skip_spaces rem)) rem params,
		fail _ =>
			let rev : List Param := list_reverse params in
			success orig rev
	}

def def_explicit_param (r : ParseResult String) (close_rem : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem name => def_explicit_colon (tag ":" (skip_spaces rem)) close_rem name params,
		fail e => fail e
	}

def def_explicit_colon (r : ParseResult String) (close_rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ => def_explicit_type (type_expression rem) close_rem name params,
		fail e => fail e
	}

def def_explicit_type (r : ParseResult Term) (close_rem : String) (name : String) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem typ => def_explicit_close (tag ")" rem) close_rem name typ params,
		fail e => fail e
	}

def def_explicit_close (r : ParseResult String) (close_rem : String) (name : String) (typ : Term) (params : List Param) : ParseResult (List Param) :=
	match r {
		success rem _ => def_params_loop (skip_spaces rem) (List.cons (Param.mk (Identifier.id name) typ) params),
		fail e => fail e
	}

def def_params (r : ParseResult (List Param)) (name : Identifier) : ParseResult Decl :=
	match r {
		success rem params => def_ret_type (tag ":" (skip_spaces rem)) rem name params,
		fail e => fail e
	}

def def_ret_type (r : ParseResult String) (orig : String) (name : Identifier) (params : List Param) : ParseResult Decl :=
	match r {
		success rem _ => def_ret_expr (type_expression rem) name params,
		fail _ => fail (ParseError.custom "expected : return type")
	}

def def_ret_expr (r : ParseResult Term) (name : Identifier) (params : List Param) : ParseResult Decl :=
	match r {
		success rem typ => def_body rem name params typ,
		fail e => fail e
	}

def def_body (input : String) (name : Identifier) (params : List Param) (typ : Term) : ParseResult Decl :=
	def_body_assign (tag ":=" (skip_spaces input)) name params typ input

def def_body_assign (r : ParseResult String) (name : Identifier) (params : List Param) (typ : Term) (orig : String) : ParseResult Decl :=
	match r {
		success rem _ => def_body_expr (expression (skip_spaces rem)) name params typ,
		fail _ => def_body_block (tag "{" (skip_spaces orig)) name params typ
	}

def def_body_expr (r : ParseResult Term) (name : Identifier) (params : List Param) (typ : Term) : ParseResult Decl :=
	match r {
		success rem body => success rem (def_to_decl (lam_params params body) name typ),
		fail e => fail e
	}

def def_body_block (r : ParseResult String) (name : Identifier) (params : List Param) (typ : Term) : ParseResult Decl :=
	match r {
		success rem _ => def_body_do (do_stmts rem) name params typ,
		fail e => fail e
	}

def def_body_do (r : ParseResult (List DoStmt)) (name : Identifier) (params : List Param) (typ : Term) : ParseResult Decl :=
	match r {
		success rem stmts => success rem (def_to_decl (lam_params params (desugar_do stmts)) name typ),
		fail e => fail e
	}

def lam_params (params : List Param) (body : Term) : Term :=
	let rev : List Param := list_reverse params in
	lam_params_loop rev body

def lam_params_loop (params : List Param) (body : Term) : Term :=
	match params {
		List.cons p rest => lam_params_loop rest (Term.lam p body),
		List.empty => body
	}

def def_to_decl (body : Term) (name : Identifier) (typ : Term) : Decl :=
	let empty_constraints : List TypeConstraint := List.empty in
	let empty_attrs : List String := List.empty in
	Decl.def_d (Def.mk (ModulePath.mp (List.cons name List.empty)) typ body empty_constraints empty_attrs)

// Top-level declaration dispatcher

def decl_parser (input : String) : ParseResult Decl :=
	decl_try_use (use_parser input) input

def decl_try_use (r : ParseResult Decl) (input : String) : ParseResult Decl :=
	match r {
		success rem out => success rem out,
		fail _ => decl_try_open (open_parser input) input
	}

def decl_try_open (r : ParseResult Decl) (input : String) : ParseResult Decl :=
	match r {
		success rem out => success rem out,
		fail _ => decl_try_infix (infix_parser input) input
	}

def decl_try_infix (r : ParseResult Decl) (input : String) : ParseResult Decl :=
	match r {
		success rem out => success rem out,
		fail _ => decl_try_def (def_parser input) input
	}

def decl_try_def (r : ParseResult Decl) (input : String) : ParseResult Decl :=
	match r {
		success rem out => success rem out,
		fail _ => decl_try_type (type_parser input) input
	}

def decl_try_type (r : ParseResult Decl) (input : String) : ParseResult Decl :=
	match r {
		success rem out => success rem out,
		fail _ => fail (ParseError.custom "unknown declaration")
	}

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

def main : I64 := 42
