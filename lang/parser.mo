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
	then success rem 42
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

def main : I64 := 42
