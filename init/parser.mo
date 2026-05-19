type ParseError {
	tagE String,
	altE (List ParseError),
	customE String,
	expectedE String
}

type ParseResult O {
	success (remaining: String) (output: O),
	fail (error: ParseError)
}

open ParseResult

def tag (s : String) : String -> ParseResult String := \input =>
	if String.starts_with s input
	then success (String.drop (String.length s) input) s
	else fail (ParseError.tagE s)

def eof : String -> ParseResult Unit := \input =>
	if String.is_empty input
	then success input unit
	else fail (ParseError.expectedE "end of input")

def alt (a : String -> ParseResult A) (b : String -> ParseResult A) (input : String) : ParseResult A :=
	alt_step (a input) b input

def alt_step (r : ParseResult A) (b : String -> ParseResult A) (input : String) : ParseResult A :=
	match r {
		success remaining output => success remaining output,
		fail e1 => alt_step2 (b input) e1
	}

def alt_step2 (r : ParseResult A) (e1 : ParseError) : ParseResult A :=
	match r {
		success remaining output => success remaining output,
		fail e2 => fail (ParseError.altE (List.cons e1 (List.cons e2 List.empty)))
	}

infix (<|>) := alt

@[terminating]
def many0 (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	many0_step (p input) p input

def many0_step (r : ParseResult A) (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	match r {
		success rem out =>
			match many0 p rem {
				success rem2 rest => success rem2 (List.cons out rest),
				fail _ => success rem (List.cons out List.empty)
			},
		fail _ => success input List.empty
	}

def many1 (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	many1_step (p input) p input

def many1_step (r : ParseResult A) (p : String -> ParseResult A) (input : String) : ParseResult (List A) :=
	match r {
		success rem out =>
			match many0 p rem {
				success rem2 rest => success rem2 (List.cons out rest),
				fail _ => success rem (List.cons out List.empty)
			},
		fail e => fail e
	}

@[test]
def test_tag_success : Bool :=
	match tag "hel" "hello" {
		success remaining output =>
			String.beq output "hel" && String.beq remaining "lo",
		fail _ => false
	}

@[test]
def test_tag_fail : Bool :=
	match tag "xyz" "hello" {
		success _ _ => false,
		fail _ => true
	}

@[test]
def test_alt_first : Bool :=
	match (alt (tag "foo") (tag "bar")) "foobar" {
		success remaining output =>
			String.beq output "foo" && String.beq remaining "bar",
		fail _ => false
	}

@[test]
def test_alt_second : Bool :=
	match (alt (tag "foo") (tag "bar")) "barbaz" {
		success remaining output =>
			String.beq output "bar" && String.beq remaining "baz",
		fail _ => false
	}

@[test]
def test_alt_both_fail : Bool :=
	match (alt (tag "foo") (tag "bar")) "xyz" {
		success _ _ => false,
		fail _ => true
	}

@[test]
def test_alt_infix : Bool :=
	match (tag "foo" <|> tag "bar") "bar" {
		success _ output => String.beq output "bar",
		fail _ => false
	}

@[test]
def test_many0_no_match : Bool :=
	match many0 (tag "x") "hello" {
		success remaining list =>
			List.is_empty list && String.beq remaining "hello",
		fail _ => false
	}

@[test]
def test_many0_one_match : Bool :=
	match many0 (tag "h") "hello" {
		success remaining list =>
			not (List.is_empty list) && String.beq remaining "ello",
		fail _ => false
	}

@[test]
def test_many0_multi_match : Bool :=
	match many0 (tag "a") "aaab" {
		success remaining list => true,
		fail _ => false
	}

@[test]
def test_many1_success : Bool :=
	match many1 (tag "a") "aabc" {
		success remaining list => true,
		fail _ => false
	}

@[test]
def test_many1_fail : Bool :=
	match many1 (tag "x") "abc" {
		success _ _ => false,
		fail _ => true
	}

@[terminating]
def char_in_string (c : String) (s : String) : Bool :=
	if String.is_empty s then false
	else if String.beq (String.slice s 0 1) c then true
	else char_in_string c (String.drop 1 s)

def is_digit (c : String) : Bool :=
	char_in_string c "0123456789"

def is_alpha (c : String) : Bool :=
	char_in_string c "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

def is_alphanumeric (c : String) : Bool := is_digit c || is_alpha c

def is_space (c : String) : Bool :=
	char_in_string c " \t\n\r"

def is_ident_char (c : String) : Bool :=
	is_alphanumeric c || String.beq "_" c

def satisfy (pred : String -> Bool) (input : String) : ParseResult String :=
	if String.is_empty input
	then fail (ParseError.customE "unexpected eof")
	else satisfy_step pred (String.slice input 0 1) (String.drop 1 input)

def satisfy_step (pred : String -> Bool) (ch : String) (rest : String) : ParseResult String :=
	if pred ch
	then success rest ch
	else fail (ParseError.customE ("unexpected: " ++ ch))

def char (c : String) (input : String) : ParseResult String :=
	satisfy (\ch => String.beq ch c) input

def digit (input : String) : ParseResult String :=
	satisfy is_digit input

def alpha (input : String) : ParseResult String :=
	satisfy is_alpha input

def space (input : String) : ParseResult String :=
	satisfy is_space input

def take_while (pred : String -> Bool) (input : String) : ParseResult String :=
	take_while_step pred "" input

@[terminating]
def take_while_step (pred : String -> Bool) (acc : String) (input : String) : ParseResult String :=
	if String.is_empty input
	then success input acc
	else take_while_step_body pred acc input (String.slice input 0 1) (String.drop 1 input)

@[terminating]
def take_while_step_body (pred : String -> Bool) (acc : String) (input : String) (ch : String) (rest : String) : ParseResult String :=
	if pred ch
	then take_while_step pred (String.concat acc ch) rest
	else success input acc

def opt (p : String -> ParseResult A) (input : String) : ParseResult (Option A) :=
	opt_body (p input) input

def opt_body (r : ParseResult A) (input : String) : ParseResult (Option A) :=
	match r {
		success rem out => opt_some rem out,
		fail _ => opt_none input
	}

def opt_some (rem : String) (out : A) : ParseResult (Option A) :=
	success rem (some out)

def opt_none (input : String) : ParseResult (Option A) :=
	success input none

def preceded (before : String -> ParseResult A) (p : String -> ParseResult B) (input : String) : ParseResult B :=
	preceded_before (before input) p

def preceded_before (r : ParseResult A) (p : String -> ParseResult B) : ParseResult B :=
	match r {
		success rem _ => p rem,
		fail e => preceded_fail e
	}

def preceded_fail (e : ParseError) : ParseResult B :=
	fail e

def terminated (p : String -> ParseResult A) (after : String -> ParseResult B) (input : String) : ParseResult A :=
	terminated_parse (p input) after

def terminated_parse (r : ParseResult A) (after : String -> ParseResult B) : ParseResult A :=
	match r {
		success rem out => terminated_after (after rem) out,
		fail e => terminated_err e
	}

def terminated_after (r : ParseResult B) (out : A) : ParseResult A :=
	match r {
		success rem _ => terminated_ok rem out,
		fail e => terminated_err e
	}

def terminated_ok (rem : String) (out : A) : ParseResult A :=
	success rem out

def terminated_err (e : ParseError) : ParseResult A :=
	fail e

def delimited (before : String -> ParseResult A) (p : String -> ParseResult B) (after : String -> ParseResult C) (input : String) : ParseResult B :=
	delimited_before (before input) p after

def delimited_before (r : ParseResult A) (p : String -> ParseResult B) (after : String -> ParseResult C) : ParseResult B :=
	match r {
		success rem _ => delimited_parse p after rem,
		fail e => delimited_err e
	}

def delimited_parse (p : String -> ParseResult B) (after : String -> ParseResult C) (rem : String) : ParseResult B :=
	delimited_body (p rem) after

def delimited_body (r : ParseResult B) (after : String -> ParseResult C) : ParseResult B :=
	match r {
		success rem2 out => delimited_after (after rem2) out,
		fail e => delimited_err e
	}

def delimited_after (r : ParseResult C) (out : B) : ParseResult B :=
	match r {
		success rem3 _ => delimited_ok rem3 out,
		fail e => delimited_err e
	}

def delimited_ok (rem : String) (out : B) : ParseResult B :=
	success rem out

def delimited_err (e : ParseError) : ParseResult B :=
	fail e

def recognize (p : String -> ParseResult A) (input : String) : ParseResult String :=
	recognize_parse (p input) input

def recognize_parse (r : ParseResult A) (input : String) : ParseResult String :=
	match r {
		success rem _ => recognize_ok input rem,
		fail e => fail e
	}

def recognize_ok (input : String) (rem : String) : ParseResult String :=
	success rem (String.slice input 0 (I64.sub (String.length input) (String.length rem)))

@[test]
def test_char_in_string_true : Bool :=
	char_in_string "a" "abcde"

@[test]
def test_char_in_string_false : Bool :=
	not (char_in_string "z" "abcde")

@[test]
def test_is_digit : Bool :=
	is_digit "5" && not (is_digit "a")

@[test]
def test_is_alpha : Bool :=
	is_alpha "a" && is_alpha "Z" && not (is_alpha "5")

@[test]
def test_is_space : Bool :=
	is_space " " && is_space "\n" && not (is_space "a")

@[test]
def test_satisfy_digit : Bool :=
	match (satisfy is_digit) "123" {
		success rem out => String.beq out "1" && String.beq rem "23",
		fail _ => false
	}

@[test]
def test_char : Bool :=
	match (char "h") "hello" {
		success rem out => String.beq out "h" && String.beq rem "ello",
		fail _ => false
	}

@[test]
def test_digit_parser : Bool :=
	match digit "42abc" {
		success rem out => String.beq out "4" && String.beq rem "2abc",
		fail _ => false
	}

@[test]
def test_take_while_digits : Bool :=
	match (take_while is_digit) "123abc" {
		success rem out => String.beq out "123" && String.beq rem "abc",
		fail _ => false
	}

def is_some (x : Option A) : Bool :=
	match x {
		some _ => true,
		none => false
	}

def is_none (x : Option A) : Bool :=
	match x {
		some _ => false,
		none => true
	}

@[test]
def test_opt_some : Bool :=
	match (opt digit) "123" {
		success rem out => is_some out && String.beq rem "23",
		fail _ => false
	}

@[test]
def test_opt_none : Bool :=
	match (opt digit) "abc" {
		success rem out => is_none out && String.beq rem "abc",
		fail _ => false
	}

@[test]
def test_recognize : Bool :=
	match (recognize (tag "hello")) "hello world" {
		success rem out => String.beq out "hello" && String.beq rem " world",
		fail _ => false
	}
