/// Number parsing functions for the self-hosted Monad parser.

use lang.parser.core {ParseResult, custom, fail, is_empty, success}
use lang.parser.char_preds {is_digit}
use lang.parser.combinators {take_while}

open ParseResult {fail, success}


// --- Number parser ---

#[partial]
def is_digit_or_underscore (c : String) : Bool :=
	if is_digit c then true
	else String.beq "_" c


#[partial]
def number (input : String) : ParseResult I64 :=
	number_body (take_while is_digit_or_underscore input)


#[partial]
def number_body (r : ParseResult String) : ParseResult I64 :=
	match r {
		success rem out =>
			if is_empty out
			then fail (ParseError.custom "expected number")
			else number_parse out rem,
		fail e => fail e
	}


#[partial]
def number_parse (s : String) (rem : String) : ParseResult I64 :=
	if is_empty s
	then fail (ParseError.custom "empty number")
	else if is_digit (String.slice s 0 1)
	then success rem (parse_digits s)
	else fail (ParseError.custom "number must start with digit")


// --- Number parsing helpers ---

#[partial]
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


#[partial]
def parse_digits (s : String) : I64 :=
	parse_digits_loop s 0


#[partial]
def parse_digits_loop (s : String) (acc : I64) : I64 :=
	if is_empty s
	then acc
	else parse_digits_char (String.slice s 0 1) (String.drop 1 s) acc


#[partial]
def parse_digits_char (ch : String) (rest : String) (acc : I64) : I64 :=
	parse_digits_loop rest (I64.add (I64.mul acc 10) (char_to_digit ch))
