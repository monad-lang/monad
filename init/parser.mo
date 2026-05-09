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
