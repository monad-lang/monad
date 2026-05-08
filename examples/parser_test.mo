use init.parser
open init.parser.ParseResult

def list_is_empty (l : List A) : Bool :=
	match l {
		empty => true,
		cons _ _ => false
	}

def list_is_singleton (l : List String) (x : String) : Bool :=
	match l {
		empty => false,
		cons h t =>
			String.beq h x && list_is_empty t
	}

def list_is (l : List String) (xs : List String) : Bool :=
	match l {
		empty => match xs {
			empty => true,
			cons _ _ => false
		},
		cons h t => match xs {
			empty => false,
			cons h2 t2 =>
				String.beq h h2 && list_is t t2
		}
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
	match (many0 (tag "x")) "hello" {
		success remaining list =>
			list_is_empty list && String.beq remaining "hello",
		fail _ => false
	}

@[test]
def test_many0_one_match : Bool :=
	match (many0 (tag "h")) "hello" {
		success remaining list =>
			list_is_singleton list "h" && String.beq remaining "ello",
		fail _ => false
	}

@[test]
def test_many0_multi_match : Bool :=
	match (many0 (tag "a")) "aaab" {
		success remaining list =>
			list_is list ["a", "a", "a"] && String.beq remaining "b",
		fail _ => false
	}

@[test]
def test_many1_success : Bool :=
	match (many1 (tag "a")) "aabc" {
		success remaining list =>
			list_is list ["a", "a"] && String.beq remaining "bc",
		fail _ => false
	}

@[test]
def test_many1_fail : Bool :=
	match (many1 (tag "x")) "abc" {
		success _ _ => false,
		fail _ => true
	}
