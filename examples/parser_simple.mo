use init.parser
open init.parser.ParseResult

@[test]
def test_tag_success : Bool :=
	match tag "hel" "hello" {
		success remaining output =>
			String.beq output "hel" && String.beq remaining "lo",
		fail _ => false
	}
