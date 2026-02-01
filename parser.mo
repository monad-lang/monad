
type Pair A B {
 pair A B
}

type ParseResult I O E {
 success (Pair I O),
 fail E,
}

type ParseError {
 tagE String,
}

def ParserFull (I O E : Type) : Type := I -> ParseResult I O E 
def Parser (O : Type) : Type := ParserFull String O ParserError


def tag (s : String) : Parser String := \input =>
  if input.starts_with s
  then success <| pair input s
  else fail <| ParserError.tagE s
 
