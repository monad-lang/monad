/// The generated predicates at category boundaries.
use unicode::classify {
    Unicode.is_space_separator, Unicode.is_punctuation_or_symbol, Unicode.is_white_space,
    Unicode.is_word, Unicode.is_digit,
}

#[test]
def test_space_separator : Bool :=
    Unicode.is_space_separator 32u32 && Unicode.is_space_separator 160u32
        && Unicode.is_space_separator 12288u32
        && Bool.not (Unicode.is_space_separator 9u32)
        && Bool.not (Unicode.is_space_separator 65u32)

#[test]
def test_punctuation_or_symbol : Bool :=
    Unicode.is_punctuation_or_symbol 8212u32 && Unicode.is_punctuation_or_symbol 36u32
        && Unicode.is_punctuation_or_symbol 163u32
        && Bool.not (Unicode.is_punctuation_or_symbol 65u32)

#[test]
def test_white_space : Bool :=
    Unicode.is_white_space 9u32 && Unicode.is_white_space 13u32 && Unicode.is_white_space 133u32
        && Unicode.is_white_space 8232u32
        && Bool.not (Unicode.is_white_space 8203u32)

#[test]
def test_word : Bool :=
    Unicode.is_word 95u32 && Unicode.is_word 97u32 && Unicode.is_word 48u32
        && Unicode.is_word 233u32 && Unicode.is_word 26085u32
        && Unicode.is_word 769u32
        && Unicode.is_word 8205u32
        && Bool.not (Unicode.is_word 45u32)
        && Bool.not (Unicode.is_word 32u32)

#[test]
def test_digit : Bool :=
    Unicode.is_digit 48u32 && Unicode.is_digit 57u32 && Unicode.is_digit 1632u32
        && Bool.not (Unicode.is_digit 47u32)
        && Bool.not (Unicode.is_digit 178u32)
