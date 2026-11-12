/// Parser golden tests: each syntax form's `RxAst.render`, and each refusal's
/// message and exact span.
use regex::syntax::parser {parse, RxParsed}
use regex::syntax::ast {RxAst}
use regex::error {RegexSpan, RegexError}
use std::list {}

/// The tree, or `err <start>-<end> <message>`.
def show (pattern : String) : String :=
    match parse pattern false 250 {
        Result.ok r => RxAst.render r.ast,
        Result.err e => show_err e,
    }

def show_x (pattern : String) : String :=
    match parse pattern true 250 {
        Result.ok r => RxAst.render r.ast,
        Result.err e => show_err e,
    }

def show_err (e : RegexError) : String :=
    match RegexError.span e {
        Option.some sp =>
            String.concat_list ["err ", I64.to_string sp.start, "-", I64.to_string sp.end, " ",
                RegexError.message e],
        Option.none => String.concat "err " (RegexError.message e),
    }

def is (pattern : String) (expected : String) : Bool := String.beq (show pattern) expected

// ─── Literals and escapes ───

#[test]
def test_literals : Bool :=
    is "a" "(lit 97)"
        && is "ab" "(cat (lit 97) (lit 98))"
        && is "" "empty"
        && is "é" "(lit 233)"
        && is "日" "(lit 26085)"

#[test]
def test_escapes : Bool :=
    is r#"\n\t\x41\x{1F600}é\U0001F600"# "(cat (lit 10) (lit 9) (lit 65) (lit 128512) (lit 233) (lit 128512))"
        && is r#"\.\*\+\?\(\)\[\]\{\}\|\^\$\\\#\&\-\~"#
            "(cat (lit 46) (lit 42) (lit 43) (lit 63) (lit 40) (lit 41) (lit 91) (lit 93) (lit 123) (lit 125) (lit 124) (lit 94) (lit 36) (lit 92) (lit 35) (lit 38) (lit 45) (lit 126))"

#[test]
def test_escape_errors : Bool :=
    is r#"\"# "err 0-1 incomplete escape sequence"
        && is r#"\q"# "err 0-2 unrecognized escape sequence"
        && is r#"\x{110000}"# "err 0-10 escape is not a Unicode scalar value"
        && is r#"\xZ"# "err 0-3 invalid hexadecimal escape"

// ─── Classes ───

#[test]
def test_perl_and_unicode_classes : Bool :=
    is r#"\d\D\s\S\w\W"# "(cat (perl d) (perl ^d) (perl s) (perl ^s) (perl w) (perl ^w))"
        && is r#"\pL\p{Greek}\P{Lu}\p{^N}"# "(cat (prop L) (prop Greek) (prop ^Lu) (prop ^N))"

#[test]
def test_brackets : Bool :=
    is "[a-z]" "(class [97-122])"
        && is "[^abc]" "(class ^[97 98 99])"
        && is "[]a]" "(class [93 97])"
        && is "[a-]" "(class [97 45])"
        && is "[[:alpha:][:^digit:]]" "(class [[:alpha:] [:^digit:]])"
        && is r#"[\d\p{Greek}x]"# "(class [\\d \\p{Greek} 120])"
        && is "[a[bc]]" "(class [97 [98 99]])"

#[test]
def test_set_operations : Bool :=
    is "[a-z&&[^aeiou]]" "(class [(97-122 && [^97 101 105 111 117])])"
        && is "[a-z--b~~c]" "(class [((97-122 -- 98) ~~ 99)])"

#[test]
def test_class_errors : Bool :=
    is "[a" "err 0-1 unclosed character class"
        && is "[z-a]" "err 2-4 invalid class range: the start exceeds the end"
        && is "[[:foo:]]" "err 1-8 invalid ASCII class name"
        && is r#"[\b]"# "err 1-3 assertions are not allowed in a character class"

// ─── Repetition ───

#[test]
def test_repetition : Bool :=
    is "a*" "(rep 0 inf (lit 97))"
        && is "a+?" "(rep 1 inf lazy (lit 97))"
        && is "a?" "(rep 0 1 (lit 97))"
        && is "a{3}" "(rep 3 3 (lit 97))"
        && is "a{3,}" "(rep 3 inf (lit 97))"
        && is "a{3,5}?" "(rep 3 5 lazy (lit 97))"
        && is "a{,5}" "(rep 0 5 (lit 97))"
        && is "ab*" "(cat (lit 97) (rep 0 inf (lit 98)))"

#[test]
def test_repetition_errors : Bool :=
    is "*a" "err 0-1 repetition operator missing expression"
        && is "a{" "err 1-2 unclosed counted repetition"
        && is "a{5,3}" "err 1-6 invalid repetition range: the minimum exceeds the maximum"
        && is "a{}" "err 1-3 repetition quantifier expects a count"
        && is "(?i)*" "err 4-5 repetition operator missing expression"

// ─── Groups and flags ───

#[test]
def test_groups : Bool :=
    is "(a)(b)" "(cat (group cap 1 (lit 97)) (group cap 2 (lit 98)))"
        && is "(?:a)" "(group nc  (lit 97))"
        && is "(?P<y>a)(?<m>b)" "(cat (group cap 1 y (lit 97)) (group cap 2 m (lit 98)))"
        && is "(?i-s:a)" "(group nc i-s (lit 97))"
        && is "a(?i)b" "(cat (lit 97) (flags i) (lit 98))"
        && is "a|b|" "(alt (lit 97) (lit 98) empty)"
        && is "()" "(group cap 1 empty)"

#[test]
def test_anchors : Bool :=
    is r#"^\A\b\B\z$"# "(cat (assert ^) (assert \\A) (assert \\b) (assert \\B) (assert \\z) (assert $))"

#[test]
def test_group_errors : Bool :=
    is "(a" "err 0-1 unclosed group"
        && is "a)" "err 1-2 unopened group"
        && is "(?P<n>a)(?P<n>b)" "err 8-14 duplicate capture group name"
        && is "(?z)" "err 2-3 unrecognized flag"
        && is "(?)" "err 0-3 empty flag group"
        && is "(?ii)" "err 3-4 duplicate flag"
        && is "(?i-)" "err 4-5 expected a flag after '-'"

#[test]
def test_verbose_mode : Bool :=
    String.beq (show_x "a b # comment\n c") "(cat (lit 97) (lit 98) (lit 99))"
        && String.beq (show_x r#"a\ b"#) "(cat (lit 97) (lit 32) (lit 98))"
        && is "(?x) a b" "(cat (flags x) (lit 97) (lit 98))"
        && is "(?x: a ) b" "(cat (group nc x (lit 97)) (lit 32) (lit 98))"

// ─── G5: unsupported constructs, with spans ───

#[test]
def test_unsupported : Bool :=
    is r#"(a)\1"# "err 3-5 backreferences is not supported: this engine guarantees linear-time matching, which rules it out"
        && is "(?=a)" "err 0-3 look-ahead is not supported: this engine guarantees linear-time matching, which rules it out"
        && is "(?!a)" "err 0-3 look-ahead is not supported: this engine guarantees linear-time matching, which rules it out"
        && is "(?<=a)" "err 0-4 look-behind is not supported: this engine guarantees linear-time matching, which rules it out"
        && is "(?<!a)" "err 0-4 look-behind is not supported: this engine guarantees linear-time matching, which rules it out"
        && is "(?>a)" "err 0-3 atomic groups is not supported: this engine guarantees linear-time matching, which rules it out"
        && is "a++" "err 2-3 possessive repetition is not supported: use a plain greedy repetition: this engine never backtracks, so it cannot need one"

#[test]
def test_nest_limit : Bool :=
    match parse "((((a))))" false 3 {
        Result.err e => String.beq (RegexError.message e) "pattern nests deeper than the limit of 3",
        Result.ok _ => false,
    }

#[test]
def test_capture_count_and_names : Bool :=
    match parse "(a)(?P<x>b)(?:c)" false 250 {
        Result.ok r => I64.beq r.captures 2 && I64.beq (List.length r.names) 1,
        Result.err _ => false,
    }

#[test]
def test_render_caret : Bool :=
    match parse r#"(a)\1"# false 250 {
        Result.err e =>
            String.beq (RegexError.render e r#"(a)\1"#)
                "regex parse error: backreferences is not supported: this engine guarantees linear-time matching, which rules it out\n    (a)\\1\n       ^^",
        Result.ok _ => false,
    }

/// The caret counts scalars, not bytes.
#[test]
def test_render_caret_after_multibyte : Bool :=
    match parse "é(?=a)" false 250 {
        Result.err e =>
            String.beq (RegexError.render e "é(?=a)")
                "regex parse error: look-ahead is not supported: this engine guarantees linear-time matching, which rules it out\n    é(?=a)\n     ^^^",
        Result.ok _ => false,
    }
