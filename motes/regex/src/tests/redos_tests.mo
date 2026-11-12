/// G1: classic ReDoS patterns stay linear. Each runs one search on inputs
/// of two sizes, 10x apart, and the Pike VM's step count (thread
/// operations, a deterministic clock) may grow at most 11x. A backtracking
/// engine is exponential or polynomial on every one of these.
use regex::regex {Regex, Regex.new, Regex.search_steps, Regex.is_match}

/// `s` doubled `k` times: `String.repeat` concatenates one copy at a time,
/// which is quadratic.
#[terminating]
def doubled (s : String) (k : I64) : String :=
    if I64.lt 0 k then doubled (String.concat s s) (k - 1) else s

/// `unit` repeated about `n` bytes' worth (to the next power of two).
def about (unit : String) (n : I64) : String := doubled unit (doublings (String.length unit) n 0)

#[terminating]
def doublings (len : I64) (n : I64) (k : I64) : I64 :=
    if I64.lt len n then doublings (len * 2) n (k + 1) else k

def steps (pat : String) (hay : String) : I64 :=
    match Regex.new pat {
        Result.ok r => Regex.search_steps r hay,
        Result.err _ => 0 - 1,
    }

/// Steps at 1x and 10x input; linear growth is at most 11x.
def linear (pat : String) (unit : String) (suffix : String) : Bool :=
    let body : String := about unit 1000 in
    let small : I64 := steps pat (String.concat body suffix) in
    let large : I64 := steps pat (String.concat (String.concat_list [body, body, body, body, body, body, body, body, body, body]) suffix) in
    I64.lt 0 small && I64.lt large (small * 11)

#[test]
def test_nested_plus : Bool := linear r#"(a+)+$"# "a" "!"

#[test]
def test_overlapping_alternation : Bool := linear r#"(a|aa)*b"# "a" ""

#[test]
def test_repeated_dot_star : Bool := linear r#"(.*a){20}"# "a" ""

#[test]
def test_word_list : Bool := linear r#"(\w+\s?)*$"# "word " "!"

#[test]
def test_email_like : Bool := linear r#"^(([a-z])+.)+[A-Z]([a-z])+$"# "abcdefgh" ""

/// And the answers are still right.
#[test]
def test_redos_answers : Bool :=
    match Regex.new r#"(a+)+$"# {
        Result.ok r => Bool.not (Regex.is_match r "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa!") && Regex.is_match r "aaa",
        Result.err _ => false,
    }
