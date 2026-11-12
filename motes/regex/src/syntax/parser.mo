/// The regex parser: pattern bytes to `RxAst`, with exact error spans.
///
/// A recursive descent over a `List U8` cursor (`RxP.rest`) plus its byte
/// offset (`RxP.pos`). Not `String.get`: compiled, every non-zero index pays a
/// `strlen`. Not an `Array`: `Array.from_list` is quadratic. The parser only
/// ever peeks at most three bytes ahead, which a list does in O(1).
///
/// `#[terminating]` marks the recursion the structural checker cannot see:
/// every cycle through the parser consumes at least one byte of `RxP.rest`
/// (or, for group/class entry, one byte and one level of `RxP.depth`), so
/// the pattern length bounds it.
///
/// Matches the Rust `regex` dialect; constructs that cannot run in linear
/// time (backreferences, lookaround, atomic groups, possessive repetition)
/// are `RegexError.unsupported` with the span of the construct.
use lib::error {RegexSpan, RegexSpan.at, RegexError}
use lib::syntax::ast {
    RxAst, RxAssert, RxClassItem, RxClassSet, RxFlag, RxFlagItem, RxGroupKind, RxPerl, RxSetOp,
}
use std::list {}

/// The parser's cursor and the state that crosses groups.
struct RxP {
    rest : List U8,
    pos : I64,
    /// The `x` flag, which changes how the pattern is read.
    ignore_ws : Bool,
    /// Capture groups opened so far.
    caps : I64,
    names : List (Pair String I64),
    depth : I64,
    limit : I64,
}

/// A parse step: a value and the cursor after it, or an error.
type RxStep A {
    step_ok (value : A) (p : RxP),
    step_fail (e : RegexError),
}

/// What `parse` returns: the tree, the number of capture groups and the
/// named groups with their indices.
pub struct RxParsed {
    ast : RxAst,
    captures : I64,
    names : List (Pair String I64),
}

pub def parse (pattern : String) (ignore_ws : Bool) (nest_limit : I64) : Result RegexError RxParsed :=
    let p0 : RxP := {
        rest := String.to_list pattern,
        pos := 0,
        ignore_ws := ignore_ws,
        caps := 0,
        names := List.empty,
        depth := 0,
        limit := nest_limit,
    } in
    match parse_alt p0 {
        RxStep.step_fail e => Result.err e,
        RxStep.step_ok ast p1 => finish_top ast p1,
    }

def finish_top (ast : RxAst) (p : RxP) : Result RegexError RxParsed :=
    if I64.lt (peek p) 0 then
        let r : RxParsed := { ast := ast, captures := p.caps, names := List.reverse p.names } in
        Result.ok r
    else Result.err (syntax_at "unopened group" p.pos (p.pos + 1))

// ─── Cursor primitives ───

/// The first byte of a one-character ASCII string: `ch "("` is 40.
def ch (s : String) : I64 :=
    match String.get s 0 {
        Option.some b => U8.to_i64 b,
        Option.none => 0 - 1,
    }

#[terminating]
def byte_at (xs : List U8) (n : I64) : I64 :=
    match xs {
        List.empty => 0 - 1,
        List.cons b rest => if I64.beq n 0 then U8.to_i64 b else byte_at rest (n - 1),
    }

#[terminating]
def drop_bytes (xs : List U8) (n : I64) : List U8 :=
    if I64.lt 0 n then
        match xs {
            List.empty => List.empty,
            List.cons _ rest => drop_bytes rest (n - 1),
        }
    else xs

/// The list's first byte alone.
def first_byte (xs : List U8) : List U8 :=
    match xs {
        List.empty => List.empty,
        List.cons b _ => List.cons b List.empty,
    }

/// The next byte, or -1 at the end.
def peek (p : RxP) : I64 := byte_at p.rest 0

def peek_at (p : RxP) (n : I64) : I64 := byte_at p.rest n

def bump (p : RxP) (n : I64) : RxP := { p with rest := drop_bytes p.rest n, pos := p.pos + n }

def is_at (p : RxP) (s : String) : Bool := I64.beq (peek p) (ch s)

def syntax_at (msg : String) (start : I64) (stop : I64) : RegexError :=
    RegexError.syntax msg (RegexSpan.at start stop)

def fail_at (msg : String) (start : I64) (stop : I64) : RxStep A :=
    RxStep.step_fail (syntax_at msg start stop)

def unsupported_at (feature : String) (start : I64) (stop : I64) (hint : String) : RxStep A :=
    RxStep.step_fail (RegexError.unsupported feature (RegexSpan.at start stop) hint)

def linear_hint : String :=
    "this engine guarantees linear-time matching, which rules it out"

def is_space (c : I64) : Bool :=
    I64.beq c 32 || (I64.lt 8 c && I64.lt c 14)

def is_digit (c : I64) : Bool := I64.lt 47 c && I64.lt c 58

def is_lower (c : I64) : Bool := I64.lt 96 c && I64.lt c 123

def is_upper (c : I64) : Bool := I64.lt 64 c && I64.lt c 91

def is_alnum (c : I64) : Bool := is_digit c || is_lower c || is_upper c

/// In `x` mode, skip whitespace and `#` comments.
#[terminating]
def skip_ws (p : RxP) : RxP :=
    if Bool.not p.ignore_ws then p
    else if is_space (peek p) then skip_ws (bump p 1)
    else if is_at p "#" then skip_ws (skip_comment (bump p 1))
    else p

#[terminating]
def skip_comment (p : RxP) : RxP :=
    if I64.lt (peek p) 0 then p
    else if I64.beq (peek p) 10 then bump p 1
    else skip_comment (bump p 1)

/// In `x` mode inside a class, skip whitespace only.
#[terminating]
def skip_class_ws (p : RxP) : RxP :=
    if p.ignore_ws && is_space (peek p) then skip_class_ws (bump p 1) else p

// ─── UTF-8 ───

/// A decoded scalar and its width in bytes; width 0 means invalid UTF-8.
struct RxDecoded {
    cp : I64,
    width : I64,
}

def decoded (cp : I64) (width : I64) : RxDecoded :=
    let d : RxDecoded := { cp := cp, width := width } in d

def cont (xs : List U8) (n : I64) : I64 :=
    let b : I64 := byte_at xs n in
    if I64.lt 127 b && I64.lt b 192 then I64.and b 63 else 0 - 1

def decode (xs : List U8) : RxDecoded :=
    let b0 : I64 := byte_at xs 0 in
    if I64.lt b0 128 then decoded b0 1
    else if I64.lt 193 b0 && I64.lt b0 224 then decode2 (I64.and b0 31) (cont xs 1)
    else if I64.lt 223 b0 && I64.lt b0 240 then decode3 (I64.and b0 15) (cont xs 1) (cont xs 2)
    else if I64.lt 239 b0 && I64.lt b0 245 then decode4 (I64.and b0 7) (cont xs 1) (cont xs 2) (cont xs 3)
    else decoded 0 0

def decode2 (h : I64) (c1 : I64) : RxDecoded :=
    if I64.lt c1 0 then decoded 0 0 else decoded (I64.or (I64.shl h 6) c1) 2

def decode3 (h : I64) (c1 : I64) (c2 : I64) : RxDecoded :=
    if I64.lt c1 0 || I64.lt c2 0 then decoded 0 0
    else decoded (I64.or (I64.shl h 12) (I64.or (I64.shl c1 6) c2)) 3

def decode4 (h : I64) (c1 : I64) (c2 : I64) (c3 : I64) : RxDecoded :=
    if I64.lt c1 0 || I64.lt c2 0 || I64.lt c3 0 then decoded 0 0
    else decoded (I64.or (I64.shl h 18) (I64.or (I64.shl c1 12) (I64.or (I64.shl c2 6) c3))) 4

/// The scalar at the cursor as a literal.
def parse_literal_cp (p : RxP) : RxStep I64 :=
    let d : RxDecoded := decode p.rest in
    if I64.beq d.width 0 then fail_at "invalid UTF-8 in pattern" p.pos (p.pos + 1)
    else RxStep.step_ok d.cp (bump p d.width)

// ─── Alternation and concatenation ───

#[terminating]
def parse_alt (p : RxP) : RxStep RxAst :=
    match parse_concat p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok first p2 => alt_more p.pos (List.cons first List.empty) p2,
    }

#[terminating]
def alt_more (start : I64) (acc : List RxAst) (p : RxP) : RxStep RxAst :=
    if is_at p "|" then alt_branch start acc (bump p 1)
    else RxStep.step_ok (finish_list start p.pos acc true) p

#[terminating]
def alt_branch (start : I64) (acc : List RxAst) (p : RxP) : RxStep RxAst :=
    match parse_concat p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok b p2 => alt_more start (List.cons b acc) p2,
    }

/// `acc` is newest-first. One item is itself; none is `empty`.
def finish_list (start : I64) (stop : I64) (acc : List RxAst) (is_alt : Bool) : RxAst :=
    match acc {
        List.empty => RxAst.empty (RegexSpan.at start stop),
        List.cons a rest =>
            if List.is_empty rest then a
            else if is_alt then RxAst.alternation (RegexSpan.at start stop) (List.reverse (List.cons a rest))
            else RxAst.concat (RegexSpan.at start stop) (List.reverse (List.cons a rest)),
    }

#[terminating]
def parse_concat (p : RxP) : RxStep RxAst :=
    let p1 : RxP := skip_ws p in
    concat_loop p1.pos List.empty p1

#[terminating]
def concat_loop (start : I64) (acc : List RxAst) (p : RxP) : RxStep RxAst :=
    let p1 : RxP := skip_ws p in
    let c : I64 := peek p1 in
    if I64.lt c 0 || I64.beq c (ch "|") || I64.beq c (ch ")") then
        RxStep.step_ok (finish_list start p1.pos acc false) p1
    else concat_atom start acc p1

#[terminating]
def concat_atom (start : I64) (acc : List RxAst) (p : RxP) : RxStep RxAst :=
    match parse_atom p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok atom p2 => concat_postfix start acc atom p2,
    }

#[terminating]
def concat_postfix (start : I64) (acc : List RxAst) (atom : RxAst) (p : RxP) : RxStep RxAst :=
    match parse_postfix atom p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok a p2 => concat_loop start (List.cons a acc) p2,
    }

// ─── Repetition ───

#[terminating]
def parse_postfix (atom : RxAst) (p : RxP) : RxStep RxAst :=
    let p1 : RxP := skip_ws p in
    let c : I64 := peek p1 in
    if I64.beq c (ch "*") then rep_check atom 0 Option.none p1
    else if I64.beq c (ch "+") then rep_check atom 1 Option.none p1
    else if I64.beq c (ch "?") then rep_check atom 0 (Option.some 1) p1
    else if I64.beq c (ch "{") then parse_counted atom p1
    else RxStep.step_ok atom p1

/// A repetition needs an expression: a standalone `(?flags)` is not one.
#[terminating]
def rep_check (atom : RxAst) (min : I64) (max : Option I64) (p : RxP) : RxStep RxAst :=
    match atom {
        RxAst.set_flags _ _ => fail_at "repetition operator missing expression" p.pos (p.pos + 1),
        _ => rep_tail atom min max (bump p 1),
    }

/// After the operator: an optional lazy `?`, and a possessive `+` refused.
#[terminating]
def rep_tail (atom : RxAst) (min : I64) (max : Option I64) (p : RxP) : RxStep RxAst :=
    let lazy : Bool := is_at p "?" in
    let p2 : RxP := if lazy then bump p 1 else p in
    if is_at p2 "+" then
        unsupported_at "possessive repetition" p2.pos (p2.pos + 1)
            "use a plain greedy repetition: this engine never backtracks, so it cannot need one"
    else
        let sp : RegexSpan := RxAst.span atom in
        let start : I64 := sp.start in
        parse_postfix (RxAst.repetition (RegexSpan.at start p2.pos) min max (Bool.not lazy) atom) p2

/// A decimal count and how many digits it had.
struct RxNum {
    value : I64,
    digits : I64,
}

def num (value : I64) (digits : I64) : RxNum :=
    let n : RxNum := { value := value, digits := digits } in n

#[terminating]
def read_decimal (acc : RxNum) (p : RxP) : RxStep RxNum :=
    let c : I64 := peek p in
    if is_digit c then
        if I64.lt 100000 acc.value then fail_at "repetition count is too large" p.pos (p.pos + 1)
        else read_decimal (num (acc.value * 10 + (c - 48)) (acc.digits + 1)) (bump p 1)
    else RxStep.step_ok acc p

/// At `{`: `{n}`, `{n,}`, `{n,m}` or `{,m}`.
#[terminating]
def parse_counted (atom : RxAst) (p : RxP) : RxStep RxAst :=
    match atom {
        RxAst.set_flags _ _ => fail_at "repetition operator missing expression" p.pos (p.pos + 1),
        _ => counted_min atom p.pos (bump p 1),
    }

#[terminating]
def counted_min (atom : RxAst) (lpos : I64) (p : RxP) : RxStep RxAst :=
    match read_decimal (num 0 0) (skip_class_ws p) {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok lo p2 => counted_after_min atom lpos lo (skip_class_ws p2),
    }

#[terminating]
def counted_after_min (atom : RxAst) (lpos : I64) (lo : RxNum) (p : RxP) : RxStep RxAst :=
    if is_at p "}" then
        if I64.beq lo.digits 0 then fail_at "repetition quantifier expects a count" lpos (p.pos + 1)
        else rep_tail atom lo.value (Option.some lo.value) (bump p 1)
    else if is_at p "," then counted_max atom lpos lo (skip_class_ws (bump p 1))
    else fail_at "unclosed counted repetition" lpos (lpos + 1)

#[terminating]
def counted_max (atom : RxAst) (lpos : I64) (lo : RxNum) (p : RxP) : RxStep RxAst :=
    match read_decimal (num 0 0) p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok hi p2 => counted_close atom lpos lo hi (skip_class_ws p2),
    }

#[terminating]
def counted_close (atom : RxAst) (lpos : I64) (lo : RxNum) (hi : RxNum) (p : RxP) : RxStep RxAst :=
    if Bool.not (is_at p "}") then fail_at "unclosed counted repetition" lpos (lpos + 1)
    else if I64.beq hi.digits 0 then
        if I64.beq lo.digits 0 then fail_at "repetition quantifier expects a count" lpos (p.pos + 1)
        else rep_tail atom lo.value Option.none (bump p 1)
    else if I64.lt hi.value lo.value then
        fail_at "invalid repetition range: the minimum exceeds the maximum" lpos (p.pos + 1)
    else rep_tail atom lo.value (Option.some hi.value) (bump p 1)

// ─── Atoms ───

#[terminating]
def parse_atom (p : RxP) : RxStep RxAst :=
    let c : I64 := peek p in
    if I64.beq c (ch "(") then parse_group p
    else if I64.beq c (ch "[") then parse_bracket_atom p
    else if I64.beq c (ch ".") then RxStep.step_ok (RxAst.dot (RegexSpan.at p.pos (p.pos + 1))) (bump p 1)
    else if I64.beq c (ch "^") then
        RxStep.step_ok (RxAst.assertion (RegexSpan.at p.pos (p.pos + 1)) RxAssert.start_line) (bump p 1)
    else if I64.beq c (ch "$") then
        RxStep.step_ok (RxAst.assertion (RegexSpan.at p.pos (p.pos + 1)) RxAssert.end_line) (bump p 1)
    else if I64.beq c (ch "\\") then parse_escape_atom p
    else if I64.beq c (ch "*") || I64.beq c (ch "+") || I64.beq c (ch "?") || I64.beq c (ch "{") then
        fail_at "repetition operator missing expression" p.pos (p.pos + 1)
    else literal_atom p

#[terminating]
def literal_atom (p : RxP) : RxStep RxAst :=
    match parse_literal_cp p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok cp p2 => RxStep.step_ok (RxAst.literal (RegexSpan.at p.pos p2.pos) cp) p2,
    }

// ─── Escapes ───

/// What a backslash escape denotes, before the caller decides whether it
/// is allowed where it appears.
type RxEsc {
    lit (cp : I64),
    perl (kind : RxPerl) (negated : Bool),
    prop (name : String) (negated : Bool),
    assertion (kind : RxAssert),
}

def parse_escape_atom (p : RxP) : RxStep RxAst :=
    match parse_escape p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok esc p2 => RxStep.step_ok (esc_to_ast (RegexSpan.at p.pos p2.pos) esc) p2,
    }

def esc_to_ast (sp : RegexSpan) (esc : RxEsc) : RxAst :=
    match esc {
        RxEsc.lit cp => RxAst.literal sp cp,
        RxEsc.perl kind negated => RxAst.perl sp kind negated,
        RxEsc.prop name negated => RxAst.unicode_class sp name negated,
        RxEsc.assertion kind => RxAst.assertion sp kind,
    }

def esc_ok (esc : RxEsc) (p : RxP) : RxStep RxEsc := RxStep.step_ok esc (bump p 1)

/// At `\`.
def parse_escape (p : RxP) : RxStep RxEsc :=
    let start : I64 := p.pos in
    let q : RxP := bump p 1 in
    let c : I64 := peek q in
    if I64.lt c 0 then fail_at "incomplete escape sequence" start (start + 1)
    else if I64.beq c (ch "d") then esc_ok (RxEsc.perl RxPerl.digit false) q
    else if I64.beq c (ch "D") then esc_ok (RxEsc.perl RxPerl.digit true) q
    else if I64.beq c (ch "s") then esc_ok (RxEsc.perl RxPerl.space false) q
    else if I64.beq c (ch "S") then esc_ok (RxEsc.perl RxPerl.space true) q
    else if I64.beq c (ch "w") then esc_ok (RxEsc.perl RxPerl.word false) q
    else if I64.beq c (ch "W") then esc_ok (RxEsc.perl RxPerl.word true) q
    else if I64.beq c (ch "p") then parse_prop start false (bump q 1)
    else if I64.beq c (ch "P") then parse_prop start true (bump q 1)
    else parse_escape_rest start c q

def parse_escape_rest (start : I64) (c : I64) (q : RxP) : RxStep RxEsc :=
    if I64.beq c (ch "b") then
        if I64.beq (peek_at q 1) (ch "{") then
            unsupported_at "\\b{...} word-boundary forms" start (start + 3) "use \\b or \\B"
        else esc_ok (RxEsc.assertion RxAssert.word_boundary) q
    else if I64.beq c (ch "B") then esc_ok (RxEsc.assertion RxAssert.not_word_boundary) q
    else if I64.beq c (ch "A") then esc_ok (RxEsc.assertion RxAssert.start_text) q
    else if I64.beq c (ch "z") then esc_ok (RxEsc.assertion RxAssert.end_text) q
    else if I64.beq c (ch "n") then esc_ok (RxEsc.lit 10) q
    else if I64.beq c (ch "t") then esc_ok (RxEsc.lit 9) q
    else if I64.beq c (ch "r") then esc_ok (RxEsc.lit 13) q
    else if I64.beq c (ch "a") then esc_ok (RxEsc.lit 7) q
    else if I64.beq c (ch "f") then esc_ok (RxEsc.lit 12) q
    else if I64.beq c (ch "v") then esc_ok (RxEsc.lit 11) q
    else if I64.beq c (ch "x") then parse_hex start 2 (bump q 1)
    else if I64.beq c (ch "u") then parse_hex start 4 (bump q 1)
    else if I64.beq c (ch "U") then parse_hex start 8 (bump q 1)
    else parse_escape_other start c q

def parse_escape_other (start : I64) (c : I64) (q : RxP) : RxStep RxEsc :=
    if is_digit c || I64.beq c (ch "k") then
        unsupported_at "backreferences" start (start + 2) linear_hint
    else if I64.beq c (ch "<") || I64.beq c (ch ">") then
        unsupported_at "\\< and \\> word-boundary assertions" start (start + 2) "use \\b"
    else if I64.beq c 32 || (I64.lt 32 c && I64.lt c 127 && Bool.not (is_alnum c)) then
        esc_ok (RxEsc.lit c) q
    else fail_at "unrecognized escape sequence" start (start + 2)

def hex_digit (c : I64) : I64 :=
    if is_digit c then c - 48
    else if I64.lt 96 c && I64.lt c 103 then c - 87
    else if I64.lt 64 c && I64.lt c 71 then c - 55
    else 0 - 1

/// After `\x`/`\u`/`\U`: exactly `width` hex digits, or `{1-8 digits}`.
def parse_hex (start : I64) (width : I64) (p : RxP) : RxStep RxEsc :=
    if is_at p "{" then hex_braced start (num 0 0) (bump p 1)
    else hex_fixed start width (num 0 0) p

#[terminating]
def hex_fixed (start : I64) (width : I64) (acc : RxNum) (p : RxP) : RxStep RxEsc :=
    if I64.beq acc.digits width then scalar_esc start acc.value p
    else
        let d : I64 := hex_digit (peek p) in
        if I64.lt d 0 then fail_at "invalid hexadecimal escape" start (p.pos + 1)
        else hex_fixed start width (num (acc.value * 16 + d) (acc.digits + 1)) (bump p 1)

#[terminating]
def hex_braced (start : I64) (acc : RxNum) (p : RxP) : RxStep RxEsc :=
    if is_at p "}" then
        if I64.beq acc.digits 0 then fail_at "empty hexadecimal escape" start (p.pos + 1)
        else scalar_esc start acc.value (bump p 1)
    else
        let d : I64 := hex_digit (peek p) in
        if I64.lt d 0 || I64.lt 7 acc.digits then fail_at "invalid hexadecimal escape" start (p.pos + 1)
        else hex_braced start (num (acc.value * 16 + d) (acc.digits + 1)) (bump p 1)

def scalar_esc (start : I64) (v : I64) (p : RxP) : RxStep RxEsc :=
    if I64.lt 1114111 v || (I64.lt 55295 v && I64.lt v 57344) then
        fail_at "escape is not a Unicode scalar value" start p.pos
    else RxStep.step_ok (RxEsc.lit v) p

/// After `\p`/`\RxP`: one letter, or `{name}` with an optional leading `^`.
def parse_prop (start : I64) (negated : Bool) (p : RxP) : RxStep RxEsc :=
    let c : I64 := peek p in
    if I64.beq c (ch "{") then prop_braced start negated List.empty (bump p 1)
    else if is_lower c || is_upper c then
        RxStep.step_ok (RxEsc.prop (String.from_list (first_byte p.rest)) negated) (bump p 1)
    else fail_at "expected a Unicode class name after \\p" start (p.pos + 1)

#[terminating]
def prop_braced (start : I64) (negated : Bool) (acc : List U8) (p : RxP) : RxStep RxEsc :=
    let c : I64 := peek p in
    if I64.lt c 0 then fail_at "unclosed Unicode class" start (start + 2)
    else if I64.beq c (ch "}") then prop_close start negated (List.reverse acc) (bump p 1)
    else match p.rest {
        List.cons b _ => prop_braced start negated (List.cons b acc) (bump p 1),
        List.empty => fail_at "unclosed Unicode class" start (start + 2),
    }

def prop_close (start : I64) (negated : Bool) (name : List U8) (p : RxP) : RxStep RxEsc :=
    match name {
        List.empty => fail_at "empty Unicode class name" start p.pos,
        List.cons b rest =>
            if I64.beq (U8.to_i64 b) (ch "^") then prop_named start (Bool.not negated) rest p
            else prop_named start negated (List.cons b rest) p,
    }

def prop_named (start : I64) (negated : Bool) (name : List U8) (p : RxP) : RxStep RxEsc :=
    match name {
        List.empty => fail_at "empty Unicode class name" start p.pos,
        _ => RxStep.step_ok (RxEsc.prop (String.from_list name) negated) p,
    }

// ─── Groups ───

/// At `(`.
#[terminating]
def parse_group (p : RxP) : RxStep RxAst :=
    if I64.lt p.limit (p.depth + 1) then RxStep.step_fail (RegexError.nest_limit p.limit)
    else
        let q : RxP := bump p 1 in
        if is_at q "?" then parse_group_ext p.pos (bump q 1)
        else
            let idx : I64 := q.caps + 1 in
            group_body p.pos (RxGroupKind.capture idx) q.ignore_ws { q with caps := idx }

/// The group's contents and its `)`. `inner_ws` is the `x` flag inside;
/// the enclosing value comes back at the `)`, which is what scopes a
/// standalone `(?x)` to the rest of its group.
#[terminating]
def group_body (lpos : I64) (kind : RxGroupKind) (inner_ws : Bool) (p : RxP) : RxStep RxAst :=
    match parse_alt { p with ignore_ws := inner_ws, depth := p.depth + 1 } {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok sub p2 => close_group lpos kind p.ignore_ws sub p2,
    }

#[terminating]
def close_group (lpos : I64) (kind : RxGroupKind) (outer_ws : Bool) (sub : RxAst) (p : RxP) : RxStep RxAst :=
    if is_at p ")" then
        let q : RxP := bump p 1 in
        RxStep.step_ok (RxAst.group (RegexSpan.at lpos q.pos) kind sub) { q with ignore_ws := outer_ws, depth := q.depth - 1 }
    else fail_at "unclosed group" lpos (lpos + 1)

/// After `(?`.
#[terminating]
def parse_group_ext (lpos : I64) (p : RxP) : RxStep RxAst :=
    let c : I64 := peek p in
    let c2 : I64 := peek_at p 1 in
    if I64.beq c (ch "P") && I64.beq c2 (ch "<") then group_name lpos List.empty (bump p 2)
    else if I64.beq c (ch "P") && I64.beq c2 (ch "=") then
        unsupported_at "backreferences" lpos (p.pos + 2) linear_hint
    else if I64.beq c (ch "P") && I64.beq c2 (ch ">") then
        unsupported_at "recursion" lpos (p.pos + 2) linear_hint
    else if I64.beq c (ch "<") && (I64.beq c2 (ch "=") || I64.beq c2 (ch "!")) then
        unsupported_at "look-behind" lpos (p.pos + 2) linear_hint
    else if I64.beq c (ch "<") then group_name lpos List.empty (bump p 1)
    else if I64.beq c (ch "=") || I64.beq c (ch "!") then
        unsupported_at "look-ahead" lpos (p.pos + 1) linear_hint
    else if I64.beq c (ch ">") then
        unsupported_at "atomic groups" lpos (p.pos + 1) linear_hint
    else parse_flags lpos List.empty false p

def is_name_byte (c : I64) (first : Bool) : Bool :=
    I64.beq c (ch "_") || is_lower c || is_upper c
        || (Bool.not first && (is_digit c || I64.beq c (ch ".") || I64.beq c (ch "[") || I64.beq c (ch "]")))

#[terminating]
def group_name (lpos : I64) (acc : List U8) (p : RxP) : RxStep RxAst :=
    let c : I64 := peek p in
    if I64.beq c (ch ">") then name_close lpos (List.reverse acc) (bump p 1)
    else if is_name_byte c (List.is_empty acc) then
        match p.rest {
            List.cons b _ => group_name lpos (List.cons b acc) (bump p 1),
            List.empty => fail_at "unclosed group name" lpos p.pos,
        }
    else if I64.lt c 0 then fail_at "unclosed group name" lpos p.pos
    else fail_at "invalid character in group name" p.pos (p.pos + 1)

#[terminating]
def name_close (lpos : I64) (name : List U8) (p : RxP) : RxStep RxAst :=
    if List.is_empty name then fail_at "empty group name" lpos p.pos
    else
        let s : String := String.from_list name in
        if name_taken s p.names then fail_at "duplicate capture group name" lpos p.pos
        else
            let idx : I64 := p.caps + 1 in
            group_body lpos (RxGroupKind.named s idx) p.ignore_ws
                { p with caps := idx, names := List.cons (Pair.pair s idx) p.names }

#[terminating]
def name_taken (s : String) (names : List (Pair String I64)) : Bool :=
    match names {
        List.empty => false,
        List.cons entry rest =>
            match entry {
                Pair.pair n _ => String.beq n s || name_taken s rest,
            },
    }

def flag_of (c : I64) : Option RxFlag :=
    if I64.beq c (ch "i") then Option.some RxFlag.case_insensitive
    else if I64.beq c (ch "m") then Option.some RxFlag.multi_line
    else if I64.beq c (ch "s") then Option.some RxFlag.dot_matches_new_line
    else if I64.beq c (ch "U") then Option.some RxFlag.swap_greed
    else if I64.beq c (ch "x") then Option.some RxFlag.ignore_whitespace
    else if I64.beq c (ch "u") then Option.some RxFlag.unicode
    else Option.none

def flag_eq (a : RxFlag) (b : RxFlag) : Bool :=
    match a {
        RxFlag.case_insensitive => match b { RxFlag.case_insensitive => true, _ => false },
        RxFlag.multi_line => match b { RxFlag.multi_line => true, _ => false },
        RxFlag.dot_matches_new_line => match b { RxFlag.dot_matches_new_line => true, _ => false },
        RxFlag.swap_greed => match b { RxFlag.swap_greed => true, _ => false },
        RxFlag.ignore_whitespace => match b { RxFlag.ignore_whitespace => true, _ => false },
        RxFlag.unicode => match b { RxFlag.unicode => true, _ => false },
    }

#[terminating]
def flag_seen (f : RxFlag) (items : List RxFlagItem) : Bool :=
    match items {
        List.empty => false,
        List.cons it rest => flag_eq it.flag f || flag_seen f rest,
    }

/// The `x` flag after applying `items` (newest-first) to `ws`.
#[terminating]
def ws_after (ws : Bool) (items : List RxFlagItem) : Bool :=
    match items {
        List.empty => ws,
        List.cons it rest =>
            match it.flag {
                RxFlag.ignore_whitespace => it.on,
                _ => ws_after ws rest,
            },
    }

/// After `(?`: flag letters, at most one `-`, then `)` or `:`. `items` is
/// newest-first; `negating` is whether a `-` has been read.
#[terminating]
def parse_flags (lpos : I64) (items : List RxFlagItem) (negating : Bool) (p : RxP) : RxStep RxAst :=
    let c : I64 := peek p in
    if I64.beq c (ch ")") then flags_close lpos items negating p true
    else if I64.beq c (ch ":") then flags_close lpos items negating p false
    else if I64.beq c (ch "-") then
        if negating then fail_at "repeated negation in flag group" p.pos (p.pos + 1)
        else parse_flags lpos items true (bump p 1)
    else match flag_of c {
        Option.none =>
            if I64.lt c 0 then fail_at "unclosed group" lpos (lpos + 1)
            else fail_at "unrecognized flag" p.pos (p.pos + 1),
        Option.some f =>
            if flag_seen f items then fail_at "duplicate flag" p.pos (p.pos + 1)
            else
                let it : RxFlagItem := { flag := f, on := Bool.not negating } in
                parse_flags lpos (List.cons it items) negating (bump p 1),
    }

#[terminating]
def flags_close (lpos : I64) (items : List RxFlagItem) (negating : Bool) (p : RxP) (standalone : Bool) : RxStep RxAst :=
    if negating && List.is_empty items then fail_at "expected a flag after '-'" p.pos (p.pos + 1)
    else if negating && Bool.not (has_negated items) then fail_at "expected a flag after '-'" p.pos (p.pos + 1)
    else if standalone then
        if List.is_empty items then fail_at "empty flag group" lpos (p.pos + 1)
        else
            let q : RxP := bump p 1 in
            RxStep.step_ok (RxAst.set_flags (RegexSpan.at lpos q.pos) (List.reverse items))
                { q with ignore_ws := ws_after q.ignore_ws items }
    else group_body lpos (RxGroupKind.non_capture (List.reverse items)) (ws_after p.ignore_ws items) (bump p 1)

/// Whether the newest item is a negated one (a `-` was followed by a flag).
def has_negated (items : List RxFlagItem) : Bool :=
    match items {
        List.empty => false,
        List.cons it _ => Bool.not it.on,
    }

// ─── Bracketed classes ───

struct RxBracket {
    negated : Bool,
    set : RxClassSet,
    span : RegexSpan,
}

#[terminating]
def parse_bracket_atom (p : RxP) : RxStep RxAst :=
    match parse_bracket p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok b p2 => RxStep.step_ok (RxAst.bracket b.span b.negated b.set) p2,
    }

/// At `[`. A `]` straight after `[` or `[^` is a literal.
#[terminating]
def parse_bracket (p : RxP) : RxStep RxBracket :=
    if I64.lt p.limit (p.depth + 1) then RxStep.step_fail (RegexError.nest_limit p.limit)
    else
        let q : RxP := bump p 1 in
        let negated : Bool := is_at q "^" in
        let q2 : RxP := if negated then bump q 1 else q in
        let inner : RxP := { q2 with depth := q2.depth + 1 } in
        if is_at inner "]" then
            bracket_union p.pos negated (List.cons (RxClassItem.lit 93) List.empty) (bump inner 1)
        else bracket_union p.pos negated List.empty inner

#[terminating]
def bracket_union (lpos : I64) (negated : Bool) (acc : List RxClassItem) (p : RxP) : RxStep RxBracket :=
    match union_loop lpos acc p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok items p2 => set_rest lpos negated (RxClassSet.items items) p2,
    }

/// Which set operator starts at the cursor, if any.
def set_op_at (p : RxP) : Option RxSetOp :=
    let c : I64 := peek p in
    let c2 : I64 := peek_at p 1 in
    if I64.beq c (ch "&") && I64.beq c2 (ch "&") then Option.some RxSetOp.intersection
    else if I64.beq c (ch "-") && I64.beq c2 (ch "-") then Option.some RxSetOp.difference
    else if I64.beq c (ch "~") && I64.beq c2 (ch "~") then Option.some RxSetOp.symmetric_difference
    else Option.none

#[terminating]
def set_rest (lpos : I64) (negated : Bool) (lhs : RxClassSet) (p : RxP) : RxStep RxBracket :=
    let p1 : RxP := skip_class_ws p in
    if is_at p1 "]" then
        let q : RxP := bump p1 1 in
        let b : RxBracket := { negated := negated, set := lhs, span := RegexSpan.at lpos q.pos } in
        RxStep.step_ok b { q with depth := q.depth - 1 }
    else match set_op_at p1 {
        Option.none => fail_at "unclosed character class" lpos (lpos + 1),
        Option.some op => set_rhs lpos negated lhs op (bump p1 2),
    }

#[terminating]
def set_rhs (lpos : I64) (negated : Bool) (lhs : RxClassSet) (op : RxSetOp) (p : RxP) : RxStep RxBracket :=
    match union_loop lpos List.empty p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok items p2 => set_rest lpos negated (RxClassSet.op op lhs (RxClassSet.items items)) p2,
    }

/// Items up to `]` or a set operator; `acc` is newest-first.
#[terminating]
def union_loop (lpos : I64) (acc : List RxClassItem) (p : RxP) : RxStep (List RxClassItem) :=
    let p1 : RxP := skip_class_ws p in
    let c : I64 := peek p1 in
    if I64.lt c 0 then fail_at "unclosed character class" lpos (lpos + 1)
    else if I64.beq c (ch "]") then RxStep.step_ok (List.reverse acc) p1
    else match set_op_at p1 {
        Option.some _ => RxStep.step_ok (List.reverse acc) p1,
        Option.none => union_item lpos acc p1,
    }

#[terminating]
def union_item (lpos : I64) (acc : List RxClassItem) (p : RxP) : RxStep (List RxClassItem) :=
    match parse_class_item p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok item p2 => union_range lpos acc item p2,
    }

/// After an item: `-` then another literal makes a range, unless the `-`
/// is last (`[a-]`) or starts `--`.
#[terminating]
def union_range (lpos : I64) (acc : List RxClassItem) (item : RxClassItem) (p : RxP) : RxStep (List RxClassItem) :=
    let p1 : RxP := skip_class_ws p in
    let next : I64 := peek_at p1 1 in
    if is_at p1 "-" && Bool.not (I64.beq next (ch "]")) && Bool.not (I64.beq next (ch "-")) then
        match item {
            RxClassItem.lit lo => range_hi lpos acc lo p1.pos (skip_class_ws (bump p1 1)),
            _ => fail_at "invalid range boundary: a class cannot start a range" p1.pos (p1.pos + 1),
        }
    else union_loop lpos (List.cons item acc) p

#[terminating]
def range_hi (lpos : I64) (acc : List RxClassItem) (lo : I64) (dash : I64) (p : RxP) : RxStep (List RxClassItem) :=
    match parse_class_item p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok item p2 => range_close lpos acc lo dash item p2,
    }

#[terminating]
def range_close (lpos : I64) (acc : List RxClassItem) (lo : I64) (dash : I64) (hi : RxClassItem) (p : RxP) : RxStep (List RxClassItem) :=
    match hi {
        RxClassItem.lit h =>
            if I64.lt h lo then fail_at "invalid class range: the start exceeds the end" dash (p.pos)
            else union_loop lpos (List.cons (RxClassItem.range lo h) acc) p,
        _ => fail_at "invalid range boundary: a class cannot end a range" dash p.pos,
    }

#[terminating]
def parse_class_item (p : RxP) : RxStep RxClassItem :=
    let c : I64 := peek p in
    if I64.beq c (ch "[") then
        if I64.beq (peek_at p 1) (ch ":") then ascii_or_nested p
        else nested_item p
    else if I64.beq c (ch "\\") then class_escape p
    else match parse_literal_cp p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok cp p2 => RxStep.step_ok (RxClassItem.lit cp) p2,
    }

#[terminating]
def nested_item (p : RxP) : RxStep RxClassItem :=
    match parse_bracket p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok b p2 => RxStep.step_ok (RxClassItem.bracket b.negated b.set) p2,
    }

def class_escape (p : RxP) : RxStep RxClassItem :=
    match parse_escape p {
        RxStep.step_fail e => RxStep.step_fail e,
        RxStep.step_ok esc p2 => class_escape_item p.pos esc p2,
    }

def class_escape_item (start : I64) (esc : RxEsc) (p : RxP) : RxStep RxClassItem :=
    match esc {
        RxEsc.lit cp => RxStep.step_ok (RxClassItem.lit cp) p,
        RxEsc.perl kind negated => RxStep.step_ok (RxClassItem.perl kind negated) p,
        RxEsc.prop name negated => RxStep.step_ok (RxClassItem.unicode name negated) p,
        RxEsc.assertion _ => fail_at "assertions are not allowed in a character class" start p.pos,
    }

// ─── ASCII classes ───

/// A `[:name:]` / `[:^name:]` shape read ahead without consuming: the
/// name, whether it is negated, and its total length in bytes.
struct RxAsciiShape {
    name : String,
    negated : Bool,
    len : I64,
}

def ascii_names : List String :=
    ["alnum", "alpha", "ascii", "blank", "cntrl", "digit", "graph",
        "lower", "print", "punct", "space", "upper", "word", "xdigit"]

#[terminating]
def name_known (s : String) (names : List String) : Bool :=
    match names {
        List.empty => false,
        List.cons n rest => String.beq n s || name_known s rest,
    }

/// At `[:`. Not the shape: a nested class that starts with `:`. The
/// shape with an unknown name: an error.
#[terminating]
def ascii_or_nested (p : RxP) : RxStep RxClassItem :=
    match ascii_shape (drop_bytes p.rest 2) {
        Option.none => nested_item p,
        Option.some shape =>
            if name_known shape.name ascii_names then
                RxStep.step_ok (RxClassItem.ascii shape.name shape.negated) (bump p (shape.len + 2))
            else fail_at "invalid ASCII class name" p.pos (p.pos + shape.len + 2),
    }

def ascii_shape (xs : List U8) : Option RxAsciiShape :=
    match xs {
        List.cons b rest =>
            if I64.beq (U8.to_i64 b) (ch "^") then ascii_name rest true 1 List.empty
            else ascii_name (List.cons b rest) false 0 List.empty,
        List.empty => Option.none,
    }

/// Lowercase letters, then `:]`. `len` counts the bytes after `[:`.
#[terminating]
def ascii_name (xs : List U8) (negated : Bool) (len : I64) (acc : List U8) : Option RxAsciiShape :=
    match xs {
        List.empty => Option.none,
        List.cons b rest =>
            let c : I64 := U8.to_i64 b in
            if is_lower c then ascii_name rest negated (len + 1) (List.cons b acc)
            else if I64.beq c (ch ":") && I64.beq (byte_at rest 0) (ch "]") && Bool.not (List.is_empty acc) then
                let s : RxAsciiShape := { name := String.from_list (List.reverse acc), negated := negated, len := len + 2 } in
                Option.some s
            else Option.none,
    }
