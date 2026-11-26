/// Tests for `Parser S A` (`parser.mo`): the instances a grammar uses --
/// `Functor`, `Applicative`, `Monad` (do notation), `Alternative` (`<|>`),
/// `MonadState` -- and the `StateT S (ResultT ParseError Id)` bridge.
///
/// A separate file so the tests are discovered: a `#[test]` inside a module
/// re-exported by `lib.mo` is not swept (`AGENTS.md`).
use lib::core {ParseError, ParseResult, Text}
use lib::input {Input}
use lib::parser {Parser}
use init::transformers {ResultT, StateT}
use init::id {Id}
use lib::combinators {alt, tag}
open ParseResult {fail, success}

def run_text (p : Parser Text A) (s : String) : ParseResult Text A :=
    Parser.run_p p (Text.of_string s)

/// One character, as a `Parser` value -- what a grammar's leaves look like in
/// this layer.
def p_char : Parser Text U8 :=
    Parser.mk (fn s => match Input.input_head s {
        Option.none => fail (ParseError.custom "eof" s),
        Option.some b => success (Input.input_advance 1 s) b
    })

def p_none : Parser Text U8 :=
    Parser.mk (fn s => fail (ParseError.custom "none" s))

#[test]
def test_do_block_threads_the_cursor : Bool :=
    let p : Parser Text (Pair U8 U8) := do {
        let a <- p_char;
        let b <- p_char;
        return (Pair.pair a b)
    } in
    match run_text p "xy" {
        success rem out => match out {
            Pair.pair a b => U8.beq a 120u8 && U8.beq b 121u8 && I64.beq (Text.offset rem) 2
        },
        fail _ => false
    }

/// `<|>` runs the right branch from the cursor the LEFT branch started at,
/// which is `combinators.alt`'s own rule.
#[test]
def test_or_else_backtracks : Bool :=
    let p : Parser Text U8 := p_none <|> p_char in
    match run_text p "z" {
        success rem out => U8.beq out 122u8 && I64.beq (Text.offset rem) 1,
        fail _ => false
    }

/// `Alternative.empty` fails at the CURRENT cursor, carrying its offset.
#[test]
def test_empty_fails_at_the_current_offset : Bool :=
    let p : Parser Text U8 := Alternative.empty in
    let start : Text := Input.input_advance 3 (Text.of_string "abcdef") in
    match Parser.run_p p start {
        success _ _ => false,
        fail e => I64.beq (ParseError.error_offset e) 3
    }

#[test]
def test_functor_map : Bool :=
    let p : Parser Text I64 := Functor.map (fn (b : U8) => 1) p_char in
    match run_text p "q" {
        success _ out => I64.beq out 1,
        fail _ => false
    }

/// `MonadState.get` hands the grammar its own cursor.
#[test]
def test_monad_state_get : Bool :=
    let p : Parser Text I64 := do {
        let t <- MonadState.get;
        return (Text.offset t)
    } in
    match Parser.run_p p (Input.input_advance 1 (Text.of_string "ab")) {
        success _ out => I64.beq out 1,
        fail _ => false
    }

/// `MonadState.set` REPLACES the cursor: a grammar can use it to backtrack
/// past a lookahead deliberately.
#[test]
def test_monad_state_set_backtracks : Bool :=
    let p : Parser Text U8 := do {
        let _ <- p_char;
        let start : Text <- MonadState.get;
        let _ <- p_char;
        let _ <- MonadState.set start;
        return 7u8
    } in
    match run_text p "xy" {
        // `start` is the cursor AFTER the first character, so `set` rewinds
        // to offset 1 -- not to the beginning.
        success rem out => U8.beq out 7u8 && I64.beq (Text.offset rem) 1,
        fail _ => false
    }

/// The `Parser` form and the function form must compose to the same answer:
/// `Parser.alt` is an adapter, not a reimplementation.
#[test]
def test_parser_alt_agrees_with_function_alt : Bool :=
    let a : Parser Text String := Parser.tag "foo" in
    let b : Parser Text String := Parser.of_fn (tag "bar") in
    match run_text (a <|> b) "barbaz" {
        success rem out => String.beq out "bar" && I64.beq (Text.offset rem) 3,
        fail _ => false
    }

#[test]
def test_monad_bind_agrees_with_bind_parse : Bool :=
    let p : Parser Text String := do {
        let a <- Parser.tag "a";
        let b <- Parser.tag "b";
        return (String.concat a b)
    } in
    match run_text p "abc" {
        success rem out => String.beq out "ab" && I64.beq (Text.offset rem) 2,
        fail _ => false
    }

/// The bridge: `Parser S A` and `StateT S (ResultT ParseError Id) A` are the
/// same thing, both ways, on success and on failure.
#[test]
def test_transformer_bridge_round_trips_success : Bool :=
    let p : Parser Text String := Parser.tag "ab" in
    let q : Parser Text String := Parser.from_state_result (Parser.to_state_result p) in
    match run_text q "abcd" {
        success rem out => String.beq out "ab" && I64.beq (Text.offset rem) 2,
        fail _ => false
    }

#[test]
def test_transformer_bridge_round_trips_failure : Bool :=
    let p : Parser Text String := Parser.tag "zz" in
    let q : Parser Text String := Parser.from_state_result (Parser.to_state_result p) in
    match run_text q "abcd" {
        success _ _ => false,
        fail e => I64.beq (ParseError.error_offset e) 0
    }

/// A `Parser` can also be USED through its transformer form directly --
/// `StateT.run` gives the cursor/output pair, `ResultT.run` the error.
#[test]
def test_transformer_form_runs_a_parser : Bool :=
    let p : Parser Text String := Parser.tag "hi" in
    let m : StateT Text (ResultT ParseError Id) String := Parser.to_state_result p in
    match ResultT.run (StateT.run m (Text.of_string "hi!")) {
        Id.id r => match r {
            Result.ok pr => match pr {
                Pair.pair rem out => String.beq out "hi" && I64.beq (Text.offset rem) 2
            },
            Result.err _ => false
        }
    }

/// The function-shaped combinators are still the primary API, and `alt` from
/// `combinators.mo` is what the instance delegates to.
#[test]
def test_function_alt_still_works : Bool :=
    match alt (tag "a") (tag "b") (Text.of_string "b") {
        success rem out => String.beq out "b" && I64.beq (Text.offset rem) 1,
        fail _ => false
    }
