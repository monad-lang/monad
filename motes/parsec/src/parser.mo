/// `Parser S A`: the same parser as `S -> ParseResult S A`, as a NOMINAL
/// type so it can carry the instances a grammar wants -- `Functor`,
/// `Applicative`, `Monad` (so `do { x <- p; ... }` works), `Alternative`
/// (so `p <|> q` backtracks) and `MonadState` (so `get`/`set` read and move
/// the cursor).
///
/// The function form stays the primary one: `combinators.mo`'s structural
/// combinators take and return plain `S -> ParseResult S A` functions, the
/// 70 text grammars in the tree keep that spelling, and nothing allocates a
/// wrapper per byte. This module is the ADAPTER layer -- `Parser.of_fn` /
/// `Parser.to_fn` convert, and the instance bodies thread the cursor
/// directly. One `mk` box is allocated per combinator invocation, never per
/// character, which is the right trade for do-notation grammars (the first
/// consumer is `motes/elf`).
///
/// `type`, not `struct`: a parameterized struct's constructor does not
/// generalize its type parameters on the Rust host (`init/transformers.mo`
/// records the same choice for `StateT`), and parsec is inside that host's
/// meta-evaluation closure.
use lib::core {ParseError, ParseResult, parse_error_at}
use lib::input {Input, Text}
use lib::combinators {alt, many0, opt, separated_by, tag, tag_keyword, take_while_byte}
use lib::number {number}

open ParseResult {fail, success}
use init::transformers {ResultT, StateT}
use init::id {Id}

pub type Parser (S : Type) (A : Type) {
    mk (run : S -> ParseResult S A)
}

/// Run a parser at a cursor.
pub def Parser.run_p (p : Parser S A) (s : S) : ParseResult S A :=
    match p {
        mk f => f s
    }

/// Lift a parser FUNCTION into the instance layer -- the adapter the
/// function-shaped combinators come through.
pub def Parser.of_fn (f : S -> ParseResult S A) : Parser S A :=
    Parser.mk f

/// Back to the function the structural combinators take.
pub def Parser.to_fn (p : Parser S A) : S -> ParseResult S A :=
    Parser.run_p p

// ─── Functor ─────────────────────────────────────────────────────────
//
// Every instance body is a single expression delegating to a `*_step` def:
// the checker does not accept a multi-line lambda inside an instance body
// (`init/transformers.mo`'s `ResultT.bind_step` is the precedent).

def map_step (f : A -> B) (r : ParseResult S A) : ParseResult S B :=
    match r {
        success rem out => success rem (f out),
        fail e => fail e
    }

def map_parser_go (f : A -> B) (p : Parser S A) (s : S) : ParseResult S B :=
    map_step f (Parser.run_p p s)

pub instance Functor (Parser S) {
    def map (f : A -> B) (p : Parser S A) : Parser S B :=
        Parser.mk (map_parser_go f p)
}

// ─── Applicative ─────────────────────────────────────────────────────

def apply_step (r : ParseResult S (A -> B)) (pa : Parser S A) : ParseResult S B :=
    match r {
        success rem f => map_step f (Parser.run_p pa rem),
        fail e => fail e
    }

def pure_parser (a : A) (s : S) : ParseResult S A :=
    success s a

def apply_parser_go (pf : Parser S (A -> B)) (pa : Parser S A) (s : S) : ParseResult S B :=
    apply_step (Parser.run_p pf s) pa

pub instance Applicative (Parser S) {
    def pure (a : A) : Parser S A :=
        Parser.mk (pure_parser a)
    def apply (pf : Parser S (A -> B)) (pa : Parser S A) : Parser S B :=
        Parser.mk (apply_parser_go pf pa)
}

// ─── Monad ───────────────────────────────────────────────────────────
//
// `bind` needs no `[Copy S]`: the cursor goes to `p.run` once, and the
// continuation receives the remainder the parser itself answered. Only a
// combinator that runs BOTH branches (Alternative) has to duplicate it.

def bind_step (f : A -> Parser S B) (r : ParseResult S A) : ParseResult S B :=
    match r {
        success rem out => Parser.run_p (f out) rem,
        fail e => fail e
    }

def bind_parser_go (p : Parser S A) (f : A -> Parser S B) (s : S) : ParseResult S B :=
    bind_step f (Parser.run_p p s)

pub instance Monad (Parser S) {
    def bind (p : Parser S A) (f : A -> Parser S B) : Parser S B :=
        Parser.mk (bind_parser_go p f)
    def pure (a : A) : Parser S A :=
        Parser.mk (pure_parser a)
}

// ─── Alternative ─────────────────────────────────────────────────────
//
// `or_else` runs the right branch at the cursor the LEFT branch started
// from, which is `combinators.alt`'s own backtracking rule; `empty` fails
// at the current offset (`parse_error_at` -- the cursor itself is not
// available inside a nullary `empty`, so the error carries the position
// only).

def alt_step [Copy S] (a : Parser S A) (b : Parser S A) (s : S) : ParseResult S A :=
    alt (Parser.run_p a) (Parser.run_p b) s

def empty_parser [Input S] {S : Type} {A : Type} (s : S) : ParseResult S A :=
    fail (parse_error_at "empty" s)

pub instance [Copy S, Input S] Alternative (Parser S) {
    def empty : Parser S A :=
        Parser.mk (empty_parser)
    def or_else (a : Parser S A) (b : Parser S A) : Parser S A :=
        Parser.mk (alt_step a b)
}

// ─── MonadState ──────────────────────────────────────────────────────
//
// The parser's state IS its cursor, so `get` reads it and `set` replaces it
// (a lookahead/backtrack primitive a grammar can use directly). All five
// methods are listed -- an instance must spell out every method even where
// the class supplies a default.

def state_get [Copy S] {S : Type} (s : S) : ParseResult S S :=
    success s s

def state_set {S : Type} (s2 : S) (_s : S) : ParseResult S Unit :=
    success s2 Unit.unit

def state_modify_get {S : Type} {A : Type} (f : S -> Pair S A) (s : S) : ParseResult S A :=
    match f s {
        Pair.pair s2 a => success s2 a
    }

pub instance [Copy S] MonadState (Parser S) {
    def get : Parser S S :=
        Parser.mk (state_get)
    def set (s2 : S) : Parser S Unit :=
        Parser.mk (state_set s2)
    def modify_get (f : S -> Pair S A) : Parser S A :=
        Parser.mk (state_modify_get f)
    def modify (f : S -> S) : Parser S Unit :=
        Parser.mk (state_modify_set f)
    def get_map (f : S -> A) : Parser S A :=
        Parser.mk (state_get_map f)
}

def state_modify_set {S : Type} (f : S -> S) (s : S) : ParseResult S Unit :=
    success (f s) Unit.unit

def state_get_map [Copy S] {S : Type} {A : Type} (f : S -> A) (s : S) : ParseResult S A :=
    success s (f s)

// ─── Adapters for the function-shaped combinators ────────────────────
//
// A grammar written in `Parser` form needs the combinators as values; each
// of these is a type adapter (`Parser.of_fn` around the function form), not
// a reimplementation.

pub def Parser.alt [Copy S] (a : Parser S A) (b : Parser S A) : Parser S A :=
    Parser.of_fn (alt (Parser.run_p a) (Parser.run_p b))

pub def Parser.many0 [Copy S] (p : Parser S A) : Parser S (List A) :=
    Parser.of_fn (many0 (Parser.run_p p))

pub def Parser.opt [Copy S] (p : Parser S A) : Parser S (Option A) :=
    Parser.of_fn (opt (Parser.run_p p))

pub def Parser.separated_by [Copy S] (sep : Parser S A) (p : Parser S B) : Parser S (List B) :=
    Parser.of_fn (separated_by (Parser.run_p sep) (Parser.run_p p))

/// Text literals as parser values (`tag`/`tag_keyword` are the monomorphic
/// text primitives; a `Parser Text` grammar uses these).
pub def Parser.tag (lit : String) : Parser Text String :=
    Parser.of_fn (tag lit)

pub def Parser.tag_keyword (lit : String) : Parser Text String :=
    Parser.of_fn (tag_keyword lit)

pub def Parser.take_while_byte (pred : U8 -> Bool) : Parser Text String :=
    Parser.of_fn (take_while_byte pred)

pub def Parser.number : Parser Text I64 :=
    Parser.of_fn number

// ─── The transformer bridge ──────────────────────────────────────────
//
// `Parser S A` is the same thing as `StateT S (ResultT ParseError Id) A` --
// a cursor threaded through an error-carrying identity monad -- so the two
// convert losslessly. The bridge is what lets a parser sit inside a real
// transformer stack, and it is the executable statement that the parser's
// Monad IS the StateT/ResultT Monad (`init/transformers.mo`).
//
// `Parser` itself is NOT implemented as the stack: the direct newtype avoids
// a closure layer per bind in the parse path. The equivalence is pinned by
// `parser_tests.mo`'s round trip.

pub def Parser.to_state_result (p : Parser S A) : StateT S (ResultT ParseError Id) A :=
    StateT.mk (state_result_of p)

def state_result_of (p : Parser S A) (s : S) : ResultT ParseError Id (Pair S A) :=
    ResultT.mk (Id.id (outcome_to_result (Parser.run_p p s)))

def outcome_to_result (r : ParseResult S A) : Result ParseError (Pair S A) :=
    match r {
        success rem out => Result.ok (Pair.pair rem out),
        fail e => Result.err e
    }

pub def Parser.from_state_result (m : StateT S (ResultT ParseError Id) A) : Parser S A :=
    Parser.mk (Parser.from_state_run (StateT.run m))

def Parser.from_state_run (run : S -> ResultT ParseError Id (Pair S A)) (s : S) : ParseResult S A :=
    result_to_outcome (id_unwrap (ResultT.run (run s)))

def id_unwrap (r : Id (Result ParseError (Pair S A))) : Result ParseError (Pair S A) :=
    match r {
        Id.id inner => inner
    }

def result_to_outcome (r : Result ParseError (Pair S A)) : ParseResult S A :=
    match r {
        Result.ok p => match p { Pair.pair s a => success s a },
        Result.err e => fail e
    }
