/// Indexed Monads Example: Protocol state tracking
/// Demonstrates the IndexedMonad class with phantom type indices
#![mote { name := "indexed_monads" }]


// Protocol states
type Init {}
type Ready {}
type Done {}

// Indexed protocol type — indices are phantom type markers
type Protocol (I : Type) (J : Type) (A : Type) {
    protocol (val : A)
}

instance IndexedMonad Protocol {
    def pure (a : A) : Protocol I I A :=
        Protocol.protocol a

    def bind (a : Protocol I J A) (f : A -> Protocol J K B) : Protocol I K B :=
        Protocol.protocol (match a { protocol va => match f va { protocol vb => vb } })

    def map (f : A -> B) (ma : Protocol I J A) : Protocol I J B :=
        match ma {
            protocol va => Protocol.protocol (f va)
        }

    def and_then (first : Protocol I J A) (second : Protocol J K B) : Protocol I K B :=
        match first {
            protocol _ => match second { protocol vb => Protocol.protocol vb }
        }

    def lift (a : A) : Protocol I I A :=
        Protocol.protocol a
}

/// Do-notation on `Protocol Init Init` via a `Monad (Protocol I I)` instance.
/// The generic bridge instance `instance {I : Type} [IndexedMonad M] Monad (M I I)`
/// in `init/prelude.mo` is the correct design, but the current type checker's
/// `KnownInstances` lookup can't match a variable-head instance against a concrete
/// type (it keys on `(class, type_head)`, and the bridge has `M` as its head, not
/// `Protocol`). This direct instance works around that limitation —
/// `term_head_path(Protocol I I)` returns `Protocol`, which `KnownInstances` finds.
instance Monad (Protocol I I) {
    def pure (a : A) : Protocol I I A :=
        Protocol.protocol a
    def bind (a : Protocol I I A) (f : A -> Protocol I I B) : Protocol I I B :=
        Protocol.protocol (match a { protocol va => match f va { protocol vb => vb } })
}

/// Unwrap a `Protocol` value to extract its inner value.
def Protocol.unwrap (a : Protocol I J A) : A :=
    match a { protocol va => va }

/// Do-notation with `bind` — separated into its own def to avoid a
/// `MatchTraversalMismatch` (a known checker/lowering desync that occurs
/// when `Monad.bind` dictionary-projection matches from do-notation are
/// interleaved with other class-method or pattern-match resolutions in
/// the same def).
def do_bind_result : I64 :=
    Protocol.unwrap (do {
        let x <- Protocol.protocol 42;
        return (x + 1)
    } : Protocol Init Init I64)

#[test]
def test_indexed_monad_compiles : Bool :=
    true

/// Do-notation with `return` only (exercises `Monad.pure`).
#[test]
def test_indexed_monad_do_pure : Bool :=
    match (do { return 42 } : Protocol Init Init I64) {
        protocol v => v == 42
    }

/// Do-notation with `bind` (exercises `Monad.bind` + `Monad.pure`).
/// The do-block is in a separate `def` to avoid `MatchTraversalMismatch`.
#[test]
def test_indexed_monad_do_bind : Bool :=
    do_bind_result == 43
