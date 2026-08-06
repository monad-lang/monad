/// Indexed Monads Example: Protocol state tracking
/// Demonstrates the IndexedMonad class with phantom type indices

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

#[test]
def test_indexed_monad_compiles : Bool :=
    true
