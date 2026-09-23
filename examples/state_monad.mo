/// State monad example: a simple counter using the MonadState class
#![mote { name := "state_monad" }]


/// State monad wrapping a state-transformer function S -> (S, A)
type State S A {
    state (run : S -> Pair S A)
}

/// Run a State computation with an initial state, returning (final_state, result)
def State.run (m : State S A) (s : S) : Pair S A :=
    match m { state r => r s }

/// Helper: bind step — apply run to state, then run continuation on the result
def State.bind_step (ma : State S A) (f : A -> State S B) (s : S) : Pair S B :=
    match State.run ma s {
        Pair.pair ns a => State.run (f a) ns
    }

instance Monad (State S) {
    def pure (a : A) : State S A :=
        State.state (fn s => Pair.pair s a)
    def bind (ma : State S A) (f : A -> State S B) : State S B :=
        State.state (State.bind_step ma f)
}

instance MonadState (State I64) {
    def get : State I64 I64 :=
        State.state (fn s => Pair.pair s s)
    def set (new_s : I64) : State I64 Unit :=
        State.state (fn _ => Pair.pair new_s unit)
    def modify_get (f : I64 -> Pair I64 A) : State I64 A :=
        State.state (fn s => f s)
    def modify (f : I64 -> I64) : State I64 Unit :=
        State.state (fn s => Pair.pair (f s) unit)
    def get_map (f : I64 -> A) : State I64 A :=
        State.state (fn s => Pair.pair s (f s))
}

/// Increment the counter and return the old value
def increment : State I64 I64 :=
    MonadState.modify_get (fn n => Pair.pair (n + 1) n)

/// Three increments via explicit bind chain (avoiding do-notation MatchTraversalMismatch)
def three_increments : State I64 Unit :=
    Monad.bind increment (fn _ =>
    Monad.bind increment (fn _ =>
    Monad.bind increment (fn _ =>
    Monad.pure unit)))

/// Run a sequence of increments and return the final state
def run_counter : I64 :=
    match State.run three_increments 0 {
        Pair.pair final_state _ => final_state
    }

#[test]
def test_state_pure : Bool :=
    match State.run (Monad.pure 42 : State I64 I64) 0 {
        Pair.pair s a => (s == 0) && (a == 42)
    }

#[test]
def test_state_get : Bool :=
    match State.run (MonadState.get : State I64 I64) 7 {
        Pair.pair s a => (s == 7) && (a == 7)
    }

#[test]
def test_state_set : Bool :=
    match State.run (MonadState.set 99 : State I64 Unit) 0 {
        Pair.pair s _ => s == 99
    }

#[test]
def test_state_modify_get : Bool :=
    match State.run (MonadState.modify_get (fn n => Pair.pair (n + 1) (n + 1)) : State I64 I64) 5 {
        Pair.pair s a => (s == 6) && (a == 6)
    }

#[test]
def test_counter : Bool :=
    run_counter == 3
