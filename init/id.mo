/// Identity monad: wraps a pure value, enabling do notation in pure contexts.
type Id A {
    id (a : A)
}
open Id

instance Functor Id {
    def map (f : A -> B) (a : Id A) : Id B :=
        match a { id a => id (f a) }
}

instance Applicative Id {
    def pure (a : A) : Id A := id a

    def apply (f : Id (A -> B)) (a : Id A) : Id B :=
        match f { id f2 => match a { id a2 => id (f2 a2) } }
}

instance Monad Id {
    def pure (a : A) : Id A := id a

    def bind (a : Id A) (f : A -> Id B) : Id B :=
        match a { id a => f a }
}

/// Unwrap an Id monad value, extracting the underlying pure value.
def Id.run (a : Id A) : A :=
    match a { id a => a }
