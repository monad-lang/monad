// A dictionary-capturing closure stored in a constructor, then applied
// through a match. The Rust host's interpreter runs it; the compiled
// backends used to resolve the captured `[Monad M]` dictionary to the
// prelude's catch-all bridge (`dict-capturing-closure-segfault`), whose
// layout does not match `Monad IO`, and crashed natively (SIGSEGV) and on
// the web profile (a trap in `apply_closure_raw1`). Prints 42 and exits 0.

#![mote { name := "dict_closure_probe" }]

type Holder (M : Type -> Type) A {
    holder (f : A -> M A)
}

def holder_pure [Monad M] {A : Type} (a : A) : Holder M A :=
    Holder.holder (fn (x : A) => Monad.pure a)

def holder_run [Monad M] {A : Type} (h : Holder M A) (a : A) : M A :=
    match h { Holder.holder f => f a }

def main (args : List String) : IO I64 := do {
    let h : Holder IO I64 := holder_pure 42;
    let v <- holder_run h 1;
    let _ <- IO.println (I64.to_string v);
    return 0
}
