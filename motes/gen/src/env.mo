// A binder stack for generated de Bruijn terms.
//
// Indices are invisible in the output (the printer shows names), so this
// module exists to keep a generator from computing them by hand: `ref`
// looks a name up, `lam` extends the stack for the body it wraps.

use lang::types {DebugName, Identifier, Term, binder_explicit, sentinel}

/// The names in scope, innermost first.
pub struct Env {
    names : List String,
}

pub def Env.empty : Env := { names := List.empty }

/// Extend with one binder: the body of a `lam` over `name`.
pub def Env.bind (env : Env) (name : String) : Env :=
    { names := List.cons name env.names }

/// The de Bruijn index of `name`, or none when it is not bound.
pub def Env.index (env : Env) (name : String) : Option I64 :=
    index_go env.names name 0

#[partial]
def index_go (names : List String) (name : String) (i : I64) : Option I64 :=
    match names {
        List.empty => Option.none,
        List.cons hd tl =>
            if String.beq hd name
            then Option.some i
            else index_go tl name (I64.add i 1),
    }

/// A reference to `name` from inside `env`: its index when bound,
/// otherwise a free reference to a global (`U32.lt`, `Option.none`).
pub def Gen.ref (env : Env) (name : String) : Term :=
    match Env.index env name {
        Option.some idx => Term.var idx (DebugName.named (Identifier.id name)),
        Option.none => Term.var sentinel (DebugName.named (Identifier.id name)),
    }

/// `fn (name : type_) => body`, with `body_of` given the extended env.
pub def Gen.lam (env : Env) (name : String) (type_ : Term) (body_of : Env -> Term) : Term :=
    Term.lam (binder_explicit (DebugName.named (Identifier.id name))) type_ (body_of (Env.bind env name))
