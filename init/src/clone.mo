/// `Clone` — the **explicit** copy.
///
/// `Copy` duplicates the representation implicitly whenever a binder is used
/// more than once; `Clone` is the opposite: a user-visible call that produces
/// a NEW owned value. It is never inserted by the checker — an implicit deep
/// copy would hide its own cost — so a program that wants two owners writes
/// `Clone.clone` (or gets one from `#[derive Clone]`).
///
/// ## Why the source is a `Shared A`
///
/// Cloning must not consume what it copies. Taking `Shared A` puts the source
/// in the read position the affine rule already knows about, so
/// `Clone.clone (Shared.of x)` leaves `x` usable, while the result is a fresh
/// value that can be stored or returned. That is the sanctioned way to
/// duplicate a value that has no `Copy` instance, and the escape hatch the
/// `Shared.get` view rule needs (a view may not be stored; a clone may).
///
/// ## What has an instance, and what deliberately does not
///
/// Scalars, `String` and the structural containers are here. **Mutable state
/// and handles are not** — `ByteBuf`, `Ref`, `Array`, `Channel`, `FdStream`,
/// `Ptr` and function types have no instance, because a deep copy of a
/// mutable cell or a session handle is either a second independent resource
/// (surprising) or impossible. A caller who wants that says so with its own
/// instance, in full view.
///
/// Instances may be constrained (`[Clone A] Clone (List A)`) — ordinary class
/// dispatch, unlike `Copy`, whose resolver deliberately refuses constrained
/// parametric instances (`lang/typecheck/copy_class.mo`).
use init::shared {Shared, Shared.get}

pub class Clone (A : Type) {
    def clone (x : Shared A) : A
}

// ---------- Builtin instances ----------
//
// Their bodies are the identity: every one of these types is `Copy` and
// immutable, so the "new value" is the same immutable value. They exist so a
// constrained container instance (`Clone (List I64)`) resolves.

pub instance Clone I64 {
    def clone (x : Shared I64) : I64 := Shared.get x
}

pub instance Clone U64 {
    def clone (x : Shared U64) : U64 := Shared.get x
}

pub instance Clone I32 {
    def clone (x : Shared I32) : I32 := Shared.get x
}

pub instance Clone U32 {
    def clone (x : Shared U32) : U32 := Shared.get x
}

pub instance Clone U8 {
    def clone (x : Shared U8) : U8 := Shared.get x
}

pub instance Clone F64 {
    def clone (x : Shared F64) : F64 := Shared.get x
}

pub instance Clone Bool {
    def clone (x : Shared Bool) : Bool := Shared.get x
}

pub instance Clone Char {
    def clone (x : Shared Char) : Char := Shared.get x
}

pub instance Clone Unit {
    def clone (x : Shared Unit) : Unit := Shared.get x
}

/// A `String` is an immutable shared pointer, so its clone is the same
/// pointer — a copy of the bytes is not wanted here (`Copy` already covers
/// sharing, and `String.concat ""` is how a caller asks for real bytes).
pub instance Clone String {
    def clone (x : Shared String) : String := Shared.get x
}

// ---------- Structural instances ----------
//
// Every reachable non-`Copy` node is rebuilt into fresh storage. Match
// binders are views of the source, re-wrapped by `Shared.of` on the way into
// the recursive clone — the read position the view rule permits.

pub instance [Clone A, Clone B] Clone (Pair A B) {
    def clone (p : Shared (Pair A B)) : Pair A B :=
        match Shared.get p {
            Pair.pair a b =>
                Pair.pair (Clone.clone (Shared.of a)) (Clone.clone (Shared.of b)),
        }
}

pub instance [Clone A] Clone (Option A) {
    def clone (o : Shared (Option A)) : Option A :=
        match Shared.get o {
            Option.some a => Option.some (Clone.clone (Shared.of a)),
            Option.none => Option.none,
        }
}

pub instance [Clone E, Clone A] Clone (Result E A) {
    def clone (r : Shared (Result E A)) : Result E A :=
        match Shared.get r {
            Result.ok a => Result.ok (Clone.clone (Shared.of a)),
            Result.err e => Result.err (Clone.clone (Shared.of e)),
        }
}

pub instance [Clone A] Clone (List A) {
    def clone (xs : Shared (List A)) : List A :=
        match Shared.get xs {
            List.empty => List.empty,
            List.cons a rest =>
                List.cons (Clone.clone (Shared.of a)) (Clone.clone (Shared.of rest)),
        }
}
