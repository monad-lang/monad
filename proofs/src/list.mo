// Basic `List` theorems, by structural induction through an explicit
// eliminator with a named family (see nat.mo's header for why).

use proofs::equiv {Path}
use proofs::paths {refl, ap}

/// Structural induction over `List A`, into an arbitrary type family.
#[proof]
pub def list_elim {A : Type} (P : List A -> Type) (hn : P List.empty)
    (hc : (x : A) -> (t : List A) -> P t -> P (List.cons x t))
    (xs : List A) : P xs :=
    match xs {
        List.empty => hn,
        List.cons x t => hc x t (list_elim P hn hc t),
    }

/// `xs ++ [] = xs`.
#[proof]
pub def append_nil_fam {A : Type} (xs : List A) : Type :=
    Path (List A) (List.append xs List.empty) xs

#[proof]
pub def append_nil {A : Type} (xs : List A) :
    Path (List A) (List.append xs List.empty) xs :=
    list_elim append_nil_fam (refl List.empty)
        (fn x t ih => ap (fn tl => List.cons x tl) ih) xs

/// `[] ++ xs = xs` holds definitionally.
#[proof]
pub def nil_append {A : Type} (xs : List A) :
    Path (List A) (List.append List.empty xs) xs :=
    refl xs

/// Append is associative.
#[proof]
pub def append_assoc_fam {A : Type} (ys : List A) (zs : List A) (xs : List A) : Type :=
    Path (List A) (List.append (List.append xs ys) zs)
        (List.append xs (List.append ys zs))

#[proof]
pub def append_assoc {A : Type} (xs : List A) (ys : List A) (zs : List A) :
    Path (List A) (List.append (List.append xs ys) zs)
        (List.append xs (List.append ys zs)) :=
    list_elim (append_assoc_fam ys zs) (refl (List.append ys zs))
        (fn x t ih => ap (fn tl => List.cons x tl) ih) xs
