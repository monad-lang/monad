class Semigroup A {
  def combine (a b : A) : A
}

class [Semigroup A] Monoid A {
  def mempty (u : Unit) : A
}

instance {A : Type} Semigroup (List A) {
  def combine (a b : List A) : List A := List.append a b
}

instance {A : Type} Monoid (List A) {
  def mempty (u : Unit) : List A := List.empty
}

instance Semigroup String {
  def combine (a b : String) : String := String.concat a b
}

instance Monoid String {
  def mempty (u : Unit) : String := ""
}

class Foldable (T : Type -> Type) {
  def foldr (f : A -> B -> B) (z : B) (t : T A) : B
  def foldl (f : B -> A -> B) (z : B) (t : T A) : B
}

class [Foldable T] Traversable (T : Type -> Type) {
  def traverse [Applicative F] {A B : Type} (f : A -> F B) (t : T A) : F (T B)
}

instance Foldable List {
  def foldr (f : A -> B -> B) (z : B) (t : List A) : B :=
    match t {
      empty => z,
      cons a tail => (f a (Foldable.foldr f z tail) : B)
    }

  def foldl (f : B -> A -> B) (z : B) (t : List A) : B :=
    match t {
      empty => z,
      cons a tail => (Foldable.foldl f (f z a) tail : B)
    }
}

instance Foldable Option {
  def foldr (f : A -> B -> B) (z : B) (t : Option A) : B :=
    match t {
      none => z,
      some a => f a z
    }

  def foldl (f : B -> A -> B) (z : B) (t : Option A) : B :=
    match t {
      none => z,
      some a => f z a
    }
}
