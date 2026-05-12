
type Any {
	any {A : Type} (value: A)
}

class Functor (F: Type -> Type) {
	def map (f: A -> B) : (F A) -> F B
}

class FromListLiteral (L: Type -> Type) {
	def cons (a : A) (L A) : L A
	def empty : L A 
}

/// Hetrogenous addition class
class HAdd A B C {
	def add : A -> B -> C
}

/// Homogenous addition
class Add A {
	def add : A -> A -> A
}

instance [HAdd A A A] Add A {
	def add (a b : A) : A := HAdd.add a b
}

instance [Add A] HAdd A A A {
	def add (a b : A) : A := Add.add a b
}

/// Heterogeneous multiplication
class HMul A B C {
	def mul : A -> B -> C
}

/// Subtraction
class Sub A {
	def sub : A -> A -> A
}

class Div A {
	def div : A -> A -> A
}

infix (/) := Div.div

infix (*) := HMul.mul

infix (-) := Sub.sub


class [Functor F] Applicative (F: Type -> Type) {
    def pure : A -> F A
    def apply : F (A -> B) -> F A -> F B
}

class [Applicative M] Monad (M: Type -> Type) {
    def bind (a : M A) (f : A -> M B) : M B
    def pure : A -> M A
}

infix (>>=) := Monad.bind

type Void {}

type String {
	of_bytes U8
}

class ToString A {
	def to_string (a : A) : String
}

/// Primitive number types

type I64 {}
type I32 {}
type I16 {}
type I8 {}

type U64 {}
type U32 {}
type U16 {}
type U8 {}

type F64 {}
type F32 {}

type Unit {
	unit
}

open Unit

type Bool {
	true,
	false
}

open Bool

/// Trivially true proposition (unit in Prop)
type True : Prop {
    trivial
}

open True

/// Propositional equality: Eq A a b lives in Prop (Sort 0)
type Eq (A : Sort 1) (a : A) (b : A) : Prop {
    refl : Eq A a a
}

/// Equals
class BEq A {
	def beq : A -> A -> Bool
}

instance BEq Bool {
	def beq (a b : Bool) : Bool :=
		if a then b
		else (Bool.not b)
}

infix (==) := BEq.beq

/// Ordered comparison
class BOrd A {
	def lt (a b : A) : Bool
	def gt (a b : A) : Bool
}

type DefaultValue (A: Type) (default : A) {
	default
}

def Bool.not (b : Bool) : Bool := if b then false else true

def Bool.and (a b : Bool) : Bool := if a then b else false

infix (&&) := Bool.and

def Bool.or (a b : Bool) : Bool := if a then true else b

infix (||) := Bool.or

type Result E A {
	ok (a: A),
	err (e: E)
}

open Result

type Option A {
	some (a: A),
	none
}

open Option

def Option.get_or_default (default : A) (self : Option A) : A :=
	match self {
		some a => a,
		none => default
	}

type Nat {
	zero,
	succ (n : Nat)
}

def Nat.add (a b : Nat) : Nat :=
	match a {
		zero => b,
		succ n => Nat.succ (Nat.add n b)
	}

def Nat.sub (a b : Nat) : Nat :=
	match b {
		zero => a,
		succ n => match a {
			zero => Nat.zero,
			succ m => Nat.sub m n
		}
	}

def Nat.mul (a b : Nat) : Nat :=
	match a {
		zero => Nat.zero,
		succ n => Nat.add b (Nat.mul n b)
	}

def Nat.eq (a b : Nat) : Bool :=
	match a {
		zero => match b {
			zero => true,
			succ _ => false
		},
		succ n => match b {
			zero => false,
			succ m => Nat.eq n m
		}
	}

@[native "nat_to_string"]
def Nat.to_string (n : Nat) : String

instance BEq Nat {
	def beq (a b : Nat) : Bool := Nat.eq a b
}

instance Add Nat {
	def add (a b : Nat) : Nat := Nat.add a b
}

instance Sub Nat {
	def sub (a b : Nat) : Nat := Nat.sub a b
}

def Lens [Functor F] {F : Type -> Type} (S: Type) (T: Type) (A: Type) (B : Type) : Type :=
	(A -> F B) -> S -> F T

type List A {
	empty,
	cons (a : A) (List A) : List A
}

instance FromListLiteral List {
	def cons (a: A) (l : List A) : List A := List.cons a l
	def empty : List A := List.empty
}

def List.is_empty (self : List A) : Bool :=
	match self {
		empty => true,
		cons a tail => false
	}

def List.append (a b : List A) : List A :=
	match a {
		empty => b,
		cons el_a tail => List.cons el_a (List.append tail b)
	}

/// Append b to value a
class Append A {
	def append (a b : A) : A
}

// TODO
// instance [A] Append (List A) {
// 	def append (a b : List A) : List A = List.append a b
// }

infix (++) := Append.append

def List.first (self : List A) : Option A :=
	match self {
		empty => none,
		cons a tail => some a
	}
def List.last (self : List A) : Option A :=
	match self {
		empty => none,
		cons a tail => if List.is_empty tail
			then some a
			else List.last tail
	}
def List.flatten (self : List (List A)) : List A :=
	match self {
		empty => List.empty,
		cons list tail => List.append list (List.flatten tail)
	}

def List.tail (l : List A) : List A :=
	match l {
		empty => List.empty,
		cons a tail => tail
	}

/*
instance Functor List {
	def map (f : A -> B) (self: List A) : List B :=
		match self {
			empty => List.empty,
			cons a tail => List.cons (f a) (Functor.map f tail)
		}
}
/*
instance Applicative List {

	def pure (a : A) : List A := List.cons a List.empty

	def apply (fs : List (A -> B)) (self: List A) : List B :=
		match self {
			empty => List.empty,
			cons a tail => List.append (Functor.map (\f => f a) fs) (Applicative.apply fs tail)
		}
}*/

/*
type Vec (len : Nat) A {
	nil : Vec Nat.zero A,
	vcons (a : A) (Vec m A) : Vec (Nat.succ m) A
}*/

/// A length-indexed vector: Vec len A is a list of exactly len elements of type A
type Vec (len : Nat) A {
	nil : Vec Nat.zero A,
	cons (head : A) (tail : Vec len A) : Vec (Nat.succ len) A
}

def fun_apply (f : A -> B) (a : A) : B := f a 

infix (<|) := fun_apply

def apply_fun (a : A) (f : A -> B) : B := f a 

infix (|>) := apply_fun

/// Indexed monad: M I J A
/// I = initial index, J = final index, A = value
class IndexedMonad (M : Type -> Type -> Type -> Type) {
    def pure (a : A) : M I I A
    def bind (a : M I J A) (f : A -> M J K B) : M I K B

    /// Map across the value (preserving indices)
    def map (f : A -> B) (ma : M I J A) : M I J B :=
        bind ma (fn a => pure (f a))

    /// Sequence two actions, discarding the first value
    def and_then (first : M I J A) (second : M J K B) : M I K B :=
        bind first (fn _ => second)

    /// Lift a pure value into the indexed monad at any index
    def lift (a : A) : M I I A := pure a
}
