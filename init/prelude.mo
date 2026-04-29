
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
class [HAdd A A A] Add A {
	def add : A -> A -> A
}

/// Heterogeneous multiplication
class HMul A B C {
	def mul : A -> B -> C
}

/// Subtraction
class Sub A {
	def sub : A -> A -> A
}

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

infix (++) := append

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

def fun_apply (f : A -> B) (a : A) : B := f a 

infix (<|) := fun_apply

def apply_fun (a : A) (f : A -> B) : B := f a 

infix (|>) := apply_fun
