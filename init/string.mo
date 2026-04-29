
/// String functions

use math

@[native string_eq]
def String.beq (a b : String) : Bool

@[native string_concat]
def String.concat (a b : String) : String

@[native string_length]
def String.length (s : String) : I64

@[native string_get]
def String.get (s : String) (i : I64) : Option U8

instance BEq String {
	def beq (a b : String) : Bool := String.beq a b
}

instance ToString String {
	def to_string (s : String) : String := s
}

instance Add String {
	def add (a b : String) : String := String.concat a b
}

infix (++) := String.concat

def String.is_empty (s : String) : Bool :=
	I64.beq (String.length s) 0
