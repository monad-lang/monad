class HMul A B C {
	def mul : A -> B -> C
}

infix (*) := HMul.mul

class Sub A  {
	def sub : A -> A -> A
}

infix (-) := Sub.sub

@[native num_add]
def I64.add (a b : I64) : I64

@[native num_sub]
def I64.sub (a b : I64) : I64

@[native num_mul]
def I64.mul (a b : I64) : I64

instance HMul I64 I64 I64 {
	def mul (a b : I64) : I64 := I64.mul a b
}

@[native num_to_str]
def I64.to_string (a : I64) : String

instance ToString I64 {
	def to_string (i : I64) : String := I64.to_string i
}

instance Sub I64 {
	def sub (a b : I64) : I64 := I64.sub a b
}

@[native i64_eq]
def I64.beq (a b : I64) : Bool 

instance BEq I64 {
	def beq (a b : I64) : Bool := I64.beq a b
}
