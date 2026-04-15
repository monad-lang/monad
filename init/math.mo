class HMul A B C {
	def mul : A -> B -> C
}

infix:20 (*) := HMul.mul