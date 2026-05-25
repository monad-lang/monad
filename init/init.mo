// Init module

pub use id
pub use io
pub use number
pub use math
pub use string

infix (+) := I64.add

class From T A {
 def from (t: T): A
}

/// Get the element at index
def List.get (index : I64) (l : List A) : Option A :=
	// TODO fails to parse properly
	let b := index == 0 in
	if b
	then
	(match l {
		empty => none,
		cons a tail => some a
	})
	else (let b2 := BOrd.gt index 0 in
	if b2
	then match l {
		empty => none,
		cons a tail => List.get (I64.sub index 1) tail
	}
	else none)


instance [BEq A] BEq (Option A) {
	def beq (oa ob : Option A) : Bool :=
		match oa {
			some a => match ob {
				some b => a == b,
				none => false
			},
			none => match ob {
				some b => false,
				none => true,
			}
		}
}

