// Init module -- the ambient re-export hub for init/ (bare `init`
// resolves to this file, see AGENTS.md's "init vs std" section).

pub use id {*}
pub use io {*}
pub use number {*}
pub use math {*}
pub use string {*}
pub use list {*}

infix (+) := I64.add

class From T A {
 def from (t: T): A
}

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

