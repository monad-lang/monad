// Init module -- the ambient re-export hub for init/ (bare `init`
// resolves to this file, see AGENTS.md's "init vs std" section).

pub use lib::id {*}
pub use lib::io {*}
pub use lib::number {*}
pub use lib::math {*}
pub use lib::string {*}
pub use lib::list {*}
// `copy`/`borrow` are not re-exported. Ambience is how the affine gate
// sees a `Copy` in each file's own scope, but it also puts copy.mo in
// every module's closure -- a cost every self-hosted sweep pays.

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

