// Init module -- the ambient re-export hub for init/ (bare `init`
// resolves to this file, see AGENTS.md's "init vs std" section).

pub use lib::id {*}
pub use lib::io {*}
pub use lib::number {*}
pub use lib::math {*}
pub use lib::string {*}
pub use lib::list {*}
// `Copy` is re-exported alongside the rest because under Design B
// (branch `experiment/qtt-affine`) its instances are the only route to
// unrestricted use, so they must be ambient: a file that never
// declares `use init::copy` still has I64 binders, and the affine
// gate consults the file's own scope. Without this line the gate
// fail-closed every binder in every module outside init's closure
// that didn't import copy.mo by hand (measured: 0 candidates).
pub use lib::copy {*}
// `Clone` is ambient for the same reason as `Copy`: the affine
// diagnostic offers `Clone.clone` as a remedy in every file, so the
// class and its instances have to be in scope without an import.
pub use lib::clone {*}
// `Shared` is deliberately NOT re-exported: a file that uses
// `Shared.of` must name it, and one that never does holds no shared
// read for the gate to recognise either way.

infix (+) := I64.add

class From T A {
 def from (t: T): A
}

pub instance [BEq A] BEq (Option A) {
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

