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
//
// No `infix (+)` override here: `init/src/prelude.mo`'s own
// `infix (+) := HAdd.add` is what `+` resolves to. This line used to
// shadow it with `infix (+) := I64.add` (the era's workaround for
// `HAdd` having no resolvable instances -- a variable-headed bridge
// instance is unkeyable by the checker's concrete-head lookup, so
// `+` on anything but `I64` was a type error and `I64` needed the
// direct spelling). With per-type `HAdd` instances in
// `init/src/number.mo`, `+` dispatches through the class for every
// width, exactly as `*` always has through `HMul`.

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

