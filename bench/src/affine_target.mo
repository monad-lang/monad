/// The elaboration target for `bench/src/affine_report.mo`.
///
/// One file that pulls in both halves the report needs in a single
/// scope: the compiler's own closure (`lang`, which is what is being
/// measured) and the `Copy` class with its builtin instances
/// (`init::copy`, which is what the measurement resolves against).
///
/// It exists because `init/src/copy.mo` is deliberately NOT re-exported
/// from `init/src/lib.mo`. Making `Copy` ambient corpus-wide is a real
/// decision — it puts the class and its `copy` method into every
/// importer's namespace — and it belongs to the milestone where
/// enforcement actually lands, not to an experiment still deciding
/// whether enforcement is viable. Loading it here gives the report a
/// scope containing the instances without perturbing anything the
/// corpus compiles. `init::borrow` rides along for the same reason
/// (B1, M2.5): the `Copy (Borrow A)` instance must be in this same
/// closure for the report to see it.
///
/// **A predicted shortcut that did not work, recorded so it is not
/// retried.** Moving `Copy` into `init` was expected to retire this
/// file, on the reasoning that every mote already depends on `init`.
/// It does not: *depending on* a mote does not load its modules, and
/// instances reach a scope only by being in the elaborated dependency
/// CLOSURE. Nor does importing `init::copy` from
/// `lang/typecheck/copy_class.mo` help — `lang/src/lib.mo` re-exports a
/// deliberately small surface (`types`, `module`, `pretty`,
/// `codegen::emit`) that never reaches `copy_class.mo`, so the report's
/// target closure still would not contain it. The B0 verification
/// caught this: `Copy granted` fell from 240 to 0 while every other
/// figure held. Only two things actually put the instances in scope —
/// this shim, or re-exporting from `init/src/lib.mo`.
use lang {}
use init::copy {}
use init::borrow {}

/// A test only so the module has a runnable decl; the file's job is its
/// `use` lines. The report never calls this.
#[test]
def affine_target_loads : Bool := true
