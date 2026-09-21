/// The elaboration target for `bench/src/affine_report.mo`.
///
/// One file that pulls in both halves the report needs in a single
/// scope: the compiler's own closure (`lang`, which is what is being
/// measured) and the `Copy` class with its builtin instances
/// (`std::copy`, which is what the measurement resolves against).
///
/// It exists because `std/src/copy.mo` is deliberately NOT re-exported
/// from `std/src/lib.mo` yet. Making `Copy` ambient corpus-wide is a
/// real decision — it puts the class and its `copy` method into every
/// importer's namespace — and it belongs to the milestone where
/// enforcement actually lands, not to an experiment that is still
/// deciding whether enforcement is viable. Loading it here gives the
/// report a scope containing the instances without perturbing anything
/// the corpus compiles.
use lang {}
use std::copy {}

/// A test only so the module has a runnable decl; the file's job is its
/// `use` lines. The report never calls this.
#[test]
def affine_target_loads : Bool := true
