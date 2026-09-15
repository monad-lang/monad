// The runtime mote's library root -- bare `use runtime` resolves here.
//
// The C runtime is linked into every compiled binary, so its path is a
// build input that both the compiler's CLI and the codegen e2e harness
// need. It lives here, in the mote that owns the file, rather than being
// copied into each call site -- which is what it was before, in four
// places that all had to be found by hand when the file moved.

pub use lib::natives {runtime_native_functions}

/// Path to the C runtime source, relative to the repository root.
///
/// Repo-root-relative because every caller runs from there (the test
/// harnesses, `monad compile`, the devenv bootstrap task). Making this
/// absolute or store-resolved is part of the build-system work, not this
/// mote's job -- see plans/library-ideas/monad-build.md.
def Runtime.c_path : String := "runtime/src/runtime.c"
