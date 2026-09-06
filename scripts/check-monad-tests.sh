#!/usr/bin/env bash
# Fast pre-commit .mo sweep (run by the `monad-tests` hook in devenv.nix).
# Splits the old single `test init std lang examples` into a fast
# `test init std examples` (the lang/ test suite is the slow part -- it
# runs the self-hosted checker over its own test files) plus a cheaper
# `check lang` (type-check lang/ without running its tests). prek does
# not invoke a shell, so a hook entry can't use `&&`/newlines to chain
# two commands -- hence this wrapper script.
#
# `check lang` runs the Rust host's checker over the whole lang/ tree.
# It used to fail on a bare-key collision in the meta-eval's whole-program
# capture (`init/meta.mo`'s `MatchArm`/`Decl`/`Param` overwritten by
# `lang/core_ir.mo`'s `MatchArm` and `lang/types.mo`'s `Decl`/`Param` in
# the flat bare-key `program.inductives` map), surfacing as
# `unresolved global: MatchArm.match_arm`; fixed by scoping
# `MetaEvalContext::build` and `collect_loaded_inductives` to the
# dep-closure of the file being expanded. It now passes (0 errors) and
# gates the hook like the `test init std examples` line above.
set -euo pipefail
cargo run --release -- test init std examples lang slow_tests
