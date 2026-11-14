// The loom mote's library root -- bare `use loom` resolves here.
//
// Deliberately empty, matching `motes/moose/src/lib.mo`'s own
// precedent: the surface lives in `warp.mo` (Phase 1), `strand.mo` and
// `disposer.mo` (Phase 2), and `service.mo` (Phase 3). A bare `use loom`
// re-exports nothing; name the module (`use loom::service {Service}`).
