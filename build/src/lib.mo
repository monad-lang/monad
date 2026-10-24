// The build mote's library root -- bare `use build` resolves here.
//
// The layers, bottom up: `hash` (the content digest a key is built from),
// `identity` (which compiler is running), `closure` (the key itself),
// `store` (where output goes and what an entry is called), `check` (the
// check cache), `manage` (the verbs that inspect and reclaim all of it).
// `lock` (`mote.lock`) sits beside them rather than on top. This file is
// where they get re-exported from, so a consumer -- today only
// `cli/src/main.mo` -- sees one mote rather than seven modules.

pub use lib::hash {DigestTool}
pub use lib::identity {}
pub use lib::closure {}
pub use lib::store {Entry}
pub use lib::check {CheckPlan}
pub use lib::manage {}
pub use lib::lock {GitPin, LockRead, LockedGit, LockedMote, Lockfile}
