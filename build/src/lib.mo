// The build mote's library root -- bare `use build` resolves here.
//
// The layers, bottom up: `hash` (the content digest a key is built from),
// `identity` (which compiler is running), `closure` (the key itself),
// `store` (where output goes and what an entry is called, plus the
// `$MONAD_HOME` lookup every `~/.monad` consumer shares), `check` (the
// check cache), `manage` (the verbs that inspect and reclaim all of it).
// Beside them: `git` (the `git` CLI transport for git dependencies) and
// `fetch` (`monad fetch`/`update`, the only network verb). `mote.lock`
// itself lives in `lang::lock`: the LOADER has to read it to locate a git
// dependency, and `lang` cannot depend on `build`.
//
// This file is where they all get re-exported from, so a consumer -- today
// only `cli/src/main.mo` -- sees one mote rather than nine modules.

pub use lib::hash {DigestTool}
pub use lib::identity {}
pub use lib::closure {}
pub use lib::store {Entry}
pub use lib::check {CheckPlan}
pub use lib::manage {}
