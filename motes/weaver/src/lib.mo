// The weaver mote's library root -- bare `use weaver` resolves here.
//
// Weaver's surface is its policy (`policy.mo`); the later phases add
// the interactive gate, the command table, the settings and the dumb
// loop as they land. Re-exported by name, no `{*}` globs, the same
// discipline as `motes/json/src/lib.mo`.

pub use lib::policy {Mode, Decision, Policy.decide}
