// The lsp mote's library root -- bare `use lsp` resolves here.
//
// The language server, in the order a request moves through it: `server`
// (the state a session is, and the dispatch loop), `lifecycle`
// (`initialize`'s capabilities and encoding negotiation), `params` (reading
// a request's arguments out of its JSON), `documents` (didOpen/didChange/
// didClose against the docstore), `checks` (the check cache a document's
// diagnostics come from), `diagnostics` (turning a check into a publish
// notification) and `navigation` (hover, definition, document and
// workspace symbols). The server logs to stderr through the `log` mote's
// `Logger` (`server.mo`'s `lsp_logger`).
//
// One type group per module, which is the rule `build/src/lib.mo` set --
// a consumer cannot get a type by naming a module it does not yet know.
// The functions are reached the way `cli/src/main.mo` and the tests reach
// them (`use lsp::server { lsp_serve }`); this file's job is to make
// `use lsp` resolve and to give a consumer one declared dependency.
//
// No `{*}` globs: a glob here would pull seven modules' namespaces into
// every importer's scope.

pub use lib::checks {Check, CheckStore}
pub use lib::diagnostics {}
pub use lib::documents {DocumentEdit}
pub use lib::lifecycle {}
pub use lib::navigation {Cursor}
pub use lib::params {}
pub use lib::server {ServerState, ServerStep}
