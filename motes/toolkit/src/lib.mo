// The toolkit mote's library root -- bare `use toolkit` resolves here.
//
// The shared LSP substrate, bottom up: `bytes` (UTF-8 and ASCII byte
// classes), `position` (offsets <-> line/character, in either position
// encoding), `text` (what a span of source is), `framing` (Content-Length
// framing), `jsonrpc` (the message envelope), `wire` (the JSON shapes
// LSP-defined messages are), `diagnostic` (a compiler diagnostic as the
// wire sees it), `docstore` (open documents, keyed by URI), `decl_text` (a
// file's outline with trimmed spans and name ranges) and `navigation` (the
// identifier under a cursor, resolved for hover and definition).
//
// One type group per module, which is the rule `build/src/lib.mo` set:
// the TYPES are what a consumer cannot get by naming the module it already
// knows. Every function is reached the way `motes/lsp` reaches it today
// (`use toolkit::position { line_index_of_source }`), so this file is not
// a second index of the ten modules -- it is what makes `use toolkit`
// resolve, and what a consumer can declare its dependency against.
//
// No `{*}` globs.

pub use lib::bytes {}
pub use lib::decl_text {DeclText}
pub use lib::diagnostic {WireDiagnostic}
pub use lib::docstore {Doc, DocStore}
pub use lib::framing {FramingMode, FrameRead}
pub use lib::jsonrpc {RpcMessage}
pub use lib::navigation {NavTarget}
pub use lib::position {LineIndex, LineInfo, PositionEncoding, WirePosition, WireRange}
pub use lib::text {TextSpan}
pub use lib::wire {}
