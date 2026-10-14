/// The mcp_client mote's library root -- bare `use mcp_client` resolves
/// here.
///
/// The client half of MCP over stdio, bottom up: `protocol` (what the
/// messages say), `stdio` (how they move over a piped `Child`), `server`
/// (a mounted session: handshake, tool catalogue, teardown).
///
/// Every function is reached by naming its module
/// (`use mcp_client::stdio {Stdio}`), so this file is not a second index
/// of the three modules -- it is what makes `use mcp_client` resolve, and
/// what a consumer can declare its dependency against. No `{*}` globs,
/// matching `motes/toolkit/src/lib.mo`'s own convention.

pub use lib::protocol {McpCallResult, McpClientInfo, McpServerInfo, McpTool}
pub use lib::server {McpServer}
pub use lib::stdio {McpStdio}
