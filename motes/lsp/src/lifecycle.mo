/// The handshake: what this server says it can do, and what it agreed to count in.
///
/// THE CAPABILITY LIST IS THE PROTOCOL, and advertising more than is implemented
/// is the one mistake here that cannot be walked back. A client believes the list:
/// advertising `completionProvider` and then answering `Method not found` puts a
/// completion popup in front of the user that fails on every keystroke, and
/// advertising `codeActionProvider` makes a client offer refactors this server
/// would have to refuse. The six capabilities below are exactly the six methods
/// `server.mo` answers -- diagnostics arrive as a notification and so are not
/// advertised at all -- and the list and the dispatcher are meant to be read
/// together.
///
/// ONE THING IS ADVERTISED THAT THE RUST SERVER DID NOT: `positionEncoding`. Its
/// absence is not neutral. A client that sees no `positionEncoding` in the result
/// is held to the specification's utf-16 default, so the old server was committed
/// to utf-16 whether or not it built its ranges that way -- and it built them from
/// byte offsets, which is the same thing only on pure ASCII. This server
/// NEGOTIATES: it picks from the client's offered list and echoes the winner, so
/// the conversion the ranges go through is the conversion the client will use to
/// read them. That single field is the difference between a squiggle under the
/// right characters and a squiggle that drifts one column per non-ASCII character
/// before it, in a corpus whose comments are full of em dashes and curly quotes.
use json::json {Json}
use toolkit::docstore {docstore_path_of_uri}
use toolkit::jsonrpc {rpc_field, rpc_object}
use toolkit::position {
    PositionEncoding, position_encoding_default, position_encoding_from_string,
    position_encoding_name,
}
use lsp::params {lsp_param_index, lsp_param_nested, lsp_param_str, lsp_param_str_list}

// --- Identity ---

/// The name a client shows in its server list. The same string the Rust server
/// sends, so a user with both installed is not looking at two names for one thing.
pub def lsp_server_name : String := "monad-lsp"

/// The version in `serverInfo`. A fixed string rather than a build stamp: nothing
/// reads it but a human, and the alternative -- a compiler-emitted literal -- is a
/// codegen path for a field no client compares.
pub def lsp_server_version : String := "0.1.0"

// --- Encoding negotiation ---

/// The units this server agreed to count in.
///
/// THE CLIENT'S FIRST SUPPORTED CHOICE WINS, which is the policy
/// `toolkit::position`'s own doc states, and it is a policy rather than a
/// preference: a client lists its encodings in ITS order of preference, so taking
/// the cheapest one for this server instead would be deciding on the client's
/// behalf about something the client is better informed about.
///
/// An absent list, an empty list, and a list of nothing this server speaks all
/// answer the specification's default, utf-16. For the first two that is what the
/// specification requires; for the third it is the honest answer, because
/// `positionEncoding` in the result MUST name an encoding the client offered and
/// utf-16 is the one every client must support.
#[partial]
pub def lsp_choose_encoding (offered : List String) : PositionEncoding :=
    match lsp_first_known_encoding offered {
        Option.none => position_encoding_default,
        Option.some e => e,
    }

#[partial]
def lsp_first_known_encoding (offered : List String) : Option PositionEncoding :=
    match offered {
        List.empty => Option.none,
        List.cons s rest =>
            match position_encoding_from_string s {
                Option.none => lsp_first_known_encoding rest,
                Option.some e => Option.some e,
            },
    }

/// The encodings the client offered, or the empty list.
///
/// The field is `capabilities.general.positionEncodings` -- two levels down, under
/// the capabilities the client sends about itself -- and it was added in 3.17, so
/// a client that predates it sends nothing and gets the default. Helix 25.07 does
/// send it.
#[partial]
pub def lsp_offered_encodings (params : Json) : List String :=
    match lsp_param_nested "capabilities" "general" params {
        Option.none => lsp_no_encodings,
        Option.some general => lsp_param_str_list "positionEncodings" general,
    }

/// The empty encoding list as a named def, so no caller writes a bare
/// `List.empty` whose element type has to be inferred.
pub def lsp_no_encodings : List String := List.empty

// --- The workspace root ---

/// The directory this session is about, from `initialize`.
///
/// `rootUri` first, then the first of `workspaceFolders`, and nothing else. Both
/// are URIs and both are percent-decoded on the way out, which is the whole reason
/// this is not a string read: a root with a space in it arrives as `%20`, and a
/// workspace scan handed `%20` as literal text scans a directory that does not
/// exist.
///
/// A `rootUri` that is present but is not a `file:` URI -- `untitled:`, or an
/// unknown workspace -- does NOT answer `Option.none` immediately: it falls
/// through to `workspaceFolders`, because a client that sends both is describing
/// one thing and a root this server cannot use is not a decision about the other.
///
/// The deprecated `rootPath` string is deliberately not read. It names a
/// filesystem path rather than a URI, so supporting it means a second kind of
/// input with no decoding, and every client this server is tested against sends
/// `rootUri` or `workspaceFolders`.
#[partial]
pub def lsp_root_path (params : Json) : Option String :=
    match lsp_param_str "rootUri" params {
        Option.none => lsp_workspace_folder_path params,
        Option.some uri =>
            match docstore_path_of_uri uri {
                Option.none => lsp_workspace_folder_path params,
                Option.some p => Option.some p,
            },
    }

#[partial]
def lsp_workspace_folder_path (params : Json) : Option String :=
    match lsp_param_index 0 (rpc_field "workspaceFolders" params) {
        Option.none => Option.none,
        Option.some folder =>
            match lsp_param_str "uri" folder {
                Option.none => Option.none,
                Option.some uri => docstore_path_of_uri uri,
            },
    }

// --- The initialize result ---

/// Full-text sync, which is the specification's `TextDocumentSyncKind.Full`.
///
/// Incremental sync is `2` and is not advertised, because the docstore applies a
/// whole buffer. `toolkit::docstore`'s own doc records that its `open` and
/// `change` entry points are separate so that incremental sync would change
/// exactly one of them -- when it does, this constant moves and nothing else.
pub def lsp_sync_full : I64 := 1

/// What this server can do, in the client's vocabulary.
///
/// The booleans are the navigation features and formatting; `textDocumentSync` is required
/// for the client to send `didOpen`/`didChange` at all, so a server that omitted
/// it would receive no documents and have nothing to check.
#[partial]
pub def lsp_capabilities_json (enc : PositionEncoding) : Json :=
    rpc_object [
        Pair.pair "positionEncoding" (Json.make_str (position_encoding_name enc)),
        Pair.pair "textDocumentSync" (Json.make_num_int lsp_sync_full),
        Pair.pair "hoverProvider" (Json.make_bool true),
        Pair.pair "definitionProvider" (Json.make_bool true),
        Pair.pair "documentSymbolProvider" (Json.make_bool true),
        Pair.pair "workspaceSymbolProvider" (Json.make_bool true),
        Pair.pair "documentFormattingProvider" (Json.make_bool true),
    ]

#[partial]
pub def lsp_server_info_json : Json :=
    rpc_object [
        Pair.pair "name" (Json.make_str lsp_server_name),
        Pair.pair "version" (Json.make_str lsp_server_version),
    ]

/// The `initialize` result, for the encoding that was negotiated from these params.
#[partial]
pub def lsp_initialize_result (enc : PositionEncoding) : Json :=
    rpc_object [
        Pair.pair "capabilities" (lsp_capabilities_json enc),
        Pair.pair "serverInfo" lsp_server_info_json,
    ]
