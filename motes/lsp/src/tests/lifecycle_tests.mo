/// Handshake tests: the encoding that was negotiated, the capabilities that were
/// advertised, and the workspace root that was read.
///
/// EVERY FIXTURE IS A NAMED DEF AND EVERY FIXTURE IS PINNED BY `lc_roundtrips`, and
/// that guard is the most important thing in this file. `lc_json` answers
/// `Json.make_null` for text that does not parse, and a `null` params node reads as
/// "the client offered nothing" -- which is exactly what several of these tests
/// expect to see. So a fixture with a missing brace does not fail; it turns the test
/// that uses it into a test of the default, which PASSES. This file shipped that bug
/// before the guard: three encoding fixtures were written with two closing braces
/// instead of three, and every assertion built on them was vacuous. Naming the
/// fixtures once and asserting each parses back to itself byte for byte is what makes
/// that class of typo loud, and it is why the guard is written as an exact round trip
/// rather than as "is an object".
///
/// THE CAPABILITY LIST IS ASSERTED AS AN EXACT WIRE STRING, for the same reason one
/// level up. Advertising a capability is not reversible from the client's side: a
/// client that sees `completionProvider` puts a completion popup in front of the user
/// and it fails on every keystroke if the server does not implement it. A test that
/// checked "the six fields are present" would pass just as happily with a seventh
/// field added by mistake, so the assertion is the whole object, byte for byte, and
/// adding a capability is a deliberate edit to this file.
///
/// The encoding tests are about a desynchronization rather than a preference: a
/// server that answers utf-8 to a client that will read utf-16 puts every range after
/// a non-ASCII character on the wrong column, and nothing in the protocol catches it.
/// The first-supported-choice rule is pinned in BOTH directions -- the same two
/// encodings, listed either way, must answer differently -- because a single
/// ordering passes for an implementation that ignores the client's order and always
/// picks its own favourite.
///
/// Field reads go through the typed accessor defs below (`lc_*`), never inline in a
/// `#[test]` def, per this repo's recorded `#[test]` plus struct-field codegen
/// hazard. The `lc_` prefix is collision-avoiding: whole-program scope is shared with
/// every other mote's tests, and a sibling helper of the same name is a documented
/// miscompile.
use json::json {Json}
use lsp::lifecycle {
    lsp_capabilities_json, lsp_choose_encoding, lsp_initialize_result, lsp_offered_encodings,
    lsp_root_path, lsp_server_info_json,
}
/// `PositionEncoding` the TYPE is not imported: nothing here writes it in a type
/// annotation, so the only uses are its CONSTRUCTORS. Those are named by their
/// BARE spelling (`utf8`, not `PositionEncoding.utf8`) -- a brace item names the
/// declaration, and a constructor is declared bare inside its type's body, even
/// though the call sites here write it qualified. Importing the type as well
/// would be the unused import `check` warns on.
use toolkit::position {position_encoding_name, utf16, utf8}

// --- Fixture plumbing ---

/// Parse a fixture, or `null`.
///
/// A malformed fixture answers `null`, which reads as "the client offered nothing"
/// and is indistinguishable from a client that genuinely offered nothing -- hence
/// `lc_roundtrips` below, which is run over every fixture so a typo cannot hide.
def lc_json (s : String) : Json :=
    match Json.parse s {
        Result.err _e => Json.make_null,
        Result.ok j => j,
    }

/// THE GUARD: the fixture parses, and parses to exactly the text written.
///
/// A round trip is identity for well-formed JSON and `"null"` for anything that does
/// not parse, so this is false for every malformed fixture and true for every good
/// one. One assertion per fixture, all of them conjoined, so `test_the_fixtures_...`
/// names the whole set at once.
///
/// IT IS IDENTITY ONLY FOR KEYS ALREADY IN WIRE ORDER, and that is a feature rather
/// than a rough edge: `Json.to_string` walks a `BTreeMap`, so a fixture written with
/// its keys out of order round-trips to the sorted spelling and fails here. A
/// `{"processId":1,"clientInfo":{...}}` fixture is therefore not merely caught, it is
/// caught for the right reason, and the fix is to write the fixture the way a client
/// would have it after a re-encode. That is how this file found its own one
/// out-of-order fixture.
def lc_roundtrips (s : String) : Bool := String.beq (Json.to_string (lc_json s)) s

def lc_path (o : Option String) : String :=
    match o {
        Option.none => "<none>",
        Option.some s => s,
    }

/// The encoding a client's params negotiate to, as its wire name -- the whole
/// negotiation, read the way `server.mo` reads it.
def lc_encoding (params : Json) : String :=
    position_encoding_name (lsp_choose_encoding (lsp_offered_encodings params))

def lc_encoding_of (s : String) : String := lc_encoding (lc_json s)

/// The encodings read out of params, joined so that an empty list is a visible empty
/// string.
def lc_offered (s : String) : String := lc_join (lsp_offered_encodings (lc_json s)) ""

#[partial]
def lc_join (xs : List String) (acc : String) : String :=
    match xs {
        List.empty => acc,
        List.cons x rest =>
            if String.is_empty acc
            then lc_join rest x
            else lc_join rest (String.concat acc (String.concat "|" x)),
    }

// --- Encoding fixtures ---

/// A list of encodings where this server's preference and the client's order agree.
def lc_enc_utf8_first : String :=
    "{\"capabilities\":{\"general\":{\"positionEncodings\":[\"utf-8\",\"utf-16\"]}}}"

/// THE OTHER ORDER, and the one that tells the two policies apart: same two
/// encodings, offered utf-16 first. A server that answered utf-8 to both would fail
/// here and pass the one above.
def lc_enc_utf16_first : String :=
    "{\"capabilities\":{\"general\":{\"positionEncodings\":[\"utf-16\",\"utf-8\"]}}}"

/// A name this server does not speak, ahead of one it does.
def lc_enc_unknown_first : String :=
    "{\"capabilities\":{\"general\":{\"positionEncodings\":[\"utf-32\",\"utf-8\"]}}}"

def lc_enc_unknown_first_utf16 : String :=
    "{\"capabilities\":{\"general\":{\"positionEncodings\":[\"utf-32\",\"utf-16\"]}}}"

/// Offering nothing, in the four shapes that means. The first three are a client that
/// has no opinion; the last is the one a reader that trusted the specification's
/// stated type would crash on.
def lc_no_caps : String := "{}"

def lc_caps_empty : String := "{\"capabilities\":{}}"

/// A realistic `initialize` with no `capabilities` at all -- a client older than
/// 3.17 sends this, and it also carries fields this server must not read. Keys are in
/// wire order, which for this pair means `clientInfo` first.
def lc_bare_init : String := "{\"clientInfo\":{\"name\":\"helix\"},\"processId\":1}"

def lc_enc_empty : String :=
    "{\"capabilities\":{\"general\":{\"positionEncodings\":[]}}}"

def lc_enc_only_unknown : String :=
    "{\"capabilities\":{\"general\":{\"positionEncodings\":[\"utf-32\"]}}}"

def lc_enc_not_a_list : String :=
    "{\"capabilities\":{\"general\":{\"positionEncodings\":\"utf-8\"}}}"

/// `positionEncodings` one level too high. The field is inside `general`, and a
/// reader that searched the capabilities object recursively would take this as an
/// offer; the specification puts it at `general`, so it is not one.
def lc_enc_wrong_path : String := "{\"capabilities\":{\"positionEncodings\":[\"utf-8\"]}}"

/// THE GUARD ITSELF, over every fixture in the file. See `lc_roundtrips`.
#[test]
def test_every_encoding_fixture_is_the_json_it_looks_like : Bool :=
    lc_roundtrips lc_enc_utf8_first
        && lc_roundtrips lc_enc_utf16_first
        && lc_roundtrips lc_enc_unknown_first
        && lc_roundtrips lc_enc_unknown_first_utf16
        && lc_roundtrips lc_no_caps
        && lc_roundtrips lc_caps_empty
        && lc_roundtrips lc_bare_init
        && lc_roundtrips lc_enc_empty
        && lc_roundtrips lc_enc_only_unknown
        && lc_roundtrips lc_enc_not_a_list
        && lc_roundtrips lc_enc_wrong_path

// --- Encoding negotiation ---

/// The client's order decides. Both directions on the same two names, so neither an
/// always-utf-8 nor an always-utf-16 implementation passes.
#[test]
def test_the_clients_order_decides_the_encoding : Bool :=
    String.beq (lc_encoding_of lc_enc_utf8_first) "utf-8"
        && String.beq (lc_encoding_of lc_enc_utf16_first) "utf-16"

/// An unrecognized name is skipped rather than ending the search, so a client that
/// offers something this server cannot do and then something it can gets the second.
#[test]
def test_an_unknown_encoding_is_skipped : Bool :=
    String.beq (lc_encoding_of lc_enc_unknown_first) "utf-8"
        && String.beq (lc_encoding_of lc_enc_unknown_first_utf16) "utf-16"

/// Everything that offers this server nothing answers the specification's default.
///
/// The last two are worth their own sentence. `positionEncodings` as a string is
/// malformed and must not crash; `positionEncodings` one level too high is
/// well-formed and must not be found, because the specification fixes the path and a
/// reader that searched for the key anywhere would invent an agreement the client did
/// not make.
#[test]
def test_nothing_usable_offered_means_utf16 : Bool :=
    String.beq (lc_encoding_of lc_no_caps) "utf-16"
        && String.beq (lc_encoding_of lc_caps_empty) "utf-16"
        && String.beq (lc_encoding_of lc_bare_init) "utf-16"
        && String.beq (lc_encoding_of lc_enc_empty) "utf-16"
        && String.beq (lc_encoding_of lc_enc_only_unknown) "utf-16"
        && String.beq (lc_encoding_of lc_enc_not_a_list) "utf-16"
        && String.beq (lc_encoding_of lc_enc_wrong_path) "utf-16"

/// The reader itself, so the tests above are about the choice and not about where the
/// list came from. The second case is the one that proves the path is exact: the same
/// array of names, at the wrong level, reads as nothing.
#[test]
def test_the_offered_list_is_read_from_the_capabilities : Bool :=
    String.beq (lc_offered lc_enc_utf16_first) "utf-16|utf-8"
        && String.beq (lc_offered lc_enc_wrong_path) ""
        && String.beq (lc_offered lc_no_caps) ""

/// The choice made directly, without params, so the default is pinned independently
/// of the reading -- and so a failure above can be attributed to the reader rather
/// than to the policy.
#[test]
def test_the_choice_defaults_to_the_specifications_encoding : Bool :=
    String.beq (position_encoding_name (lsp_choose_encoding (lc_no_offerings))) "utf-16"
        && String.beq (position_encoding_name (lsp_choose_encoding (lc_utf8_offering))) "utf-8"

/// Named locals rather than bare `List.empty`/`List.cons` in argument position: a
/// bare `List.empty` whose element type has to be inferred from the callee is the
/// `Map.empty` trap one type over, and the `lc_` prefix keeps these out of the way of
/// the mote's own `lsp_*` surface in whole-program scope.
def lc_no_offerings : List String := List.empty

def lc_utf8_offering : List String := List.cons "utf-8" lc_no_offerings

// --- Capabilities, byte for byte ---

/// THE CONTRACT. Every capability this server advertises, and nothing else.
///
/// Keys are alphabetical because `Json.to_string` walks a `BTreeMap`, which is worth
/// knowing when reading the literal: `definitionProvider` sorts before
/// `documentFormattingProvider`/`documentSymbolProvider` because `e` is before `o` in
/// the second word, and
/// `textDocumentSync` sits between `positionEncoding` and `workspaceSymbolProvider`.
def lc_caps_utf16 : String :=
    "{\"definitionProvider\":true,\"documentFormattingProvider\":true,\"documentSymbolProvider\":true,\"hoverProvider\":true,\"positionEncoding\":\"utf-16\",\"textDocumentSync\":1,\"workspaceSymbolProvider\":true}"

def lc_caps_utf8 : String :=
    "{\"definitionProvider\":true,\"documentFormattingProvider\":true,\"documentSymbolProvider\":true,\"hoverProvider\":true,\"positionEncoding\":\"utf-8\",\"textDocumentSync\":1,\"workspaceSymbolProvider\":true}"

#[test]
def test_the_capabilities_are_exactly_these_six : Bool :=
    String.beq (Json.to_string (lsp_capabilities_json PositionEncoding.utf16)) lc_caps_utf16
        && String.beq (Json.to_string (lsp_capabilities_json PositionEncoding.utf8)) lc_caps_utf8

def lc_server_info : String := "{\"name\":\"monad-lsp\",\"version\":\"0.1.0\"}"

#[test]
def test_the_server_info_names_this_server : Bool :=
    String.beq (Json.to_string lsp_server_info_json) lc_server_info

/// The initialize result as a whole, so the capabilities cannot drift out of the
/// result they are sent in, and the negotiated encoding is the one in the RESULT
/// rather than merely the one computed.
#[test]
def test_the_initialize_result_carries_the_negotiated_encoding : Bool :=
    String.beq (Json.to_string (lsp_initialize_result PositionEncoding.utf16))
        (String.concat "{\"capabilities\":" (String.concat lc_caps_utf16 (String.concat ",\"serverInfo\":" (String.concat lc_server_info "}"))))
        && String.beq (Json.to_string (lsp_initialize_result PositionEncoding.utf8))
            (String.concat "{\"capabilities\":" (String.concat lc_caps_utf8 (String.concat ",\"serverInfo\":" (String.concat lc_server_info "}"))))

// --- The workspace root ---

/// The root fixtures, guarded by the same round trip -- `test_no_root_is_no_root`
/// expects `<none>` in its first cases, which is the same answer a malformed fixture
/// gives.
def lc_root_plain : String := "{\"rootUri\":\"file:///home/u/project\"}"

def lc_root_escaped : String := "{\"rootUri\":\"file:///home/u/my%20project\"}"

def lc_root_folders : String := "{\"workspaceFolders\":[{\"uri\":\"file:///w\"}]}"

def lc_root_untitled_with_folders : String :=
    "{\"rootUri\":\"untitled:Untitled-1\",\"workspaceFolders\":[{\"uri\":\"file:///w\"}]}"

def lc_root_two_folders : String :=
    "{\"workspaceFolders\":[{\"uri\":\"file:///one\"},{\"uri\":\"file:///two\"}]}"

def lc_root_empty : String := "{}"

def lc_root_bare_file : String := "{\"rootUri\":\"file://\"}"

def lc_root_no_folders : String := "{\"workspaceFolders\":[]}"

def lc_root_untitled_only : String := "{\"workspaceFolders\":[{\"uri\":\"untitled:x\"}]}"

def lc_root_folder_no_uri : String := "{\"workspaceFolders\":[{\"name\":\"w\"}]}"

def lc_root_folders_not_a_list : String := "{\"workspaceFolders\":{\"uri\":\"file:///w\"}}"

#[test]
def test_every_root_fixture_is_the_json_it_looks_like : Bool :=
    lc_roundtrips lc_root_plain
        && lc_roundtrips lc_root_escaped
        && lc_roundtrips lc_root_folders
        && lc_roundtrips lc_root_untitled_with_folders
        && lc_roundtrips lc_root_two_folders
        && lc_roundtrips lc_root_empty
        && lc_roundtrips lc_root_bare_file
        && lc_roundtrips lc_root_no_folders
        && lc_roundtrips lc_root_untitled_only
        && lc_roundtrips lc_root_folder_no_uri
        && lc_roundtrips lc_root_folders_not_a_list

def lc_root (s : String) : String := lc_path (lsp_root_path (lc_json s))

/// `rootUri` is the first place the root is read from, and a percent-escaped path in
/// it is decoded -- the same decoding the document URIs get, on the field that names
/// the directory a workspace scan walks.
#[test]
def test_the_root_uri_is_read_and_decoded : Bool :=
    String.beq (lc_root lc_root_plain) "/home/u/project"
        && String.beq (lc_root lc_root_escaped) "/home/u/my project"

/// `workspaceFolders` is the fallback, both when `rootUri` is absent and when it is
/// present but names no directory this server can use. The second is the case worth
/// pinning: a client that sends both is describing one workspace, so a `rootUri` that
/// decodes to no path must not end the search.
#[test]
def test_the_workspace_folders_are_the_fallback : Bool :=
    String.beq (lc_root lc_root_folders) "/w"
        && String.beq (lc_root lc_root_untitled_with_folders) "/w"

/// The FIRST folder is the workspace and a later one is not consulted -- a server
/// that checked every folder would answer for a directory the user is not in.
#[test]
def test_the_first_workspace_folder_wins : Bool :=
    String.beq (lc_root lc_root_two_folders) "/one"

/// No root at all is `Option.none` rather than a guess. An empty string would be
/// worse than useless: it is the path a scan of a relative path resolves against, so
/// a workspace symbol search would silently walk the server's own working directory.
///
/// The last case is the shape a reader that treated "one folder or a list of them" as
/// equivalent would answer with the folder itself.
#[test]
def test_no_root_is_no_root : Bool :=
    String.beq (lc_root lc_root_empty) "<none>"
        && String.beq (lc_root lc_root_bare_file) "<none>"
        && String.beq (lc_root lc_root_no_folders) "<none>"
        && String.beq (lc_root lc_root_untitled_only) "<none>"
        && String.beq (lc_root lc_root_folder_no_uri) "<none>"
        && String.beq (lc_root lc_root_folders_not_a_list) "<none>"
