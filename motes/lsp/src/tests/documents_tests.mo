/// Document-notification tests: what `didOpen`/`didChange`/`didClose` leave behind.
///
/// THE `changed` FLAG IS WHAT THIS FILE MOSTLY TESTS, and it is not bookkeeping.
/// Re-checking a buffer is the expensive thing this server does, and a client sends
/// `didChange` for edits that change nothing a checker sees -- a keystroke that was
/// undone, a cursor movement it chose to report, an edit delivered twice. So the flag
/// is the debounce, and the debounce is a comparison of the incoming text against the
/// buffer already held: the one test that CANNOT be wrong. A test that only asserted
/// "the store holds the new text" would pass for a server that re-checks on every
/// keystroke, which is the failure the flag exists to prevent.
///
/// THE VERSION IS THE OTHER HALF, and its failure mode is the quietest in the whole
/// server. `publishDiagnostics` may carry the version its diagnostics were computed
/// against, and a client that receives a version NEWER than its buffer discards the
/// whole set -- so a server that invented a version, or kept a stale one, silently
/// stops showing diagnostics for a file the user is editing. Nothing errors. So the
/// absent-version cases below are pinned in both directions: a stated version wins,
/// and an absent one keeps what the document already had.
///
/// EVERY FIXTURE IS A NAMED DEF AND EVERY FIXTURE IS PINNED BY `ld_roundtrips`, for
/// the reason the sibling test files record: `ld_json` answers `null` for text that
/// does not parse, and every malformed-notification case here EXPECTS the absent
/// answer -- so a fixture with a missing brace would not fail, it would turn a
/// malformed-input test into a test of the malformed-input case, which passes. A
/// second consequence of the same guard: a fixture must be written with its keys in
/// WIRE ORDER, because `Json.to_string` walks a `BTreeMap` and re-sorts. That means
/// the fixture text below is the canonical form a client's re-encode would have, which
/// is a better fixture than a human's ordering.
///
/// Field reads go through the typed accessor defs below (`ld_*`), never inline in a
/// `#[test]` def, per this repo's recorded `#[test]` plus struct-field codegen hazard.
/// The `ld_` prefix is collision-avoiding: whole-program scope is shared with every
/// other mote's tests.
use json::json {Json}
use lsp::documents {
    DocumentEdit, document_change, document_close, document_edit_changed, document_edit_store,
    document_edit_uri, document_open, document_uri,
}
use toolkit::docstore {DocStore, docstore_count, docstore_empty, docstore_open, docstore_text, docstore_version}

// --- Fixture plumbing ---

def ld_json (s : String) : Json :=
    match Json.parse s {
        Result.err _e => Json.make_null,
        Result.ok j => j,
    }

/// THE GUARD: the fixture parses, and parses to exactly the text written.
def ld_roundtrips (s : String) : Bool := String.beq (Json.to_string (ld_json s)) s

def ld_text (o : Option String) : String :=
    match o {
        Option.none => "<none>",
        Option.some s => s,
    }

def ld_ver (o : Option I64) : String :=
    match o {
        Option.none => "<none>",
        Option.some n => I64.to_string n,
    }

def ld_bool (b : Bool) : String := if b then "true" else "false"

// --- Reading a DocumentEdit, always through accessors ---

/// The URI the notification was about, or `<none>` if it was not understood at all.
/// The three renderers below all answer `<none>` for `Option.none`, so a test that
/// names the URI and a test that names the flag cannot disagree about whether the
/// notification was understood.
def ld_uri_of (e : Option DocumentEdit) : String :=
    match e {
        Option.none => "<none>",
        Option.some d => document_edit_uri d,
    }

def ld_changed_of (e : Option DocumentEdit) : String :=
    match e {
        Option.none => "<none>",
        Option.some d => ld_bool (document_edit_changed d),
    }

/// The text the STORE holds after the edit, for that URI -- not the text the message
/// carried. The difference matters: a server that reported the message's text and a
/// server that stored it agree on every well-formed case and disagree exactly when the
/// store refused to move, which is the case worth seeing.
def ld_stored (e : Option DocumentEdit) (uri : String) : String :=
    match e {
        Option.none => "<none>",
        Option.some d => ld_text (docstore_text uri (document_edit_store d)),
    }

def ld_stored_version (e : Option DocumentEdit) (uri : String) : String :=
    match e {
        Option.none => "<none>",
        Option.some d => ld_ver (docstore_version uri (document_edit_store d)),
    }

def ld_stored_count (e : Option DocumentEdit) : String :=
    match e {
        Option.none => "<none>",
        Option.some d => I64.to_string (docstore_count (document_edit_store d)),
    }

// --- Fixtures ---

/// A `didOpen` as a client sends it. `languageId` is carried and never read: this
/// server does not decide what to do by language, and a fixture without one would
/// not be a fixture a client produces.
def ld_f_open : String :=
    "{\"textDocument\":{\"languageId\":\"monad\",\"text\":\"def f : I64 := 1\",\"uri\":\"file:///a.mo\",\"version\":1}}"

/// A second open of the SAME document, with different text and a later version.
def ld_f_open_v2 : String :=
    "{\"textDocument\":{\"languageId\":\"monad\",\"text\":\"def f : I64 := 2\",\"uri\":\"file:///a.mo\",\"version\":2}}"

/// An open whose text contains a real newline -- the shape every buffer a user has
/// actually typed in has, and the one that exercises the JSON writer's escaping.
/// In the Monad source the escape is doubled so the JSON text contains `\n`.
def ld_f_open_nl : String :=
    "{\"textDocument\":{\"text\":\"def f : I64 :=\\n  1\",\"uri\":\"file:///nl.mo\"}}"

/// A `didChange` in full-text sync: one element in `contentChanges`, whose `text` is
/// the whole buffer, and a stated version.
def ld_f_change : String :=
    "{\"contentChanges\":[{\"text\":\"def f : I64 := 3\"}],\"textDocument\":{\"uri\":\"file:///a.mo\",\"version\":5}}"

/// The same, with no version: the specification allows a null version, and a client
/// that sends none has no opinion -- which must not become an opinion here.
def ld_f_change_no_version : String :=
    "{\"contentChanges\":[{\"text\":\"def f : I64 := 4\"}],\"textDocument\":{\"uri\":\"file:///a.mo\"}}"

/// A `didChange` with no `contentChanges` at all.
def ld_f_change_no_changes : String := "{\"textDocument\":{\"uri\":\"file:///a.mo\",\"version\":9}}"

/// The same, as an empty array -- the shape a client sends when it reports an edit it
/// then rolled back. Distinct from the above because it exercises the index read
/// rather than the field read.
def ld_f_change_empty_array : String := "{\"contentChanges\":[],\"textDocument\":{\"uri\":\"file:///a.mo\"}}"

/// One change whose element carries no `text`. `range` is what an INCREMENTAL client
/// sends in place of a whole buffer, and this server advertised full sync, so it is
/// malformed input rather than incremental input -- an absent text, not a text to
/// reassemble.
def ld_f_change_no_text : String := "{\"contentChanges\":[{\"range\":{}}],\"textDocument\":{\"uri\":\"file:///a.mo\"}}"

/// A `didClose`, which names a document and carries nothing else.
def ld_f_close : String := "{\"textDocument\":{\"uri\":\"file:///a.mo\"}}"

def ld_f_no_doc : String := "{}"

/// A `textDocument` with no `uri`: present, an object, and naming nothing.
def ld_f_doc_no_uri : String := "{\"textDocument\":{\"version\":1}}"

/// An open with no `text`: the client is showing a document and has not said what is
/// in it, which this server cannot store.
def ld_f_open_no_text : String :=
    "{\"textDocument\":{\"languageId\":\"monad\",\"uri\":\"file:///a.mo\",\"version\":1}}"

/// A `uri` that is a number. Only the URI read is under test here; the malformed-URI
/// cases for the request methods live in `navigation_tests.mo`.
def ld_f_uri_int : String := "{\"textDocument\":{\"uri\":7}}"

#[test]
def test_every_fixture_is_the_json_it_looks_like : Bool :=
    ld_roundtrips ld_f_open
        && ld_roundtrips ld_f_open_v2
        && ld_roundtrips ld_f_open_nl
        && ld_roundtrips ld_f_change
        && ld_roundtrips ld_f_change_no_version
        && ld_roundtrips ld_f_change_no_changes
        && ld_roundtrips ld_f_change_empty_array
        && ld_roundtrips ld_f_change_no_text
        && ld_roundtrips ld_f_close
        && ld_roundtrips ld_f_no_doc
        && ld_roundtrips ld_f_doc_no_uri
        && ld_roundtrips ld_f_open_no_text
        && ld_roundtrips ld_f_uri_int

// --- The URI read ---

/// `document_uri` is the one reader in the module not tied to a store, and it is what
/// `didSave` and every request in `navigation.mo` use -- so it is tested on the
/// notifications that carry a document and nothing else.
#[test]
def test_the_document_uri_is_read_from_the_params : Bool :=
    String.beq (ld_text (document_uri (ld_json ld_f_close))) "file:///a.mo"
        && String.beq (ld_text (document_uri (ld_json ld_f_change_no_changes))) "file:///a.mo"
        && String.beq (ld_text (document_uri (ld_json ld_f_no_doc))) "<none>"
        && String.beq (ld_text (document_uri (ld_json ld_f_doc_no_uri))) "<none>"
        && String.beq (ld_text (document_uri (ld_json ld_f_uri_int))) "<none>"

// --- didOpen ---

/// The text comes from the MESSAGE and not from disk, and it is the whole of what the
/// notification does: an open records a version and a buffer, and does not re-read the
/// file -- the two differ the moment the user types, and the editor is showing the
/// one the user typed.
///
/// A document that was never stored counts as changed, which is what makes the flag
/// right for the very first notification about a file as well as for the tenth.
#[test]
def test_a_did_open_stores_the_text_the_client_sent : Bool :=
    let e : Option DocumentEdit := document_open (ld_json ld_f_open) docstore_empty in
    String.beq (ld_uri_of e) "file:///a.mo"
        && String.beq (ld_stored e "file:///a.mo") "def f : I64 := 1"
        && String.beq (ld_stored_version e "file:///a.mo") "1"
        && String.beq (ld_stored_count e) "1"
        && String.beq (ld_changed_of e) "true"

/// A second open of the same text is not a change; a second open of different text is.
/// Both halves on one fixture pair, because a flag that was hard-wired true would pass
/// the second alone and a flag hard-wired false the first.
#[test]
def test_a_repeated_did_open_is_a_change_only_when_the_text_moved : Bool :=
    let first : Option DocumentEdit := document_open (ld_json ld_f_open) docstore_empty in
    String.beq (ld_changed_of (ld_reopen first (ld_json ld_f_open))) "false"
        && String.beq (ld_changed_of (ld_reopen first (ld_json ld_f_open_v2))) "true"
        && String.beq (ld_stored (ld_reopen first (ld_json ld_f_open_v2)) "file:///a.mo") "def f : I64 := 2"

/// Open the same document again, through the store the first open returned -- which is
/// how the server holds it. A helper rather than an inline `match`, because a test def
/// with two nested struct-field reads is the recorded codegen hazard; the type is
/// written down and the field is read through the accessor.
def ld_reopen (first : Option DocumentEdit) (params : Json) : Option DocumentEdit :=
    match first {
        Option.none => Option.none,
        Option.some d => document_open params (document_edit_store d),
    }

/// A real newline in the buffer survives the round trip through JSON and into the
/// store, so a line-based consumer downstream is not silently handed an escaped one.
#[test]
def test_a_newline_in_the_text_survives_the_wire : Bool :=
    let e : Option DocumentEdit := document_open (ld_json ld_f_open_nl) docstore_empty in
    String.beq (ld_stored e "file:///nl.mo") "def f : I64 :=\n  1"
        && String.beq (ld_changed_of e) "true"

// --- didChange ---

/// Full-text sync: the single element of `contentChanges` is the whole buffer, so the
/// stored text is that element's `text` and not a patch applied to the old one.
#[test]
def test_a_did_change_takes_the_whole_buffer_from_the_first_change : Bool :=
    let e : Option DocumentEdit := document_change (ld_json ld_f_change) (ld_store_of "file:///a.mo" "def f : I64 := 1" 1) in
    String.beq (ld_stored e "file:///a.mo") "def f : I64 := 3"
        && String.beq (ld_stored_version e "file:///a.mo") "5"
        && String.beq (ld_changed_of e) "true"

/// A store holding one document, built directly rather than through `document_open`
/// so that a `didChange` test cannot fail because the OPEN was wrong.
def ld_store_of (uri : String) (text : String) (version : I64) : DocStore :=
    docstore_open uri version text docstore_empty

/// THE ABSENT VERSION, in both directions: a document that already has one keeps it,
/// and one this server has never seen falls back to 0.
///
/// The fallback is a number a client can tell from a stated one, because clients number
/// documents from 1 -- and `toolkit::docstore`'s tests pin that a version of 0 STORED
/// explicitly is a version like any other, so 0 here is this module's fallback and not
/// a sentinel the store understands.
#[test]
def test_an_absent_version_keeps_the_one_recorded : Bool :=
    let known : Option DocumentEdit := document_change (ld_json ld_f_change_no_version) (ld_store_of "file:///a.mo" "old" 1) in
    let unknown : Option DocumentEdit := document_change (ld_json ld_f_change_no_version) docstore_empty in
    String.beq (ld_stored_version known "file:///a.mo") "1"
        && String.beq (ld_stored known "file:///a.mo") "def f : I64 := 4"
        && String.beq (ld_stored_version unknown "file:///a.mo") "0"

/// A `didChange` that changes nothing is not a change. This is the debounce, and it is
/// the one assertion in this file that stands between a server and re-checking a file
/// on every keystroke.
#[test]
def test_a_did_change_to_the_same_text_is_not_a_change : Bool :=
    let e : Option DocumentEdit := document_change (ld_json ld_f_change) (ld_store_of "file:///a.mo" "def f : I64 := 3" 1) in
    String.beq (ld_changed_of e) "false"
        && String.beq (ld_stored_version e "file:///a.mo") "5"

// --- didClose ---

/// A close forgets the document -- the text is gone from the store, not merely marked
/// closed -- and reports itself as a change so the caller publishes the empty
/// diagnostic set. A URI left in the store would be re-checked by a later `didSave` for
/// a buffer the user no longer has open.
#[test]
def test_a_did_close_forgets_the_document : Bool :=
    let e : Option DocumentEdit := document_close (ld_json ld_f_close) (ld_store_of "file:///a.mo" "def f : I64 := 1" 1) in
    String.beq (ld_uri_of e) "file:///a.mo"
        && String.beq (ld_changed_of e) "true"
        && String.beq (ld_stored e "file:///a.mo") "<none>"
        && String.beq (ld_stored_version e "file:///a.mo") "<none>"
        && String.beq (ld_stored_count e) "0"

// --- Malformed notifications ---

/// A notification has no reply, so a malformed one is answered `Option.none` and the
/// server carries on. A crash here is not a bad error message: it is a server that
/// dies within seconds of a user typing something surprising, with no output to say
/// why.
#[test]
def test_a_malformed_did_open_is_not_an_edit : Bool :=
    String.beq (ld_uri_of (document_open (ld_json ld_f_no_doc) docstore_empty)) "<none>"
        && String.beq (ld_uri_of (document_open (ld_json ld_f_doc_no_uri) docstore_empty)) "<none>"
        && String.beq (ld_uri_of (document_open (ld_json ld_f_uri_int) docstore_empty)) "<none>"
        && String.beq (ld_uri_of (document_open (ld_json ld_f_open_no_text) docstore_empty)) "<none>"

/// The same for `didChange`, and the four shapes are four different code paths: no
/// `contentChanges` field, an empty array, an element with no `text`, and an absent
/// `textDocument`.
#[test]
def test_a_malformed_did_change_is_not_an_edit : Bool :=
    String.beq (ld_uri_of (document_change (ld_json ld_f_no_doc) docstore_empty)) "<none>"
        && String.beq (ld_uri_of (document_change (ld_json ld_f_doc_no_uri) docstore_empty)) "<none>"
        && String.beq (ld_uri_of (document_change (ld_json ld_f_change_no_changes) docstore_empty)) "<none>"
        && String.beq (ld_uri_of (document_change (ld_json ld_f_change_empty_array) docstore_empty)) "<none>"
        && String.beq (ld_uri_of (document_change (ld_json ld_f_change_no_text) docstore_empty)) "<none>"

/// And for `didClose`, which needs nothing but a URI and so is the one that would
/// silently accept a document named by a number.
#[test]
def test_a_malformed_did_close_is_not_an_edit : Bool :=
    String.beq (ld_uri_of (document_close (ld_json ld_f_no_doc) docstore_empty)) "<none>"
        && String.beq (ld_uri_of (document_close (ld_json ld_f_uri_int) docstore_empty)) "<none>"
        && String.beq (ld_uri_of (document_close (ld_json ld_f_doc_no_uri) docstore_empty)) "<none>"
