/// Docstore tests: the store's lifecycle, and the URI code in both directions.
///
/// THE URI SECTION IS THE ONE THAT MATTERS MOST, and it is where the tool being
/// replaced is wrong rather than merely different. Every expectation below that
/// involves an escape was computed by hand from RFC 3986 and then checked against
/// a run -- `%20` is a space, `%2F` is a slash, `+` is NOT a space (that is the
/// `application/x-www-form-urlencoded` rule, a different encoding that shares the
/// `%` syntax), and `%C3%A9` is the two UTF-8 bytes of `é`. A server that got any
/// of those wrong would work perfectly on every path in this repository and fail
/// on the first user path with a space in it, which is the kind of bug that is
/// only ever found by a user.
///
/// The store tests are lifecycle-shaped because that is all the store has: the
/// interesting cases are all "the client said something twice" or "the client
/// said something out of order", which is what a long-lived server sees and a
/// single-shot tool never does.
///
/// Field reads go through typed accessor defs (`dc_*`), never inline in a
/// `#[test]` def, per this repo's recorded `#[test]` plus struct-field codegen
/// hazard. The `dc_` prefix is collision-avoiding: whole-program scope is shared
/// with every other mote's tests.
use toolkit::docstore {
    Doc, DocStore, doc_mk, doc_text, doc_version, docstore_change, docstore_close, docstore_count,
    docstore_empty, docstore_lookup, docstore_open, docstore_path_of_uri, docstore_text,
    docstore_uri_of_path, docstore_uris, docstore_version,
}

// --- Accessors and renderers ---
//
// Every `Option` is rendered to a string before it is compared, so each test
// below is one `String.beq` rather than a match. `<none>` cannot be produced by
// any of these functions, so an assertion that sees it knows the `Option` was
// empty rather than silently comparing against a plausible path.

def dc_text_of (o : Option String) : String :=
    match o {
        Option.none => "<none>",
        Option.some s => s,
    }

def dc_ver_of (o : Option I64) : String :=
    match o {
        Option.none => "<none>",
        Option.some n => I64.to_string n,
    }

/// The open URIs joined with `|` and a LEADING separator, so that the empty store
/// and a store holding one empty-named document are different strings. Written by
/// hand rather than with `List.intercalate`, which is not `pub` in `init`.
def dc_uris (s : DocStore) : String := dc_join (docstore_uris s) ""

#[partial]
def dc_join (ss : List String) (acc : String) : String :=
    match ss {
        List.empty => acc,
        List.cons s rest => dc_join rest (String.concat acc (String.concat "|" s)),
    }

/// Two documents, opened in the order `b` then `a`, so every test that uses this
/// also exercises the map's own ordering rather than the insertion order.
def dc_two : DocStore :=
    docstore_open "file:///b.mo" 2 "def b : I64 := 2\n"
        (docstore_open "file:///a.mo" 1 "def a : I64 := 1\n" docstore_empty)

// --- The store's life cycle ---

/// An empty store answers nothing for anything, and the three questions a caller
/// can ask -- is it there, what is its text, what is its version -- all agree.
#[test]
def test_an_empty_store_holds_nothing : Bool :=
    I64.beq (docstore_count docstore_empty) 0
        && String.beq (dc_uris docstore_empty) ""
        && String.beq (dc_text_of (docstore_text "file:///a.mo" docstore_empty)) "<none>"
        && String.beq (dc_ver_of (docstore_version "file:///a.mo" docstore_empty)) "<none>"

/// `didOpen` records both the text and the version that came with it, which is
/// the pair every later question is answered from.
#[test]
def test_open_records_the_text_and_the_version : Bool :=
    let s : DocStore := docstore_open "file:///a.mo" 7 "hello" docstore_empty in
    String.beq (dc_text_of (docstore_text "file:///a.mo" s)) "hello"
        && String.beq (dc_ver_of (docstore_version "file:///a.mo" s)) "7"
        && I64.beq (docstore_count s) 1

/// A second `didOpen` for the same URI REPLACES rather than adds. The count is
/// the assertion that matters: an insert that appended would leave two documents
/// under one key, which a map physically cannot do, but the same mistake made one
/// level up -- a list of open documents instead of a map -- would.
#[test]
def test_a_second_open_replaces_the_first : Bool :=
    let s : DocStore := docstore_open "file:///a.mo" 2 "second" (docstore_open "file:///a.mo" 1 "first" docstore_empty)
    in
    String.beq (dc_text_of (docstore_text "file:///a.mo" s)) "second"
        && String.beq (dc_ver_of (docstore_version "file:///a.mo" s)) "2"
        && I64.beq (docstore_count s) 1

/// `didChange` replaces the text AND advances the version. Both halves matter: a
/// server that kept the old version would report diagnostics the client discards
/// as stale, and one that kept the old text would diagnose a revision the user
/// edited away from.
#[test]
def test_change_replaces_the_text_and_the_version : Bool :=
    let s : DocStore := docstore_change "file:///a.mo" 4 "edited" (docstore_open "file:///a.mo" 3 "original" docstore_empty)
    in
    String.beq (dc_text_of (docstore_text "file:///a.mo" s)) "edited"
        && String.beq (dc_ver_of (docstore_version "file:///a.mo" s)) "4"

/// A change for a URI that was never opened is RECORDED, not dropped. It is a
/// client bug, but the alternatives are worse: ignoring it leaves the file
/// checked from the disk for the rest of the session with nothing to explain
/// why, and refusing it means a server that is silently behind a client that
/// believes it is in sync.
#[test]
def test_a_change_for_an_unopened_uri_is_recorded : Bool :=
    let s : DocStore := docstore_change "file:///new.mo" 1 "text" docstore_empty in
    String.beq (dc_text_of (docstore_text "file:///new.mo" s)) "text"
        && I64.beq (docstore_count s) 1

/// `didClose` removes the document, and closing one document leaves the other
/// alone -- the assertion that would fail if `close` returned a fresh empty store
/// rather than a store without that key.
#[test]
def test_close_removes_only_that_document : Bool :=
    let s : DocStore := docstore_close "file:///a.mo" dc_two in
    I64.beq (docstore_count s) 1
        && String.beq (dc_text_of (docstore_text "file:///a.mo" s)) "<none>"
        && String.beq (dc_text_of (docstore_text "file:///b.mo" s)) "def b : I64 := 2\n"

/// Closing a URI that was never open is a no-op rather than an error or a
/// corruption. A client that sends `didClose` twice is not doing anything the
/// server should refuse, and the count proves nothing was invented.
#[test]
def test_closing_an_unknown_uri_is_a_no_op : Bool :=
    I64.beq (docstore_count (docstore_close "file:///nope.mo" dc_two)) 2
        && I64.beq (docstore_count (docstore_close "file:///nope.mo" docstore_empty)) 0

/// The URI list is ASCENDING, not insertion order: `dc_two` was built `b` then
/// `a` and the answer is `a` then `b`. Worth pinning because a `HashMap` -- the
/// `Map` class's default carrier -- would give insertion-independent but
/// arbitrary order here, so this test is also what would fail if the store's
/// annotation were ever dropped.
#[test]
def test_the_uri_list_is_sorted : Bool :=
    String.beq (dc_uris dc_two) "|file:///a.mo|file:///b.mo"

/// Two open documents are independent: changing one does not touch the other's
/// text or version. Obvious, and the failure mode it rules out -- a store whose
/// `insert` replaced the whole map instead of one key -- is not detectable from
/// any single-document test.
#[test]
def test_changing_one_document_leaves_the_other_alone : Bool :=
    let s : DocStore := docstore_change "file:///a.mo" 9 "changed a" dc_two in
    String.beq (dc_text_of (docstore_text "file:///a.mo" s)) "changed a"
        && String.beq (dc_ver_of (docstore_version "file:///a.mo" s)) "9"
        && String.beq (dc_text_of (docstore_text "file:///b.mo" s)) "def b : I64 := 2\n"
        && String.beq (dc_ver_of (docstore_version "file:///b.mo" s)) "2"

/// A `Doc` carries the two fields together, which is what makes it impossible to
/// report diagnostics against one revision of a text and one of another.
#[test]
def test_a_doc_carries_its_version_and_text_together : Bool :=
    let d : Doc := doc_mk 12 "body" in
    I64.beq (doc_version d) 12 && String.beq (doc_text d) "body"

/// The lookup and the two convenience readers agree, so a caller can use
/// whichever it needs without two of them being able to drift.
#[test]
def test_lookup_agrees_with_the_text_and_version_readers : Bool :=
    match docstore_lookup "file:///a.mo" dc_two {
        Option.none => false,
        Option.some d =>
            I64.beq (doc_version d) 1 && String.beq (doc_text d) "def a : I64 := 1\n",
    }

/// A version of zero is a version, not an absence. `didOpen`'s version is a
/// client-supplied counter and zero is a legal value for the first message; the
/// `Option` is what distinguishes "not open" from "version 0", and a store that
/// used 0 as a sentinel would report this document as closed.
#[test]
def test_version_zero_is_not_an_absence : Bool :=
    let s : DocStore := docstore_open "file:///z.mo" 0 "" docstore_empty in
    String.beq (dc_ver_of (docstore_version "file:///z.mo" s)) "0"

/// An empty text is a text. Deleting the buffer's contents is an edit like any
/// other, and the diagnostics for it must be the empty set -- not "no
/// diagnostics because the file is not open".
#[test]
def test_an_empty_buffer_is_open_and_empty : Bool :=
    let s : DocStore := docstore_open "file:///z.mo" 1 "" docstore_empty in
    String.beq (dc_text_of (docstore_text "file:///z.mo" s)) ""

// --- URI to path ---

/// The three-slash form, which is what every client sends for a local file.
#[test]
def test_a_plain_file_uri_becomes_its_path : Bool :=
    String.beq (dc_text_of (docstore_path_of_uri "file:///a/b.mo")) "/a/b.mo"

/// The authority is honoured and then dropped: `localhost` names this machine,
/// so the path is `/x` either way.
#[test]
def test_a_localhost_authority_is_dropped : Bool :=
    String.beq (dc_text_of (docstore_path_of_uri "file://localhost/x/y.mo")) "/x/y.mo"

/// An authority with no path at all names no file, so it is refused rather than
/// turned into an empty path. An empty path handed to `read_file` names the
/// current directory, which would fail in a way that looks like a server bug.
#[test]
def test_an_authority_with_no_path_is_refused : Bool :=
    String.beq (dc_text_of (docstore_path_of_uri "file://host")) "<none>"
        && String.beq (dc_text_of (docstore_path_of_uri "file://")) "<none>"

/// A scheme that is not `file:` has no path this server can check. `untitled:`
/// buffers are the ones a user will actually hit -- an unsaved buffer being
/// edited in the editor -- and the correct answer is to skip the check rather
/// than to invent a filename.
#[test]
def test_a_non_file_uri_is_refused : Bool :=
    String.beq (dc_text_of (docstore_path_of_uri "untitled:Untitled-1")) "<none>"
        && String.beq (dc_text_of (docstore_path_of_uri "http://example.com/a.mo")) "<none>"
        && String.beq (dc_text_of (docstore_path_of_uri "/a/b.mo")) "<none>"
        && String.beq (dc_text_of (docstore_path_of_uri "")) "<none>"

/// THE CASE THE RUST SERVER GETS WRONG: a space arrives as `%20`, and a server
/// that only strips the scheme hands `%20` to the checker as three literal
/// characters, which no file is named.
#[test]
def test_a_percent_escaped_space_becomes_a_space : Bool :=
    String.beq (dc_text_of (docstore_path_of_uri "file:///a%20b.mo")) "/a b.mo"

/// An already-literal space passes through unchanged: decoding is a no-op on text
/// that has nothing to decode, which is what keeps the common case free of any
/// dependence on this code being right.
#[test]
def test_a_literal_space_passes_through : Bool :=
    String.beq (dc_text_of (docstore_path_of_uri "file:///a b.mo")) "/a b.mo"

/// A non-ASCII path arrives as UTF-8 percent-escapes, and decoding is byte-wise,
/// so `%C3%A9` becomes the two bytes of `é` with no need to know it is a
/// character.
#[test]
def test_a_utf8_escape_becomes_the_character : Bool :=
    String.beq (dc_text_of (docstore_path_of_uri "file:///caf%C3%A9.mo")) "/café.mo"

/// An escaped slash decodes to a slash. This is the one escape whose decoding
/// changes the SHAPE of the path rather than just its bytes, and it is correct:
/// the client escaped the slash precisely because it is part of a filename and
/// not a separator, but the filesystem this server hands it to has no way to
/// express that -- a filename containing a slash is impossible on Unix, so a
/// client that sends `%2F` is sending something that cannot exist. Decoding it
/// gives a path that will fail to open, with an error naming the real path,
/// which is more use than any alternative.
#[test]
def test_an_escaped_slash_decodes_to_a_slash : Bool :=
    String.beq (dc_text_of (docstore_path_of_uri "file:///a%2Fb.mo")) "/a/b.mo"

/// Lowercase hex is hex. The grammar's `HEXDIG` is case-insensitive and clients
/// differ; this server must not.
#[test]
def test_lowercase_hex_escapes_decode_too : Bool :=
    String.beq (dc_text_of (docstore_path_of_uri "file:///a%2fb.mo")) "/a/b.mo"
        && String.beq (dc_text_of (docstore_path_of_uri "file:///caf%c3%a9.mo")) "/café.mo"

/// `+` is NOT a space. That rule belongs to `application/x-www-form-urlencoded`,
/// a different encoding that shares the `%` syntax, and applying it here would
/// corrupt every path with a plus sign in it.
#[test]
def test_a_plus_is_a_plus : Bool :=
    String.beq (dc_text_of (docstore_path_of_uri "file:///a+b.mo")) "/a+b.mo"

/// A malformed escape is left as written rather than dropped or decoded to
/// something invented: the path is then wrong, but it is wrong in a way a reader
/// can see by looking at the URI.
#[test]
def test_a_malformed_escape_is_left_alone : Bool :=
    String.beq (dc_text_of (docstore_path_of_uri "file:///a%ZZb.mo")) "/a%ZZb.mo"
        && String.beq (dc_text_of (docstore_path_of_uri "file:///a%2")) "/a%2"
        && String.beq (dc_text_of (docstore_path_of_uri "file:///a%")) "/a%"

/// The subtle one: after a malformed escape the scan resumes right after the `%`,
/// so a well-formed escape that follows still decodes. Consuming two characters
/// on failure instead would swallow the `%4` here and produce literal text.
#[test]
def test_a_good_escape_after_a_bad_one_still_decodes : Bool :=
    String.beq (dc_text_of (docstore_path_of_uri "file:///a%2%41b.mo")) "/a%2Ab.mo"

/// The root path, which is the degenerate case of the authority rule: three
/// slashes and nothing else is a path of `/`, not an empty authority followed by
/// nothing.
#[test]
def test_the_root_path_is_a_path : Bool :=
    String.beq (dc_text_of (docstore_path_of_uri "file:///")) "/"

// --- Path to URI ---

/// The plain direction: a path with nothing to escape comes back with the scheme
/// in front of it, three slashes and all.
#[test]
def test_a_plain_path_becomes_a_file_uri : Bool :=
    String.beq (docstore_uri_of_path "/a/b.mo") "file:///a/b.mo"

/// A space is escaped, uppercase hex.
#[test]
def test_a_space_is_escaped : Bool :=
    String.beq (docstore_uri_of_path "/a b.mo") "file:///a%20b.mo"

/// A non-ASCII byte is escaped as its UTF-8 bytes, one escape per byte -- `é` is
/// `%C3%A9` and not a single escape, because the grammar has no way to name a
/// character above `0x7f`.
#[test]
def test_a_non_ascii_byte_is_escaped_as_utf8 : Bool :=
    String.beq (docstore_uri_of_path "/café.mo") "file:///caf%C3%A9.mo"

/// A percent sign in a path is escaped, which is what makes the round trip below
/// work: without it, encoding a path that already contains an escape-looking
/// sequence would produce a URI that decodes to something else.
#[test]
def test_a_percent_is_itself_escaped : Bool :=
    String.beq (docstore_uri_of_path "/a%20b.mo") "file:///a%2520b.mo"

/// The four unreserved punctuation marks and the slash are left alone, which is
/// the whole of the "minimal" rule: a URI that encodes more than it must still
/// round-trips, but it is less readable to a human and no client needs it.
#[test]
def test_the_unreserved_marks_and_slashes_are_left_alone : Bool :=
    String.beq (docstore_uri_of_path "/a-b_c.d~e/f.mo") "file:///a-b_c.d~e/f.mo"

/// THE PROPERTY THAT MATTERS: for any path this server produces, encoding it and
/// decoding it again gives the path back. A path is what the span table and the
/// loader work in, so a round trip that changed it would put every definition
/// jump in the wrong file -- and for a file with an unescaped-looking sequence in
/// its name, only the round trip catches it.
#[test]
def test_a_path_survives_the_round_trip : Bool :=
    let p : String := "/tmp/monad a%20é/b-c_d.mo~x" in
    String.beq (dc_text_of (docstore_path_of_uri (docstore_uri_of_path p))) p

/// The same property on the cases the hand-written assertions above cover, so
/// that the round trip is pinned for the shapes a real editor produces and not
/// only for the synthetic one.
#[test]
def test_the_round_trip_holds_for_every_shape_above : Bool :=
    let a : String := "/a/b.mo" in
    let b : String := "/a b.mo" in
    let c : String := "/café.mo" in
    let d : String := "/a%20b.mo" in
    let e : String := "/a+b.mo" in
    let f : String := "/" in
    dc_round_trips a && dc_round_trips b && dc_round_trips c && dc_round_trips d
        && dc_round_trips e && dc_round_trips f

#[partial]
def dc_round_trips (p : String) : Bool :=
    String.beq (dc_text_of (docstore_path_of_uri (docstore_uri_of_path p))) p

/// A URI built from a path that is already a URI is not a thing this server must
/// handle -- `docstore_uri_of_path` takes a path and would escape the colons --
/// but the escape is what keeps the two directions from being confusable, and
/// this pins that the scheme is not special-cased inside the path.
#[test]
def test_a_colon_inside_a_path_is_escaped : Bool :=
    String.beq (docstore_uri_of_path "/a:b.mo") "file:///a%3Ab.mo"
