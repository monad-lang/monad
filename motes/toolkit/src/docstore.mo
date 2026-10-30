/// The open documents: what the client says each file currently contains, and
/// which revision of it that is.
///
/// WHY THE SERVER KEEPS ITS OWN COPY AT ALL is the first thing to be clear
/// about, because it looks like duplication. The client sends the buffer's text
/// with every change; the file on disk lags it by however long the user has gone
/// without saving. A server that read the file instead would diagnose the last
/// SAVED revision while the user looks at an unsaved one, so every squiggle
/// would be one edit behind -- the classic "the error is on the line above where
/// it says" complaint. The store is the buffer, and the disk is only consulted
/// for files no one has opened.
///
/// IT IS KEYED BY URI, NOT BY PATH, and that is the specification's model rather
/// than a convenience. A document's identity to the client is its URI, and the
/// same file reached by two URIs -- a symlink and its target, a path spelled with
/// and without a percent-escape -- is two documents as far as `didOpen` and
/// `didClose` are concerned. Keying by path would merge them and then deliver
/// `didClose` for one to the other. `docstore_path_of_uri` exists for the one
/// direction that must cross over: the checker is handed a PATH, so a URI is
/// turned into one when, and only when, a check runs.
///
/// THE VERSION IS KEPT EVEN THOUGH NOTHING HERE READS IT, because
/// `publishDiagnostics` may carry the version the diagnostics were computed
/// against, and a client that receives a version older than its buffer discards
/// the whole set. That is the correct behaviour -- stale squiggles are worse
/// than none -- but it means a server that reports the WRONG version silently
/// stops showing diagnostics for a file that is being edited. Keeping the number
/// here, next to the text it belongs to, is what makes reporting it correct by
/// construction: they are stored and read together or not at all.
///
/// SYNC IS FULL-TEXT ONLY. `didChange` replaces the whole buffer rather than
/// applying a range edit, which is what the server advertises
/// (`textDocumentSync: 1`) and what the Rust server being replaced does. The
/// `change` and `open` entry points are separate anyway, despite having the same
/// body today, because incremental sync would change exactly one of them -- and
/// the moment a range-edit path exists, a single shared entry point is the thing
/// that would let a `didOpen` be treated as an edit. When that day comes, only
/// `docstore_change` changes.
///
/// THE URI CODE IS PERCENT-AWARE, which is a difference from the tool being
/// replaced: `rust/rust-cli/src/lsp.rs`'s `uri_to_path` strips the `file://` prefix
/// and stops, so a path containing a space or any non-ASCII byte -- both of
/// which this repository's own filenames avoid but which are unremarkable
/// elsewhere -- would be handed to the checker as the literal text `%20` and
/// fail to open. LSP URIs are RFC 3986 URIs, so decoding is not optional.
use std::map {Map, BTreeMap, BTreeMap.to_list}

pub def docstore_uri_scheme : String := "file://"

// --- The stored document ---

/// One open buffer: the text the client last sent, and the version it came with.
///
/// The two are one struct rather than two maps because they are never useful
/// separately -- a version without its text names a revision nothing can be
/// checked against, and text without its version cannot be reported with a
/// version at all.
pub struct Doc {
  version : I64,
  text : String,
}

pub def doc_mk (version : I64) (text : String) : Doc := Doc.mk version text

pub def doc_version (d : Doc) : I64 := d.version

pub def doc_text (d : Doc) : String := d.text

// --- The store ---

/// The open documents, keyed by the URI the client used.
///
/// A `BTreeMap` rather than a `HashMap`: `docstore_uris` walks it in ascending
/// order, which makes a log line and a test expectation the same every run, and
/// a document's place in the store stops depending on a hash of its URI.
///
/// THE CARRIER IS PINNED BY `docstore_no_docs` AND THE THREE WRAPPERS BELOW,
/// and that is not decoration. Dictionary passing is SYNTACTIC
/// (`lang/scope.mo`'s `resolve_class_call_term`): it reads a class method's
/// carrier out of the term -- a qualified constructor, a literal's suffix, a
/// typed lambda/let parameter -- and where the only source is a DECLARED type
/// it falls through to `class_default_carrier`, which for `Map` is `HashMap`.
/// A struct FIELD's declared type is not such a source, so the `Map.empty`
/// this used to call built a `HashMap` inside a `BTreeMap String Doc` field,
/// and `docstore_uris`'s own `BTreeMap.to_list` then read a HashMap as a
/// BTreeMap: a tag mismatch, and a SIGSEGV in `monad_get_tag` under the
/// compiled compiler. The emitted IR is unambiguous -- `docstore_empty` called
/// `std.map::Map_HashMap_empty`, and no `Map_BTreeMap_*` function existed in
/// the program at all.
///
/// Nothing catches it at compile time (compiled, every value is an `i64`) and
/// nothing catches it under the Rust host, which resolves dictionaries during
/// typed elaboration. It reds the SWEEP, not the server: the compiled server's
/// own store stayed consistently HashMap, so only a `BTreeMap.*` call on it --
/// `docstore_uris`/`docstore_count`, which no server path reaches -- could
/// crash. `motes/lsp/src/checks.mo` carries the same trap on `CheckStore`.
///
/// `std/src/map.mo` has no `pub` decls, so naming `BTreeMap` in the filter above
/// raises `cross_mote_package_private` -- accepted deliberately, because the
/// empty filter that avoided it is now a hard error under the enforced `use`
/// completeness rule. See `jsonrpc.mo`'s import for the full argument.
pub struct DocStore {
  docs : BTreeMap String Doc,
}

/// The empty map, named so that its carrier comes from a declared type.
///
/// A nullary `Map.empty` offers the dictionary pass no carrier at all, so it
/// lands on the class default; a def's own declared return type is a source the
/// pass does read. This is the one place the store's map type is chosen, and
/// everything below is a `BTreeMap` because this is.
#[partial]
def docstore_no_docs : BTreeMap String Doc := Map.empty

/// The three operations the store performs, each with the map type in its
/// signature.
///
/// Wrappers rather than `Map.*` called at the point of use, for the reason the
/// struct doc gives: a field's declared type pins nothing, a typed parameter's
/// does -- which is the mechanism `std/src/map.mo`'s `instance Map BTreeMap`
/// already relies on for its own self-recursive calls.
#[partial]
def docstore_put (uri : String) (d : Doc) (m : BTreeMap String Doc) : BTreeMap String Doc :=
  Map.insert uri d m

#[partial]
def docstore_get (uri : String) (m : BTreeMap String Doc) : Option Doc := Map.lookup uri m

#[partial]
def docstore_drop (uri : String) (m : BTreeMap String Doc) : BTreeMap String Doc :=
  Map.delete uri m

pub def docstore_empty : DocStore := DocStore.mk docstore_no_docs

/// The document for a URI, if the client has one open.
pub def docstore_lookup (uri : String) (s : DocStore) : Option Doc := docstore_get uri s.docs

/// The text, if open. The caller that wants only the text should not have to
/// reach into a `Doc` for it.
pub def docstore_text (uri : String) (s : DocStore) : Option String :=
  match docstore_get uri s.docs {
    Option.none => Option.none,
    Option.some d => Option.some (doc_text d),
  }

/// The version, if open: what `publishDiagnostics` should report alongside the
/// diagnostics computed from the text this call's sibling returns.
pub def docstore_version (uri : String) (s : DocStore) : Option I64 :=
  match docstore_get uri s.docs {
    Option.none => Option.none,
    Option.some d => Option.some (doc_version d),
  }

/// `didOpen`. Replaces an entry that already exists rather than failing: a
/// second `didOpen` for the same URI is a client bug, and ignoring it would
/// leave the server checking the text from the first one for the rest of the
/// session, which is a far worse outcome than tolerating it.
pub def docstore_open (uri : String) (version : I64) (text : String) (s : DocStore) : DocStore :=
  DocStore.mk (docstore_put uri (doc_mk version text) s.docs)

/// `didChange`, full-text sync. See the module doc on why this is a separate
/// entry point from `docstore_open` despite the identical body, and on why an
/// unknown URI is inserted rather than ignored: the store's job is to hold what
/// the client last said a buffer contains, and refusing to record it would leave
/// that file diagnosed from the disk for the rest of the session with no error
/// anywhere to explain it.
pub def docstore_change (uri : String) (version : I64) (text : String) (s : DocStore) : DocStore :=
  DocStore.mk (docstore_put uri (doc_mk version text) s.docs)

/// `didClose`. Deleting a URI that was never opened is a no-op rather than an
/// error, for the same reason a repeated `didOpen` is tolerated: the client's
/// view is the authority on what is open, and the server's job is to end up
/// agreeing with it.
pub def docstore_close (uri : String) (s : DocStore) : DocStore :=
  DocStore.mk (docstore_drop uri s.docs)

/// How many documents are open. Used by the shutdown path's log line and by
/// tests; nothing makes a decision from it.
pub def docstore_count (s : DocStore) : I64 := docstore_count_go (BTreeMap.to_list s.docs) 0

#[partial]
def docstore_count_go (ps : List (Pair String Doc)) (n : I64) : I64 :=
  match ps {
    List.empty => n,
    List.cons _p rest => docstore_count_go rest (I64.add n 1),
  }

/// Every open URI, in ascending order.
///
/// Built from `BTreeMap.to_list`, because the `Map` class has no key-set
/// operation -- it is `empty`/`insert`/`lookup`/`delete` and nothing else -- and
/// `to_list` is the only way out of the map that yields the keys. That means the
/// pairs are made and then discarded, which costs an allocation per document;
/// with a handful of files open that is nothing, and the alternative is a
/// dependency on `BTreeMap`'s constructors, which would tie this module to one
/// map implementation. Ascending because a `BTreeMap`'s traversal is sorted, so
/// the order is a property of the type rather than of the walk.
pub def docstore_uris (s : DocStore) : List String :=
  docstore_strings_reverse (docstore_uris_of (BTreeMap.to_list s.docs) uri_no_strings)
    uri_no_strings

def uri_no_strings : List String := List.empty

/// Collect the keys of a `BTreeMap.to_list` result -- which is ASCENDING -- into
/// a cons-built list, which is therefore descending; the reverse above is what
/// turns it back. Written that way rather than with a right fold because this
/// module already has the reverse idiom for bytes and the alternative is an
/// accumulator threaded in the other direction, which reads no better.
#[partial]
def docstore_uris_of (ps : List (Pair String Doc)) (acc : List String) : List String :=
  match ps {
    List.empty => acc,
    List.cons p rest =>
      match p {
        Pair.pair k _v => docstore_uris_of rest (List.cons k acc),
      },
  }

#[partial]
def docstore_strings_reverse (ss : List String) (acc : List String) : List String :=
  match ss {
    List.empty => acc,
    List.cons s rest => docstore_strings_reverse rest (List.cons s acc),
  }

// --- URI to path ---

/// The filesystem path a `file:` URI names, or `Option.none` for a URI that has
/// no path this server can check.
///
/// Nothing but `file:` is accepted. An `untitled:` buffer has no path at all, and
/// a buffer from a remote scheme names a file that is not on this machine; both
/// are reported as "no path" and the caller skips the check, which is the honest
/// answer -- inventing a path from a URI the server cannot open would produce a
/// load failure that reads like a server bug.
///
/// The authority is honoured and then DISCARDED: `file://localhost/x` and
/// `file:///x` both name `/x`, which is what the specification says and what the
/// Rust server's prefix strip happens to get right for the three-slash form and
/// wrong for the other.
#[partial]
pub def docstore_path_of_uri (uri : String) : Option String :=
  if Bool.not (String.starts_with docstore_uri_scheme uri)
  then Option.none
  else
    match uri_path_part (String.drop (String.length docstore_uri_scheme) uri) {
      Option.none => Option.none,
      Option.some p => Option.some (uri_percent_decode p),
    }

/// The path part of what follows `file://`: everything from the first `/`, or
/// `Option.none` when there is no `/` at all.
///
/// This is where the authority (`localhost`, or a host name) is dropped, and the
/// two-slash case is why it cannot simply be "skip three characters": with
/// `file://localhost/x` the authority is present and with `file:///x` it is
/// empty, and only looking for the `/` handles both.
#[partial]
def uri_path_part (rest : String) : Option String :=
  if String.starts_with "/" rest
  then Option.some rest
  else
    let i : I64 := uri_slash_index (String.to_list rest) 0 in
    if I64.lt i 0 then Option.none else Option.some (String.drop i rest)

/// The index of the first `/`, or -1.
#[partial]
def uri_slash_index (bs : List U8) (i : I64) : I64 :=
  match bs {
    List.empty => 0 - 1,
    List.cons b rest => if U8.beq b uri_byte_slash then i else uri_slash_index rest (I64.add i 1),
  }

// --- Percent decoding ---

/// Decode every `%XX` escape, leaving anything that is not one alone.
///
/// A malformed escape -- `%ZZ`, `%2`, a trailing `%` -- is passed through as the
/// literal text it is, and the scan RESUMES IMMEDIATELY AFTER THE `%` rather than
/// after the two characters it would have consumed. That distinction matters for
/// input like `%2%41`, where the second escape is well formed: resuming after
/// the `%` decodes it to `A`, while consuming two characters would swallow the
/// `%4` and produce literal text. Neither answer is what a malformed URI
/// "means", since it has no meaning, but this one keeps every well-formed escape
/// in the string decoded.
///
/// Decoding is byte-wise and encoding-agnostic: `%C3%A9` becomes the two bytes
/// of a UTF-8 `é` because that is what the escape decodes to, with no need to
/// know or validate that it is a character. A sequence that decodes to something
/// that is not valid UTF-8 stays as those bytes, which is the right trade here:
/// the result is a path, handed to the operating system, which will reject it
/// more informatively than this function could.
#[partial]
pub def uri_percent_decode (s : String) : String :=
  String.from_list (uri_decode_go (String.to_list s) uri_no_bytes)

def uri_no_bytes : List U8 := List.empty

#[partial]
def uri_decode_go (bs : List U8) (acc : List U8) : List U8 :=
  match bs {
    List.empty => uri_bytes_reverse acc uri_no_bytes,
    List.cons b rest =>
      if U8.beq b uri_byte_percent
      then uri_decode_escape rest acc
      else uri_decode_go rest (List.cons b acc),
  }

/// A `%` has been consumed; `rest` is everything after it. The three ways to
/// have nothing to decode -- no characters left, one character left, or two that
/// are not hex -- all end at `uri_decode_go rest`, which is what re-examines the
/// text after the `%` under the rule the doc above states.
#[partial]
def uri_decode_escape (rest : List U8) (acc : List U8) : List U8 :=
  match rest {
    List.empty => uri_decode_go rest (List.cons uri_byte_percent acc),
    List.cons h r1 =>
      match r1 {
        List.empty => uri_decode_go rest (List.cons uri_byte_percent acc),
        List.cons l tail =>
          match uri_hex_pair h l {
            Option.none => uri_decode_go rest (List.cons uri_byte_percent acc),
            Option.some v => uri_decode_go tail (List.cons v acc),
          },
      },
  }

/// The byte two hex digits name.
#[partial]
def uri_hex_pair (h : U8) (l : U8) : Option U8 :=
  match uri_hex_value h {
    Option.none => Option.none,
    Option.some hi =>
      match uri_hex_value l {
        Option.none => Option.none,
        Option.some lo => Option.some (U8.add (U8.mul hi uri_sixteen) lo),
      },
  }

/// The value of one hex digit, or `Option.none` if it is not one.
///
/// Written entirely in `U8` arithmetic -- subtract the range's base, add ten for
/// the letters -- rather than widening to `I64` and narrowing back. `init` has no
/// `U8.to_i64`, and adding one for a sixteen-case lookup would be a larger change
/// to a shared module than the decode it serves; the arithmetic is four
/// operations on a value that is a byte by definition.
///
/// The ranges are written as "greater than the byte before the range and not
/// greater than its last", because `U8.lt` is not `pub` and `U8.gt` is.
#[partial]
def uri_hex_value (b : U8) : Option U8 :=
  if U8.gt b uri_byte_zero_minus_one && Bool.not (U8.gt b uri_byte_nine)
  then Option.some (U8.sub b uri_byte_zero)
  else if U8.gt b uri_byte_upper_a_minus_one && Bool.not (U8.gt b uri_byte_upper_f)
  then Option.some (U8.add (U8.sub b uri_byte_upper_a) uri_ten)
  else if U8.gt b uri_byte_lower_a_minus_one && Bool.not (U8.gt b uri_byte_lower_f)
  then Option.some (U8.add (U8.sub b uri_byte_lower_a) uri_ten)
  else Option.none

// --- Path to URI ---

/// The `file:` URI naming a path: the inverse of `docstore_path_of_uri`, for the
/// `Location`s this server sends back.
///
/// Hover sends no URI at all -- its contents are the answer -- but go-to-
/// definition and both symbol methods send a location, and a location names its
/// file as a URI. So the encode direction is needed by navigation even though
/// nothing needs it for reading the client's documents.
///
/// The escape set is minimal rather than maximal: a byte is left alone when it is
/// an unreserved character or `/`, and everything else is escaped. Minimal is the
/// safer direction of the two, because a URI that encodes more than it must still
/// decodes to the same path, while one that leaves a byte unescaped is relying on
/// the client to be lenient about a character the grammar does not allow there.
/// `/` is left alone deliberately even though encoding it would also round-trip:
/// a client showing the URI to a human is the common case, and a path is more
/// readable with its separators.
#[partial]
pub def docstore_uri_of_path (path : String) : String :=
  String.concat docstore_uri_scheme (uri_percent_encode path)

#[partial]
def uri_percent_encode (s : String) : String :=
  String.from_list (uri_bytes_reverse (uri_encode_go (String.to_list s) uri_no_bytes) uri_no_bytes)

#[partial]
def uri_encode_go (bs : List U8) (acc : List U8) : List U8 :=
  match bs {
    List.empty => acc,
    List.cons b rest =>
      if uri_byte_is_literal b
      then uri_encode_go rest (List.cons b acc)
      else
        let hi : U8 := U8.div b uri_sixteen in
        let lo : U8 := U8.sub b (U8.mul hi uri_sixteen) in
        uri_encode_go rest
          (List.cons (uri_hex_digit lo) (List.cons (uri_hex_digit hi) (List.cons uri_byte_percent acc))),
  }

/// Is this byte left as itself in a path? The unreserved set, plus `/`.
///
/// `-`, `.`, `_` and `~` are RFC 3986's four unreserved punctuation marks and
/// are listed by name rather than as ranges, since they are scattered across the
/// ASCII table and a range test for each would be four comparisons pretending to
/// be one.
#[partial]
def uri_byte_is_literal (b : U8) : Bool :=
  uri_byte_is_alpha b
    || (U8.gt b uri_byte_zero_minus_one && Bool.not (U8.gt b uri_byte_nine))
    || U8.beq b uri_byte_dash
    || U8.beq b uri_byte_dot
    || U8.beq b uri_byte_underscore
    || U8.beq b uri_byte_tilde
    || U8.beq b uri_byte_slash

#[partial]
def uri_byte_is_alpha (b : U8) : Bool :=
  (U8.gt b uri_byte_upper_a_minus_one && Bool.not (U8.gt b uri_byte_upper_z))
    || (U8.gt b uri_byte_lower_a_minus_one && Bool.not (U8.gt b uri_byte_lower_z))

/// A nibble as an UPPERCASE hex digit.
///
/// Uppercase because RFC 3986 says so -- the grammar's `HEXDIG` is case-
/// insensitive but the recommendation is uppercase, and every encoder a user is
/// likely to compare against uses it, so a diffable log stays diffable.
///
/// `uri_value_nine` and NOT `uri_byte_nine`, and the difference is the whole
/// content of this function: the first is the NUMBER nine, the second is the
/// ASCII code 57 for the CHARACTER `'9'`. Comparing the nibble against the byte
/// compiles, runs, and is correct for every nibble below ten, so the mistake is
/// invisible except in the letters -- `0xC3` encodes as `%<3` instead of `%C3`
/// and `0xA9` as `%:9` instead of `%A9`, which is to say every non-ASCII byte
/// and nothing else. Two constants whose values are nine and fifty-seven are not
/// interchangeable however similar their names look, which is why they are named
/// for what they ARE and not for the digit they happen to spell.
#[partial]
def uri_hex_digit (n : U8) : U8 :=
  if U8.gt n uri_value_nine then U8.add n uri_byte_upper_a_minus_ten else U8.add n uri_byte_zero

/// Reverse a byte list into `acc`. Local, like every other reverse in this mote:
/// `List.reverse` is a `lang` def that is not `pub`, and reversing five lines is
/// not worth a dependency edge on the compiler for.
#[partial]
def uri_bytes_reverse (bs : List U8) (acc : List U8) : List U8 :=
  match bs {
    List.empty => acc,
    List.cons b rest => uri_bytes_reverse rest (List.cons b acc),
  }

// --- Byte constants ---
//
// Named, because `U8.beq b 47u8` at a call site is a number a reader has to look
// up. The `_minus_one` variants are the byte BELOW a range's base: with no
// `U8.lt`, "at least 48" has to be written as "greater than 47".

pub def uri_byte_percent : U8 := 37u8

pub def uri_byte_slash : U8 := 47u8

pub def uri_byte_dash : U8 := 45u8

pub def uri_byte_dot : U8 := 46u8

pub def uri_byte_underscore : U8 := 95u8

pub def uri_byte_tilde : U8 := 126u8

def uri_byte_zero : U8 := 48u8

/// The ASCII code of `'9'`, used to bound the digit RANGE in `uri_hex_value` and
/// `uri_byte_is_literal`. Not the number nine -- that is `uri_value_nine`.
def uri_byte_nine : U8 := 57u8

/// The ASCII code of the byte below `'0'`, which is `'/'`. Written as a named
/// constant because with no `U8.lt`, "at least 48" has to be spelled "greater
/// than 47", and `47u8` at a range check reads like a magic number.
def uri_byte_zero_minus_one : U8 := 47u8

def uri_byte_upper_a : U8 := 65u8

def uri_byte_upper_f : U8 := 70u8

def uri_byte_upper_z : U8 := 90u8

def uri_byte_upper_a_minus_one : U8 := 64u8

def uri_byte_lower_a : U8 := 97u8

def uri_byte_lower_f : U8 := 102u8

def uri_byte_lower_z : U8 := 122u8

def uri_byte_lower_a_minus_one : U8 := 96u8

/// The number sixteen, the base a nibble pair is combined in.
def uri_sixteen : U8 := 16u8

/// The number ten, the offset a hex letter's value sits above its digit.
def uri_ten : U8 := 10u8

/// The number nine: the largest nibble that is still a DECIMAL digit, which is
/// what `uri_hex_digit` branches on. A value, not an ASCII code -- see that
/// function's doc for what happens when the two are confused.
def uri_value_nine : U8 := 9u8

/// `'A' - 10`. The offset a nibble above nine is added to, which is the whole of
/// the uppercase-hex table: 55 + 10 = 65 = `'A'`.
def uri_byte_upper_a_minus_ten : U8 := 55u8
