/// The four requests that answer with a place in the code: hover, definition,
/// `documentSymbol` and `workspace/symbol`.
///
/// HOVER AND DEFINITION ASK THE SAME QUESTION, and this module resolves it once.
/// Both are about the identifier under the cursor, and finding out which declaration
/// that identifier names -- through `lang`'s `nav_at_checked`, which is the
/// compiler's own `scope_resolve_name` -- is the whole of the work. What differs is
/// only which field of the answer is reported: hover shows `nav_target_detail` and
/// the identifier's extent, definition shows `nav_target_range` and the file. So
/// `lsp_cursor` resolves a cursor into a `Cursor` -- the identifier, its bytes, the
/// text, the line index, and the check -- and the two entry points below each read
/// what they want off it. A name that hovers and a name that jumps are then the same
/// set by construction, which is a property neither feature could have if each
/// resolved names on its own.
///
/// THE IDENTIFIER COMES FROM A TEXT SCAN, NOT FROM THE SYNTAX TREE, and that is the
/// one place this module is less precise than it could be. `text_identifier_at` finds
/// the run of identifier bytes containing the cursor, which is fast, total, and
/// correct for every cursor position a client can send -- including positions inside
/// comments and string literals, where there is no syntax tree node at all. The
/// alternative, walking the located term tree to the innermost node containing the
/// offset, would also decide which of two nested terms an identifier belongs to,
/// which matters for nothing here: the scan produces a NAME, and the name is resolved
/// by the compiler. Its one visible limit is that a run of bytes is not a scope, so a
/// local variable resolves to a top-level def of the same name -- inherited from the
/// resolver, and stated in `lang::navigation`'s own doc.
///
/// THE TEXT EVERY POSITION IS CONVERTED AGAINST IS THE CHECKED TEXT, which is why
/// these entry points take the check store and NOT the document store. A range from
/// the checker, a cursor position from the client, and the line index they meet in are
/// then all about one revision by construction rather than by agreement -- the
/// invariant being that the server re-checks a document whenever the client's text
/// changes, so a check is current whenever a request about the document is answered.
/// `documentSymbol` and `workspace/symbol` are the two exceptions to taking no
/// docstore: the second reads open buffers in preference to the disk (see
/// `lsp_file_text`), and neither depends on the invariant.
///
/// `documentSymbol` READS THE OUTLINE, NOT THE SCOPE, which is what makes the symbol
/// picker work in a file that does not compile. The declaration table survives a
/// truncated parse (`lang`'s `ranged_truncation` keeps the ranges and drops the
/// scope, deliberately), so a user who has just typed half a definition still gets
/// every other declaration in the file from the picker. Reading the scope instead
/// would answer nothing at exactly the moment the feature is most useful.
///
/// HOVER SHOWS A DECLARATION, NOT A TYPE. It renders the detail `lang::navigation`
/// composed -- a signature for a def, the whole declaration for a type or a class --
/// in a markdown fence, because a type's rendering is multi-line and a client that
/// reflowed it would destroy the layout that carries the meaning.
use json::json {Json}
use lang::module {
  DeclRange, RangedFileCheck, decl_range_kind, decl_range_name, decl_range_span,
  decl_ranges_of_source, ranged_file_ranges,
}
use lang::navigation {
  NavTarget, nav_at_checked, nav_target_detail, nav_target_file, nav_target_name,
  nav_target_range,
}
use lang::mote {read_file_or_none}
use lang::types {SourceRange}
use lsp::checks {Check, CheckStore, check_result, check_text, checkstore_lookup}
use lsp::documents {document_uri}
use lsp::params {lsp_param_nested_i64, lsp_param_str}
use toolkit::docstore {DocStore, docstore_text, docstore_uri_of_path}
use toolkit::jsonrpc {rpc_object}
use toolkit::position {
  LineIndex, PositionEncoding, WirePosition, line_index_of_source, offset_of_wire,
  wire_position_mk, wire_range_of_offsets,
}
use toolkit::text {
  TextSpan, text_identifier_at, text_span_start, text_span_stop, text_span_text,
}
use toolkit::wire {
  location_json_of_source_range, wire_range_json, wire_range_of_source_range,
}

// --- A resolved cursor ---

/// The identifier under the cursor, with everything needed to answer about it.
///
/// One struct rather than a tuple because six values travel together and three of them
/// are the same type: a `Pair` chain of `String`s is a bug waiting for a reviewer to
/// stop counting. `index` is here rather than rebuilt per use because both hover and
/// definition need it and building it is a pass over the whole buffer.
pub struct Cursor {
  uri : String,
  text : String,
  check : RangedFileCheck,
  index : LineIndex,
  ident : String,
  span : TextSpan,
}

pub def cursor_uri (c : Cursor) : String := c.uri

pub def cursor_text (c : Cursor) : String := c.text

pub def cursor_check (c : Cursor) : RangedFileCheck := c.check

pub def cursor_index (c : Cursor) : LineIndex := c.index

pub def cursor_ident (c : Cursor) : String := c.ident

pub def cursor_span (c : Cursor) : TextSpan := c.span

/// Resolve a request's cursor: which document, where in it, and what identifier is
/// there.
///
/// EVERY ABSENCE IS THE SAME ANSWER -- `Option.none` -- and the caller turns it into
/// a null result. A request about a document the client never opened, a position past
/// the end of the buffer, a cursor not on an identifier: a client is free to send all
/// three, and none is an error worth reporting to it. A null result is what the
/// specification says to send and is what every client renders as "nothing here".
#[partial]
pub def lsp_cursor (checks : CheckStore) (enc : PositionEncoding) (params : Json)
    : Option Cursor :=
  match document_uri params {
    Option.none => Option.none,
    Option.some uri =>
      match checkstore_lookup uri checks {
        Option.none => Option.none,
        Option.some ch => lsp_cursor_of_check uri ch enc params,
      },
  }

#[partial]
def lsp_cursor_of_check (uri : String) (ch : Check) (enc : PositionEncoding) (params : Json)
    : Option Cursor :=
  let text : String := check_text ch in
  lsp_cursor_in uri text (line_index_of_source text) (check_result ch) enc params

#[partial]
def lsp_cursor_in (uri : String) (text : String) (ix : LineIndex) (check : RangedFileCheck)
    (enc : PositionEncoding) (params : Json) : Option Cursor :=
  match lsp_position params {
    Option.none => Option.none,
    Option.some pos =>
      match offset_of_wire enc ix text pos {
        Option.none => Option.none,
        Option.some offset => lsp_cursor_at uri text ix check offset,
      },
  }

#[partial]
def lsp_cursor_at (uri : String) (text : String) (ix : LineIndex) (check : RangedFileCheck)
    (offset : I64) : Option Cursor :=
  match text_identifier_at text offset {
    Option.none => Option.none,
    Option.some span =>
      Option.some (Cursor.mk uri text check ix (text_span_text text span) span),
  }

/// `params.position`, the cursor.
///
/// A MISSING `character` IS 0 rather than a refusal: the specification requires both
/// fields, so a client that sends only a line has sent a bug, and reading its position
/// as the start of the line it named is both what it most likely meant and the only
/// reading that answers anything. A missing `line` is a refusal, because there is no
/// line to guess.
///
/// `lsp_param_nested_i64` reads through the `position` object, so the field names here
/// are `position.line` and `position.character` -- the nesting every request with a
/// cursor uses, and the reason `params.mo` has nested readers at all.
#[partial]
pub def lsp_position (params : Json) : Option WirePosition :=
  match lsp_param_nested_i64 "position" "line" params {
    Option.none => Option.none,
    Option.some line =>
      Option.some (wire_position_mk line (lsp_position_character params)),
  }

#[partial]
def lsp_position_character (params : Json) : I64 :=
  match lsp_param_nested_i64 "position" "character" params {
    Option.none => 0,
    Option.some c => c,
  }

// --- Hover ---

/// `textDocument/hover`: the identifier under the cursor, and what it declares.
///
/// The result is `{contents, range}`, the specification's `Hover`, and `contents` is
/// markdown so that a type's multi-line rendering keeps its shape (`lsp_markup`).
/// `range` is the identifier's own bytes, which is what a client underlines for the
/// user -- not the declaration's extent, which for a def in another file is not even
/// in this document.
#[partial]
pub def lsp_hover (checks : CheckStore) (enc : PositionEncoding) (params : Json) : Json :=
  match lsp_cursor checks enc params {
    Option.none => Json.make_null,
    Option.some c => lsp_hover_of_cursor enc c,
  }

#[partial]
def lsp_hover_of_cursor (enc : PositionEncoding) (c : Cursor) : Json :=
  match nav_at_checked (cursor_check c) (cursor_ident c) {
    Option.none => Json.make_null,
    Option.some t => lsp_hover_json enc c t,
  }

#[partial]
def lsp_hover_json (enc : PositionEncoding) (c : Cursor) (t : NavTarget) : Json :=
  rpc_object (List.cons (Pair.pair "contents" (lsp_markup (nav_target_detail t)))
    (lsp_hover_range enc c))

/// The `range` field, or NO FIELD AT ALL when the identifier's bytes cannot be placed
/// on the wire.
///
/// The absent field is a decision rather than an oversight: the specification makes
/// `range` optional and gives an absent one a meaning ("underline the word under the
/// cursor"), while a `range` present but null is neither optional nor a range -- it is
/// a malformed response a client may reject. So an unplaceable span produces a hover
/// with no range, which is a valid hover. The alternative, a range at the origin, is
/// the lie `wire.mo` refuses for jumps and would be no better here.
#[partial]
def lsp_hover_range (enc : PositionEncoding) (c : Cursor) : List (Pair String Json) :=
  match wire_range_of_offsets enc (cursor_index c) (cursor_text c)
      (text_span_start (cursor_span c)) (text_span_stop (cursor_span c)) {
    Option.none => List.empty,
    Option.some r => List.cons (Pair.pair "range" (wire_range_json r)) List.empty,
  }

/// A hover's `contents`: markdown, fenced, because the declaration being shown is
/// often several lines.
///
/// `show_inductive` renders a type as its whole declaration -- `type Color {`, one
/// constructor per line, `}` -- and in plaintext a client is free to reflow that into
/// a single line, which is precisely the information the rendering was carrying. A
/// fence keeps the lines: a client that renders markdown shows a code block, and one
/// that renders text shows the backticks, which still reads as a quotation of source.
///
/// `monad` as the fence's language is a hint no client knows, and it is the honest
/// one: a client that recognizes nothing shows the block unstyled, which is what a
/// user wants. Marking it as a language the client does know (`rust`, say) would
/// highlight Monad as something it is not.
#[partial]
pub def lsp_markup (detail : String) : Json :=
  rpc_object [
    Pair.pair "kind" (Json.make_str "markdown"),
    Pair.pair "value" (Json.make_str ("```monad\n" ++ detail ++ "\n```")),
  ]

/// An empty `Json` list, pinned by a def rather than written as a bare `List.empty` in
/// argument position -- the shape that resolved to the wrong instance in this
/// repository's `Map.empty` bug. `toolkit::diagnostic` names its own for the same
/// reason, and the cost is one line.
def lsp_no_symbols : List Json := List.empty

// --- Definition ---

/// `textDocument/definition`: where the identifier under the cursor is declared.
///
/// The result is an ARRAY of one location rather than a single location, which is the
/// shape the specification lists first and the one the most widely used servers send.
/// Both are accepted, so this is a choice about the future: a name can have more than
/// one declaration -- an ambiguous constructor is one case `lang::navigation` names --
/// and the array shape absorbs that without becoming a different response type.
///
/// This is a request in the IO sense: a target in another file is answered by reading
/// that file, which is `lsp_definition_far`.
#[partial]
pub def lsp_definition (checks : CheckStore) (enc : PositionEncoding) (params : Json) : IO Json := do {
    match lsp_cursor checks enc params {
        Option.none => return Json.make_null,
        Option.some c => lsp_definition_of_cursor enc c,
    }
}

#[partial]
def lsp_definition_of_cursor (enc : PositionEncoding) (c : Cursor) : IO Json :=
  match nav_at_checked (cursor_check c) (cursor_ident c) {
    Option.none => do { return Json.make_null },
    Option.some t => lsp_definition_of_target enc c t,
  }

/// The target's span in this file if it has one, and its declaration in its own file if
/// it does not.
///
/// THE TWO ARMS ARE THE TWO SHAPES A TARGET COMES IN, and the split is exact rather
/// than a fallback order: a range exists exactly when the declaration is in the file
/// whose ranges were consulted, and a file exists exactly when the target is a def the
/// scope resolved in another module. A type and a class carry no module at all -- see
/// `lang::navigation`'s stated limits -- so they never reach the second arm.
#[partial]
def lsp_definition_of_target (enc : PositionEncoding) (c : Cursor) (t : NavTarget) : IO Json :=
  match nav_target_range t {
    Option.some r => do { return (lsp_location_or_null enc (cursor_uri c) (cursor_index c) (cursor_text c) r) },
    Option.none => lsp_definition_far enc t,
  }

/// A definition in another file: read that file and find the declaration by name.
///
/// THE FILE READ IS THE HONEST WAY TO ANSWER THIS, and the alternative -- a location at
/// the start of the file, or no location at all -- is worse than it looks. A def in
/// another module reaches here as a FILE AND NO RANGE: the resolver names the module
/// that declared it and says nothing about where in that module's file it is written,
/// because `ModuleInfo` holds declarations and not positions. So the position has to
/// come from that file's own declaration table, which means reading the file, and that
/// table is keyed by the same name the resolution answered with -- the same agreement
/// `lang::navigation` relies on, read in the other direction. A jump that opens the
/// right file at the right line costs one read and one parse.
///
/// Past that, nothing. A file that cannot be read, or a name that is not in its outline,
/// answers NO LOCATION rather than a location at the origin: the origin is the lie
/// `toolkit::wire` refuses to tell, and a user who follows it lands at the top of a file
/// with no explanation. A null result is what a client renders as "no definition
/// found", which is the truth.
#[partial]
def lsp_definition_far (enc : PositionEncoding) (t : NavTarget) : IO Json := do {
    match nav_target_file t {
        Option.none => return Json.make_null,
        Option.some path => do {
            let text <- read_file_or_none (Path.path path);
            return (lsp_location_in_file enc path text (nav_target_name t))
        },
    }
}

/// The declaration called `name` in a file's text, as an array with one location in it
/// -- or null, which is what a client renders as "no definition".
#[partial]
def lsp_location_in_file (enc : PositionEncoding) (path : String) (text : Option String)
    (name : String) : Json :=
  match text {
    Option.none => Json.make_null,
    Option.some src => lsp_location_in_src enc (docstore_uri_of_path path) src name,
  }

/// The same, given text the caller already read.
///
/// The `let` sits in a def body rather than in the arm above, and that is not cosmetic:
/// an arm body holding a `let ... in` chain is the shape that aborts a parse and has it
/// reported at the NEXT declaration's header, so this file keeps every `let ... in` one
/// level out -- the form the corpus writes everywhere.
#[partial]
def lsp_location_in_src (enc : PositionEncoding) (uri : String) (src : String) (name : String)
    : Json :=
  let ix : LineIndex := line_index_of_source src in
  match lsp_decl_named (decl_ranges_of_source src) name {
    Option.none => Json.make_null,
    Option.some dr => lsp_location_or_null enc uri ix src (decl_range_span dr),
  }

/// One location, as the one-element array a client expects, or null.
///
/// The `Option` is composed away here rather than inside `toolkit::wire` because the two
/// callers disagree about what an unplaceable range means: this one is answering "where
/// is it?" and has no other answer to give, while `lsp_hover` has a whole response to
/// send with no range in it.
#[partial]
def lsp_location_or_null (enc : PositionEncoding) (uri : String) (ix : LineIndex) (text : String)
    (r : SourceRange) : Json :=
  match location_json_of_source_range uri enc ix text r {
    Option.none => Json.make_null,
    Option.some loc => Json.make_array (List.cons loc List.empty),
  }

/// The declaration called `name` in a list of ranges, or nothing.
///
/// A linear walk: a file's declarations number in the tens, the list is already in hand,
/// and the read happens once per jump. `lang`'s own `decl_ranges_of_source` is the same
/// shape for the same reason, in the same direction.
#[partial]
def lsp_decl_named (rs : List DeclRange) (name : String) : Option DeclRange :=
  match rs {
    List.empty => Option.none,
    List.cons dr rest =>
      if String.beq (decl_range_name dr) name
      then Option.some dr
      else lsp_decl_named rest name,
  }

// --- documentSymbol ---

/// `textDocument/documentSymbol`: the file's own outline.
///
/// READ FROM THE CHECK'S RANGES, so a document that does not compile still lists
/// everything the lenient parse read before it gave up -- which is the state a user is
/// in whenever they are halfway through typing a declaration and reach for the symbol
/// picker. The alternative source, the elaborated declarations, does not exist for a
/// broken file at all.
///
/// A document with no check -- never opened, or open with no path to check -- answers an
/// empty array, not an error: a client asks for the outline of documents it just opened,
/// and "nothing to show yet" is not a failure.
#[partial]
pub def lsp_document_symbol (checks : CheckStore) (enc : PositionEncoding) (params : Json)
    : Json :=
  match document_uri params {
    Option.none => Json.make_array lsp_no_symbols,
    Option.some uri =>
      match checkstore_lookup uri checks {
        Option.none => Json.make_array lsp_no_symbols,
        Option.some ch => lsp_symbols_of_check enc ch,
      },
  }

#[partial]
def lsp_symbols_of_check (enc : PositionEncoding) (ch : Check) : Json :=
  let text : String := check_text ch in
  Json.make_array (lsp_symbols_of enc text (line_index_of_source text)
    (ranged_file_ranges (check_result ch)))

#[partial]
def lsp_symbols_of (enc : PositionEncoding) (text : String) (ix : LineIndex)
    (rs : List DeclRange) : List Json :=
  match rs {
    List.empty => List.empty,
    List.cons dr rest =>
      match lsp_symbol_of enc text ix dr {
        Option.none => lsp_symbols_of enc text ix rest,
        Option.some j => List.cons j (lsp_symbols_of enc text ix rest),
      },
  }

/// One declaration as a `DocumentSymbol`, or nothing when its kind is not a symbol.
///
/// THE FILTER IS THE DESIGN. The outline carries every top-level declaration the file
/// has, including `use`, `open` and `macro`, because it is the compiler's table of what
/// a file declares; a symbol picker is a list of places a user wants to jump to, and an
/// import is not one. So the kinds with no `SymbolKind` -- see `lsp_symbol_kind` --
/// simply do not appear, which is the same five-kind filter the Rust server applied.
///
/// `range` AND `selectionRange` ARE THE SAME SPAN, which is a limitation and not a
/// simplification. The specification wants `range` to cover the declaration and
/// `selectionRange` to cover its NAME, and it requires `selectionRange` to be contained
/// by `range`. The declaration table records one span per declaration and no position
/// for its name, so the honest choice is the whole span for both -- an editor highlights
/// the declaration rather than the name, which is what the replaced server did and is
/// less precise rather than wrong.
#[partial]
def lsp_symbol_of (enc : PositionEncoding) (text : String) (ix : LineIndex) (dr : DeclRange)
    : Option Json :=
  match lsp_symbol_kind (decl_range_kind dr) {
    Option.none => Option.none,
    Option.some kind =>
      match wire_range_of_source_range enc ix text (decl_range_span dr) {
        Option.none => Option.none,
        Option.some r =>
          Option.some (rpc_object [
            Pair.pair "name" (Json.make_str (decl_range_name dr)),
            Pair.pair "kind" (Json.make_num_int kind),
            Pair.pair "range" (wire_range_json r),
            Pair.pair "selectionRange" (wire_range_json r),
          ]),
      },
  }

/// The LSP `SymbolKind` number for a declaration kind, or nothing when a picker should
/// not offer it.
///
/// THE FIVE NUMBERS ARE THE SPECIFICATION'S and the five kinds are `monad-core`'s, so
/// the picker shows what the replaced server showed: `def` 12 (Function), `struct` 23,
/// `class` 5, `type` 10 (Enum), `instance` 11 (Interface). `instance` as Interface is
/// the closest the vocabulary gets to a type class instance -- a set of methods a type
/// provides -- and `monad-core`'s own mapping says so in a comment.
#[partial]
pub def lsp_symbol_kind (kind : String) : Option I64 :=
  if String.beq kind "def" then Option.some 12
  else if String.beq kind "struct" then Option.some 23
  else if String.beq kind "class" then Option.some 5
  else if String.beq kind "type" then Option.some 10
  else if String.beq kind "instance" then Option.some 11
  else Option.none

// --- workspace/symbol ---

/// `workspace/symbol`: every declaration in the workspace whose name matches a query.
///
/// IT SCANS ON EVERY REQUEST, which is the one place this server trades responsiveness
/// for simplicity. The scan reads and parses every `.mo` file under the workspace root,
/// and a client calls this once per keystroke inside its symbol picker -- so the honest
/// description is that the picker is usable and not instant, and that the fix is a
/// cached index invalidated when a file is saved. It is a real index's worth of state
/// and a real invalidation problem (a buffer, a save, a file created outside the
/// editor), and it belongs in the change that measures the latency rather than in the
/// one that adds the feature. The Rust server this replaces made the same trade in a
/// comment: "no caching -- an accepted v1 tradeoff".
///
/// An absent query matches everything, which is the state a picker opens in.
#[partial]
pub def lsp_workspace_symbol (docs : DocStore) (root : Option String)
    (enc : PositionEncoding) (params : Json) : IO Json := do {
    match root {
        Option.none => return (Json.make_array lsp_no_symbols),
        Option.some dir => do {
            let files <- lsp_mo_files dir;
            let items <- lsp_workspace_items docs enc files (lsp_query params);
            return (Json.make_array items)
        },
    }
}

/// The query, lowercased once so the per-name comparison is not re-lowering it.
#[partial]
def lsp_query (params : Json) : String :=
  String.to_lowercase (lsp_query_raw params)

/// An absent `query` is the empty string, which matches every name -- so a client that
/// sends no query gets the whole workspace, which is what the specification's `""`
/// means. A non-string query gets the same, because no other reading of it answers a
/// question the client could have meant.
#[partial]
def lsp_query_raw (params : Json) : String :=
  match lsp_param_str "query" params {
    Option.none => "",
    Option.some q => q,
  }

#[partial]
def lsp_workspace_items (docs : DocStore) (enc : PositionEncoding) (files : List String)
    (query : String) : IO (List Json) := do {
    match files {
        List.empty => return List.empty,
        List.cons path rest => do {
            let text <- lsp_file_text docs path;
            let here := lsp_items_in_file enc path text query;
            let more <- lsp_workspace_items docs enc rest query;
            return (List.append here more)
        },
    }
}

/// Every matching declaration in one file, given its text if it could be read.
#[partial]
def lsp_items_in_file (enc : PositionEncoding) (path : String) (text : Option String)
    (query : String) : List Json :=
  match text {
    Option.none => List.empty,
    Option.some src => lsp_items_in_src enc (docstore_uri_of_path path) src query,
  }

#[partial]
def lsp_items_in_src (enc : PositionEncoding) (uri : String) (src : String) (query : String)
    : List Json :=
  let ix : LineIndex := line_index_of_source src in
  lsp_items_of enc uri src ix (decl_ranges_of_source src) query

#[partial]
def lsp_items_of (enc : PositionEncoding) (uri : String) (src : String) (ix : LineIndex)
    (rs : List DeclRange) (query : String) : List Json :=
  match rs {
    List.empty => List.empty,
    List.cons dr rest =>
      match lsp_symbol_info enc uri src ix dr query {
        Option.none => lsp_items_of enc uri src ix rest query,
        Option.some j => List.cons j (lsp_items_of enc uri src ix rest query),
      },
  }

/// One `SymbolInformation`: the same kind filter as `documentSymbol`, and a location
/// rather than a bare range, because the declaration is not in the client's open
/// document -- it is in a file the client may never have opened.
#[partial]
def lsp_symbol_info (enc : PositionEncoding) (uri : String) (src : String) (ix : LineIndex)
    (dr : DeclRange) (query : String) : Option Json :=
  match lsp_symbol_kind (decl_range_kind dr) {
    Option.none => Option.none,
    Option.some kind =>
      if lsp_name_matches (decl_range_name dr) query
      then lsp_symbol_info_of enc uri src ix dr kind
      else Option.none,
  }

#[partial]
def lsp_symbol_info_of (enc : PositionEncoding) (uri : String) (src : String) (ix : LineIndex)
    (dr : DeclRange) (kind : I64) : Option Json :=
  match location_json_of_source_range uri enc ix src (decl_range_span dr) {
    Option.none => Option.none,
    Option.some loc =>
      Option.some (rpc_object [
        Pair.pair "name" (Json.make_str (decl_range_name dr)),
        Pair.pair "kind" (Json.make_num_int kind),
        Pair.pair "location" loc,
      ]),
  }

/// Whether a name matches the query, case-insensitively and by substring.
///
/// The name is lowered here rather than the query being matched two ways, so the cost is
/// one lowering per declaration and the rule is one rule. A substring rather than a
/// prefix because a picker is a search box: a user typing `file` is looking for
/// `write_file` as readily as for `file_exists`.
///
/// AN EMPTY QUERY MATCHES EVERYTHING, which is what makes the picker's initial listing
/// the whole workspace, and it comes from `String.contains`'s own definition
/// (`list_contains` answers `List.is_empty needle` on an empty haystack) rather than
/// from a special case here. Worth knowing rather than relying on silently: it is a
/// property of a def in `init`, one edit away from being different.
#[partial]
def lsp_name_matches (name : String) (query : String) : Bool :=
  String.contains (String.to_lowercase name) query

// --- The workspace walk ---

/// Every `.mo` file under a directory, recursively.
#[partial]
def lsp_mo_files (dir : String) : IO (List String) := do {
    let is_dir <- IO.is_dir (Path.path dir);
    if is_dir
    then do {
        let entries <- IO.list_dir (Path.path dir);
        lsp_mo_files_in dir entries List.empty
    }
    else return List.empty
}

#[partial]
def lsp_mo_files_in (dir : String) (entries : List Path) (acc : List String)
    : IO (List String) := do {
    match entries {
        List.empty => return acc,
        List.cons entry rest => lsp_mo_entry dir entry rest acc
    }
}

/// One directory entry: a subdirectory to walk, a `.mo` file to keep, or neither.
#[partial]
def lsp_mo_entry (dir : String) (entry : Path) (rest : List Path) (acc : List String)
    : IO (List String) := do {
    let full := Path.to_string entry;
    let is_dir <- IO.is_dir entry;
    if lsp_walk_into (Path.file_name entry) is_dir
    then do {
        let sub <- lsp_mo_files full;
        lsp_mo_files_in dir rest (List.append acc sub)
    }
    else lsp_mo_file_entry dir full is_dir rest acc
}

/// A non-directory entry: kept when it is a `.mo` file, skipped otherwise.
#[partial]
def lsp_mo_file_entry (dir : String) (full : String) (is_dir : Bool) (rest : List Path)
    (acc : List String) : IO (List String) :=
  if lsp_keep_mo full is_dir
  then do { lsp_mo_files_in dir rest (List.append acc (List.cons full List.empty)) }
  else do { lsp_mo_files_in dir rest acc }

/// Whether a directory entry is a directory to walk into.
///
/// HIDDEN AND BUILD DIRECTORIES ARE SKIPPED, and the difference from the walk this
/// replaces is deliberate. The Rust server recursed into everything and relied on the
/// `.mo` filter to find nothing, which is correct and pays a directory read per entry in
/// trees that hold no source at all. `.git` holds directories named like hex, and
/// `target/` in this repository holds tens of thousands of them; neither can hold a
/// `.mo` file anyone wants in a symbol picker, since generated source is not a
/// declaration the user wrote.
#[partial]
def lsp_walk_into (name : String) (is_dir : Bool) : Bool :=
  if lsp_hidden name then false else is_dir

/// Whether a directory entry is a `.mo` file to keep.
#[partial]
def lsp_keep_mo (name : String) (is_dir : Bool) : Bool :=
  if is_dir then false else String.ends_with name ".mo"

/// A name a walk should not descend into: a dotfile, or the build directory.
#[partial]
def lsp_hidden (name : String) : Bool :=
  String.starts_with "." name || String.beq name "target"

/// A file's text: the client's buffer if the document is open, and the file on disk
/// otherwise.
///
/// THE BUFFER WINS when there is one, and it is the difference between a picker that
/// knows a def the user typed ten seconds ago and one that knows the file as it was last
/// saved. A search over symbols is a search over what the user can see, and what they
/// can see is the buffer. The disk is the fallback rather than the source, and it covers
/// every file the editor has not opened -- which is most of the workspace.
#[partial]
def lsp_file_text (docs : DocStore) (path : String) : IO (Option String) := do {
    match docstore_text (docstore_uri_of_path path) docs {
        Option.some text => return (Option.some text),
        Option.none => read_file_or_none (Path.path path)
    }
}

