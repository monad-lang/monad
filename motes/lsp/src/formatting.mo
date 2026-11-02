/// `textDocument/formatting`: the open buffer through `monad fmt`'s formatter.
///
/// The answer is one edit replacing the whole document, or no edits when the
/// buffer is already formatted. The formatter preserves line breaks and only
/// moves whitespace, so a whole-document edit is what it produces anyway and a
/// client keeps the cursor on its line.
///
/// The client's `FormattingOptions` are ignored: the style is the repository's
/// canonical one (`FmtConfig.default`), the same one `monad fmt --check` holds
/// files to, so a file formatted in an editor passes the CI gate.
use fmt::fmt {Fmt.default_config, Fmt.format_source}
use json::json {Json}
use lsp::documents {document_uri}
use toolkit::docstore {DocStore, docstore_text}
use toolkit::jsonrpc {rpc_object}
use toolkit::position {PositionEncoding, WireRange, line_index_of_source, wire_range_of_offsets}
use toolkit::wire {wire_range_json}

/// The edits for the document `params` names, or why there are none to give.
/// A document that is not open is an error: a client only formats what it has
/// open, so the request and the store disagree.
#[partial]
pub def lsp_formatting (docs : DocStore) (enc : PositionEncoding) (params : Json)
    : Result String Json :=
    match document_uri params {
        Option.none => Result.err "formatting: no textDocument.uri",
        Option.some uri =>
            match docstore_text uri docs {
                Option.none => Result.err ("formatting: not open: " ++ uri),
                Option.some text => lsp_format_text enc text,
            },
    }

/// The edits that take `text` to its formatted form.
#[partial]
pub def lsp_format_text (enc : PositionEncoding) (text : String) : Result String Json :=
    match Fmt.format_source Fmt.default_config text {
        Result.err e => Result.err ("formatting: " ++ e.message),
        Result.ok out =>
            if String.beq out text
            then Result.ok (Json.make_array List.empty)
            else lsp_whole_document_edit enc text out,
    }

#[partial]
def lsp_whole_document_edit (enc : PositionEncoding) (text : String) (out : String)
    : Result String Json :=
    match wire_range_of_offsets enc (line_index_of_source text) text 0 (String.length text) {
        Option.none => Result.err "formatting: the document's range could not be placed",
        Option.some r => Result.ok (Json.make_array [lsp_text_edit r out]),
    }

#[partial]
def lsp_text_edit (r : WireRange) (new_text : String) : Json :=
    rpc_object [
        Pair.pair "range" (wire_range_json r),
        Pair.pair "newText" (Json.make_str new_text),
    ]
