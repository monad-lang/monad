/// `textDocument/publishDiagnostics`: what the checker found, as the notification an
/// editor renders as markers.
///
/// THE RANGE IS ALREADY ON THE DIAGNOSTIC, and where it came from is worth knowing
/// before reading anything here. It is DECLARATION granularity: the checker pairs each
/// error with the span of the declaration it was raised in, not with the expression
/// that failed (`lang/src/module.mo`'s ranged check path, and Phase 0's probe verdict
/// that no located term survives into a `TypeError` payload). That is what the Rust
/// server this replaces shipped, so it is not a regression -- but it is the reason a
/// squiggle covers a whole `def` rather than the operator inside it, and it is the
/// thing the follow-up (a location-carrying `TypeError`) would change.
///
/// SEVERITY IS UNIFORMLY "error" TODAY, and that is a statement about the checker, not
/// a decision taken here: every diagnostic it produces is a hard failure, because
/// `check` fails a file for any of them. `toolkit::diagnostic` carries all four
/// severities and picks error, so the day the checker grows a warning the only change
/// is which one it picks -- the wire already has the field.
///
/// THE VERSION IS THE CLIENT'S, and it is sent when the client has one. See
/// `lsp_publish_notification`.
use json::json {Json}
use lang::module {Diagnostic, ranged_file_diagnostics}
use lsp::checks {Check, check_result, check_text}
use toolkit::diagnostic {WireDiagnostic, wire_diagnostic_of_lang, wire_diagnostics_json}
use toolkit::jsonrpc {rpc_encode_notification, rpc_object}
use toolkit::position {LineIndex, PositionEncoding, line_index_of_source}

// --- A check's diagnostics, on the wire ---

/// Every diagnostic a check produced, converted for the wire.
///
/// THE TEXT AND THE LINE INDEX COME FROM THE SAME REVISION, which is the only invariant
/// this module has to keep: the source is the text stored beside the check, and the
/// index is built from that text, so a range the checker computed against it cannot be
/// converted against a buffer that has moved on. That is also why this takes the check
/// and not the document store -- the text is right here.
#[partial]
pub def lsp_wire_diagnostics (enc : PositionEncoding) (ch : Check) : List WireDiagnostic :=
    let src : String := check_text ch in
    lsp_wire_diagnostics_of enc src (line_index_of_source src)
        (ranged_file_diagnostics (check_result ch))

#[partial]
def lsp_wire_diagnostics_of (enc : PositionEncoding) (src : String) (ix : LineIndex)
    (ds : List Diagnostic) : List WireDiagnostic :=
    match ds {
        List.empty => List.empty,
        List.cons d rest =>
            List.cons (wire_diagnostic_of_lang enc ix src d)
                (lsp_wire_diagnostics_of enc src ix rest),
    }

/// A check's diagnostics as the `diagnostics` array alone.
///
/// The empty case needs no branch: `wire_diagnostics_json` folds over an empty list into
/// an empty array, which is exactly what a client needs to clear a document's markers
/// after a fix. A clean file publishing nothing at all would leave the last set of
/// squiggles on screen.
#[partial]
pub def lsp_diagnostics_json (enc : PositionEncoding) (ch : Check) : Json :=
    wire_diagnostics_json (lsp_wire_diagnostics enc ch)

// --- The notification ---

/// `textDocument/publishDiagnostics`, encoded and ready to frame.
///
/// THE VERSION IS SENT WHEN THE CLIENT HAS ONE, and omitted when it does not. The
/// specification makes the field optional and gives it a real job: a client editing
/// ahead of the server drops diagnostics that arrive for a revision it has already
/// left. So the value is the CLIENT's label for its own text -- it comes from the
/// document store, not from anything the checker knows -- and a server that invented
/// one would be inventing a claim about which revision the user is looking at.
#[partial]
pub def lsp_publish_notification (uri : String) (version : Option I64)
    (enc : PositionEncoding) (ch : Check) : String :=
    rpc_encode_notification "textDocument/publishDiagnostics"
        (lsp_publish_params uri version enc ch)

#[partial]
pub def lsp_publish_params (uri : String) (version : Option I64) (enc : PositionEncoding)
    (ch : Check) : Json :=
    rpc_object (List.cons (Pair.pair "uri" (Json.make_str uri))
        (List.cons (Pair.pair "diagnostics" (lsp_diagnostics_json enc ch))
            (lsp_publish_version version)))

/// The optional `version` field, as a zero- or one-element field list.
///
/// A field list rather than a `Json.make_null` in the slot, for the reason
/// `motes/lsp`'s hover gives for its `range`: the specification makes the field
/// optional, and an absent member is unambiguous while a member that is present and
/// null asks the client to decide what null means. Omitting is the reading that cannot
/// be got wrong.
#[partial]
def lsp_publish_version (version : Option I64) : List (Pair String Json) :=
    match version {
        Option.none => lsp_no_fields,
        Option.some v => List.cons (Pair.pair "version" (Json.make_num_int v)) lsp_no_fields,
    }

/// An empty field list, named for the reason `toolkit::diagnostic` names its own: an
/// unannotated `List.empty` in argument position is the shape that resolved to the
/// wrong instance in this repository's `Map.empty` bug, and pinning it costs a line.
def lsp_no_fields : List (Pair String Json) := List.empty

/// An empty `Json` list, pinned by a def for the same reason.
def lsp_no_diagnostics : List Json := List.empty

/// The empty publish, which is how a client is told to clear a document's markers.
///
/// `didClose` is the caller, and it is the one publish with no check behind it: the
/// specification's guidance is that a server publishes an empty array for a document it
/// will not report on again, because otherwise the client keeps the last set it was
/// sent. A document that is merely clean reaches the same wire shape through a check
/// that found nothing, so this is not a second code path -- it is the same shape from
/// the one caller that has no check to convert.
#[partial]
pub def lsp_clear_notification (uri : String) : String :=
    rpc_encode_notification "textDocument/publishDiagnostics"
        (rpc_object [
            Pair.pair "uri" (Json.make_str uri),
            Pair.pair "diagnostics" (Json.make_array lsp_no_diagnostics),
        ])
