/// Reading a method's params.
///
/// EVERY READER ANSWERS AN `Option`, INCLUDING FOR A FIELD OF THE WRONG TYPE, and
/// that is a decision about hostile input rather than about tidiness. A client is
/// free to send `"version": "3"` where the specification says a number, or
/// `textDocument` as a string, and a server that took the checker's word for it
/// would fail somewhere far from the field that was wrong. So "absent" and
/// "present but not what the method needs" collapse into one answer here, and the
/// handler turns either into an `Invalid params` error naming the method -- which
/// is a thing a client author can act on, unlike a crash or a `null` result.
///
/// The readers take the params NODE, not `Option Json`. `rpc_params` answers
/// `Option.none` for a request that omitted params entirely, and the handler is
/// the right place to decide what that means for its own method -- usually "no
/// textDocument, so invalid params". Flattening it here would put that decision in
/// a helper that cannot know the method, and the flattening is one line at the
/// call site.
///
/// The nesting is spelled out per call -- `lsp_param_nested "textDocument" "uri"`
/// -- rather than as a path string split on dots. The set of paths is small, the
/// specification fixes each one, and a path string is a place a typo is a silently
/// absent field instead of a call that does not compile.
use json::json {Json}
use toolkit::jsonrpc {rpc_field}

/// A string field, absent if the field is absent or is not a string.
#[partial]
pub def lsp_param_str (key : String) (params : Json) : Option String :=
    match rpc_field key params {
        Option.none => Option.none,
        Option.some node => lsp_node_str node,
    }

/// An integer field.
///
/// `Json.get_num_i64` is handed the result of `Json.get_num`, which is how the two
/// conversions compose: a number that is not an integer -- a version sent as
/// `1.5` -- answers `Result.err` at the second step rather than truncating. That
/// matters for exactly one field, a document's version, where a truncated number
/// would be a version the client never sent.
#[partial]
pub def lsp_param_i64 (key : String) (params : Json) : Option I64 :=
    match rpc_field key params {
        Option.none => Option.none,
        Option.some node => lsp_node_i64 node,
    }

/// A field one level down, as in `textDocument.uri`.
///
/// Both levels are required to be objects for the answer to be present: a
/// `textDocument` sent as a string is not a struct missing a `uri` field, it is a
/// malformed request, and both are absent here.
#[partial]
pub def lsp_param_nested (outer : String) (inner : String) (params : Json) : Option Json :=
    match rpc_field outer params {
        Option.none => Option.none,
        Option.some node => rpc_field inner node,
    }

/// The same, read as a string, and as an integer.
///
/// These exist because almost every method in this protocol has exactly one shape
/// -- an object field naming the document, with the interesting values inside it --
/// so `lsp_param_nested_str "textDocument" "uri"` is what a handler wants at nearly
/// every call site. Composing it at the call site instead would put a `match` on an
/// `Option` in front of each one, which is the kind of repetition that hides the
/// one case where the absence means something.
#[partial]
pub def lsp_param_nested_str (outer : String) (inner : String) (params : Json) : Option String :=
    match lsp_param_nested outer inner params {
        Option.none => Option.none,
        Option.some node => lsp_node_str node,
    }

#[partial]
pub def lsp_param_nested_i64 (outer : String) (inner : String) (params : Json) : Option I64 :=
    match lsp_param_nested outer inner params {
        Option.none => Option.none,
        Option.some node => lsp_node_i64 node,
    }

/// A string, from a node already in hand.
#[partial]
def lsp_node_str (node : Json) : Option String :=
    match Json.get_str node {
        Result.err _e => Option.none,
        Result.ok s => Option.some s,
    }

/// An integer, from a node already in hand.
#[partial]
def lsp_node_i64 (node : Json) : Option I64 :=
    match Json.get_num_i64 (Json.get_num node) {
        Result.err _e => Option.none,
        Result.ok n => Option.some n,
    }

/// Element `i` of an array-valued node, 0-based.
///
/// This is `contentChanges[0]` and nothing else, and it is the only place in the
/// protocol this server reads an array element. Full-text sync means there is
/// exactly one change per `didChange`, so an index is not a position in a list a
/// client chose -- it is the specification's shape for the single change.
#[partial]
pub def lsp_param_index (i : I64) (j : Option Json) : Option Json :=
    match j {
        Option.none => Option.none,
        Option.some node =>
            match Json.get_array node {
                Result.err _e => Option.none,
                Result.ok xs => lsp_param_list_at xs i,
            },
    }

#[partial]
def lsp_param_list_at (xs : List Json) (i : I64) : Option Json :=
    match xs {
        List.empty => Option.none,
        List.cons x rest =>
            if I64.beq i 0 then Option.some x else lsp_param_list_at rest (I64.sub i 1),
    }

/// A field that is an array of strings, keeping the strings and dropping anything
/// else rather than failing the whole read.
///
/// This exists for one field: `capabilities.general.positionEncodings`. A client
/// that put a number in that list is offering nothing this server can use, and
/// dropping it loses a choice rather than a document.
#[partial]
pub def lsp_param_str_list (key : String) (params : Json) : List String :=
    lsp_str_list_go (lsp_json_list (rpc_field key params)) lsp_no_strings

/// The empty string list as a named def, so no caller writes a bare `List.empty`
/// whose element type has to be inferred -- the `Map.empty` trap one type over.
def lsp_no_strings : List String := List.empty

#[partial]
def lsp_str_list_go (xs : List Json) (acc : List String) : List String :=
    match xs {
        List.empty => lsp_str_list_rev acc lsp_no_strings,
        List.cons x rest =>
            match Json.get_str x {
                Result.err _e => lsp_str_list_go rest acc,
                Result.ok s => lsp_str_list_go rest (List.cons s acc),
            },
    }

/// Reversed locally rather than through a shared reverse, the same call
/// `jsonrpc.mo` and `position.mo` make: four lines of list reversal is not worth
/// widening a module's stated dependency surface for.
#[partial]
def lsp_str_list_rev (ls : List String) (acc : List String) : List String :=
    match ls {
        List.empty => acc,
        List.cons l rest => lsp_str_list_rev rest (List.cons l acc),
    }

/// The nodes of an array-valued field, or none.
#[partial]
def lsp_json_list (j : Option Json) : List Json :=
    match j {
        Option.none => lsp_no_json_nodes,
        Option.some node =>
            match Json.get_array node {
                Result.err _e => lsp_no_json_nodes,
                Result.ok xs => xs,
            },
    }

def lsp_no_json_nodes : List Json := List.empty
