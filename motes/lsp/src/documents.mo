/// The document notifications: `didOpen`, `didChange`, `didClose` and `didSave`.
///
/// A NOTIFICATION HAS NO REPLY, so a malformed one cannot be reported to the
/// client at all -- which is why every entry point here answers an `Option` and
/// the server logs the absence and carries on. The one thing that must not happen
/// is a crash: a client sends a notification for every keystroke a user makes, so a
/// server that dies on a malformed one dies within seconds of the user typing
/// something surprising.
///
/// THE CHANGED FLAG IS THE DEBOUNCE, and it is worth being explicit about why the
/// debounce is a flag rather than a timer. Re-checking a file is the expensive thing
/// this server does, and a client sends `didChange` for edits that do not change
/// anything a checker sees -- a keystroke that is undone, a cursor movement a client
/// chose to report, an edit that arrives twice. Comparing the incoming text against
/// the buffer already held costs one pass and CANNOT BE WRONG, whereas the two
/// alternatives can: a hash can collide and silently skip a recheck, leaving a
/// diagnostic the user cannot clear, and a fiber timer under the Rust host blocks
/// the very thread that has to keep reading messages
/// (`std/src/concurrent/combine_test.mo:3-8` records that the host serializes
/// fibers by design, and `sleep_io` is a blocking sleep). So the cheapest correct
/// debounce is the one that asks the buffer whether anything actually changed.
///
/// THE VERSION IS NEVER INVENTED. `publishDiagnostics` may carry the version the
/// diagnostics were computed against, and a client that receives a version newer
/// than its buffer discards the whole set -- correct behaviour, and the mechanism by
/// which a server that reports the wrong version silently stops showing diagnostics
/// for a file that is being edited. So a version is recorded only when the client
/// stated one, and an absent one keeps whatever the document already had
/// (`document_version` has the argument and names the one value that is a
/// fallback).
use json::json {Json}
use lsp::params {lsp_param_index, lsp_param_nested_i64, lsp_param_nested_str, lsp_param_str}
use toolkit::docstore {
    DocStore, docstore_change, docstore_close, docstore_open, docstore_text, docstore_version,
}
use toolkit::jsonrpc {rpc_field}

/// A document notification that was understood: which document it was about, the
/// store it left behind, and whether the client's view of it moved.
///
/// The three travel together because the caller needs all three at once and none of
/// them separately: the URI is what a diagnostic is published against, the store is
/// what the next call operates on, and the flag is the decision about whether to do
/// anything at all. Returning them apart would let a caller pair a URI from one
/// message with a store from another.
///
/// `changed` is true for anything the client's view moved under -- a text that
/// differs from the buffer already held, and a close, where the view moved to
/// "nothing". It is FALSE only for a notification that restates exactly what the
/// store already has, which is the case the check is skipped for.
pub struct DocumentEdit { uri : String, store : DocStore, changed : Bool }

pub def document_edit_uri (e : DocumentEdit) : String := e.uri

pub def document_edit_store (e : DocumentEdit) : DocStore := e.store

pub def document_edit_changed (e : DocumentEdit) : Bool := e.changed

/// The document a message is about: `params.textDocument.uri`.
///
/// Used by the notifications that change nothing -- `didSave`, and every request
/// in `navigation.mo` -- so it is the one reader in this module that is not tied to
/// a store.
#[partial]
pub def document_uri (params : Json) : Option String :=
    lsp_param_nested_str "textDocument" "uri" params

/// `didOpen`: the client is showing a document and sends its whole text.
///
/// The text is taken from the message rather than read from disk, because the two
/// differ the moment the user types -- a server that read the file would diagnose
/// the last SAVED revision while the user looks at an unsaved one.
///
/// A second `didOpen` for a URI already open replaces it, which is
/// `toolkit::docstore`'s behaviour and the right one here: the client is telling us
/// what it has, and what it has is the later statement.
#[partial]
pub def document_open (params : Json) (store : DocStore) : Option DocumentEdit :=
    match document_uri params {
        Option.none => Option.none,
        Option.some uri =>
            match lsp_param_nested_str "textDocument" "text" params {
                Option.none => Option.none,
                Option.some text =>
                    let changed : Bool := document_text_changed uri store text in
                    let version : I64 := document_version params uri store in
                    Option.some (DocumentEdit.mk uri (docstore_open uri version text store) changed),
            },
    }

/// `didChange`: full-text sync, so the single element of `contentChanges` is the
/// whole buffer.
///
/// THE TWO ENTRY POINTS STAY APART even though `open` and `change` have the same
/// body today, which is the property `toolkit::docstore`'s own doc asks for: when
/// incremental sync lands, the change path is the one that stops taking the whole
/// buffer, and a server that had funnelled both through `docstore_open` would have
/// to find every call site at that point instead of changing one line here.
///
/// The version may be absent, and then the one already recorded stands --
/// `document_version` has the argument.
#[partial]
pub def document_change (params : Json) (store : DocStore) : Option DocumentEdit :=
    match document_uri params {
        Option.none => Option.none,
        Option.some uri =>
            match lsp_param_str "text" (document_content_change params) {
                Option.none => Option.none,
                Option.some text =>
                    let changed : Bool := document_text_changed uri store text in
                    let version : I64 := document_version params uri store in
                    Option.some (DocumentEdit.mk uri (docstore_change uri version text store) changed),
            },
    }

/// `didClose`: the document is gone from the client's view.
///
/// The store forgets it, which matters beyond tidiness: a URI still in the store
/// would be re-checked by a `didSave` for a buffer the user closed, and reported
/// against in the diagnostics of a document the client no longer has. The caller
/// publishes the empty diagnostic set for it in the same breath -- without that,
/// the last set a client received stays in its gutter for a file that was closed.
///
/// `changed` is true, and the caller does NOT re-check: it reads the store, finds
/// no text for this URI, and publishes the empty set. That is the same rule the
/// other two use -- publish what the store says -- so a close needs no separate
/// path through the server, only the observation that a document absent from the
/// store has nothing to say.
#[partial]
pub def document_close (params : Json) (store : DocStore) : Option DocumentEdit :=
    match document_uri params {
        Option.none => Option.none,
        Option.some uri => Option.some (DocumentEdit.mk uri (docstore_close uri store) true),
    }

/// The first element of `contentChanges`, whose node the caller reads `text` from.
///
/// IN FULL-TEXT SYNC THERE IS EXACTLY ONE CHANGE, so first and last are the same
/// element and the question does not arise -- which is the case this server is in,
/// because that is the mode it advertises. A client that sends several is speaking
/// incremental sync, which was not advertised, and in that mode NO single element is
/// the buffer: each one's `text` is a replacement for a range. So the pick is
/// arbitrary in exactly the case where the input is already wrong, and taking the
/// first is the arbitrary pick with the least machinery behind it.
#[partial]
def document_content_change (params : Json) : Json :=
    match lsp_param_index 0 (rpc_field "contentChanges" params) {
        Option.none => Json.make_null,
        Option.some change => change,
    }

/// The version the client stated for this change, or the one already recorded.
///
/// An absent version is the case this exists for: the specification's
/// `VersionedTextDocumentIdentifier` allows a null version, and a server that
/// invented one would publish diagnostics under a number the client never sent --
/// which the client discards, which is how a server silently stops showing
/// diagnostics for a file the user is editing.
///
/// For a document this server has never seen -- a `didChange` for a URI that was
/// never opened, which happens when a client's `didOpen` was lost -- there is
/// nothing to keep, and the recorded version becomes 0. Clients number documents
/// from 1, so 0 cannot be confused with a stated version. It is a fallback and not a
/// sentinel in the store: `toolkit::docstore`'s tests pin that version 0 stored
/// explicitly is a version like any other.
#[partial]
def document_version (params : Json) (uri : String) (store : DocStore) : I64 :=
    match lsp_param_nested_i64 "textDocument" "version" params {
        Option.some v => v,
        Option.none => document_recorded_version uri store,
    }

#[partial]
def document_recorded_version (uri : String) (store : DocStore) : I64 :=
    match docstore_version uri store {
        Option.none => 0,
        Option.some v => v,
    }

/// Whether the incoming text differs from the text already held.
///
/// A document with no recorded text counts as changed -- there is nothing to
/// compare against, and a `didOpen` is the client declaring state this server has
/// no earlier knowledge of.
#[partial]
def document_text_changed (uri : String) (store : DocStore) (text : String) : Bool :=
    match docstore_text uri store {
        Option.none => true,
        Option.some old => Bool.not (String.beq old text),
    }
