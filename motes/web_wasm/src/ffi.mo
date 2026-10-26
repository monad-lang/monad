/// Raw web externs. Every one is side-effecting and typed `RawIO A`; the
/// user-facing wrappers in `dom.mo`, `fetch.mo`, `clock.mo`, `storage.mo`
/// and `console.mo` turn them into `IO`.
///
/// The `web_*` link names are deliberately NOT `monad_*`: the compiler
/// rejects an extern that binds a Monad runtime symbol
/// (`validate_no_monad_externs`), and these are foreign JS imports, not
/// runtime functions. `runtime/src/platform_web.c` (and the generated
/// `wasm/web/web_runtime.js`) provide the matching `web_*` wrappers; until
/// that runtime side lands, a consumer fails at link rather than at codegen.
///
/// This is the only file in the corpus that declares a web extern.
///
/// Marshalling note: strings cross as C strings here. The `mote/sqlx`
/// rebase supplies `std::cstring`/`Ptr` for length-carrying calls; switch
/// the multi-byte-string externs to `(ptr, len)` when that lands.

use lib::types {Node, RequestId, ClipboardOp}
use std::ref {Ref}

#[extern "c" {link_name := "web_dom_create"}]
def dom_create_raw (tag : String) : RawIO Node

#[extern "c" {link_name := "web_dom_create_text"}]
def dom_create_text_raw (text : String) : RawIO Node

#[extern "c" {link_name := "web_dom_create_comment"}]
def dom_create_comment_raw (text : String) : RawIO Node

#[extern "c" {link_name := "web_dom_root"}]
def dom_root_raw : RawIO Node

#[extern "c" {link_name := "web_dom_append"}]
def dom_append_raw (parent : Node) (child : Node) : RawIO Unit

#[extern "c" {link_name := "web_dom_insert_before"}]
def dom_insert_before_raw (parent : Node) (child : Node) (before : Node) : RawIO Unit

#[extern "c" {link_name := "web_dom_remove"}]
def dom_remove_raw (node : Node) : RawIO Unit

#[extern "c" {link_name := "web_dom_replace"}]
def dom_replace_raw (old : Node) (new_ : Node) : RawIO Unit

#[extern "c" {link_name := "web_dom_set_attr"}]
def dom_set_attr_raw (n : Node) (key : String) (value : String) : RawIO Unit

#[extern "c" {link_name := "web_dom_remove_attr"}]
def dom_remove_attr_raw (n : Node) (key : String) : RawIO Unit

#[extern "c" {link_name := "web_dom_set_text"}]
def dom_set_text_raw (n : Node) (text : String) : RawIO Unit

#[extern "c" {link_name := "web_dom_add_listener"}]
def dom_add_listener_raw (n : Node) (event : String) (spec : String) : RawIO Unit

#[extern "c" {link_name := "web_dom_add_listener_global"}]
def dom_add_listener_global_raw (target : I64) (event : String) (spec : String) : RawIO Unit

#[extern "c" {link_name := "web_dom_remove_listener_global"}]
def dom_remove_listener_global_raw (target : I64) (event : String) : RawIO Unit

#[extern "c" {link_name := "web_dom_child"}]
def dom_child_raw (n : Node) (index : I64) : RawIO Node

#[extern "c" {link_name := "web_dom_child_count"}]
def dom_child_count_raw (n : Node) : RawIO I64

/// Read-only introspection (hydration's match predicate, and the
/// value/selector pair an SPA needs to read a text input).
/// `dom_tag_name_raw` is lowercase -- the host folds the case.
#[extern "c" {link_name := "web_dom_node_type"}]
def dom_node_type_raw (n : Node) : RawIO I64

#[extern "c" {link_name := "web_dom_tag_name"}]
def dom_tag_name_raw (n : Node) : RawIO String

#[extern "c" {link_name := "web_dom_value"}]
def dom_value_raw (n : Node) : RawIO String

#[extern "c" {link_name := "web_dom_query"}]
def dom_query_raw (selector : String) : RawIO Node

#[extern "c" {link_name := "web_fetch_begin"}]
def fetch_begin_raw (url : String) (method : I64) (body : String) : RawIO RequestId

#[extern "c" {link_name := "web_fetch_poll"}]
def fetch_poll_raw (r : RequestId) : RawIO I64

#[extern "c" {link_name := "web_fetch_status"}]
def fetch_status_raw (r : RequestId) : RawIO I64

#[extern "c" {link_name := "web_fetch_read"}]
def fetch_read_raw (r : RequestId) (max : I64) : RawIO String

#[extern "c" {link_name := "web_clipboard_available"}]
def clipboard_available_raw : RawIO I64

#[extern "c" {link_name := "web_clipboard_read_begin"}]
def clipboard_read_begin_raw : RawIO ClipboardOp

#[extern "c" {link_name := "web_clipboard_write_begin"}]
def clipboard_write_begin_raw (text : String) : RawIO ClipboardOp

#[extern "c" {link_name := "web_clipboard_poll"}]
def clipboard_poll_raw (op : ClipboardOp) : RawIO I64

#[extern "c" {link_name := "web_clipboard_read"}]
def clipboard_read_raw (op : ClipboardOp) : RawIO String

#[extern "c" {link_name := "web_clipboard_error"}]
def clipboard_error_raw (op : ClipboardOp) : RawIO String

#[extern "c" {link_name := "web_now_ms"}]
def now_ms_raw : RawIO I64

#[extern "c" {link_name := "web_storage_get_raw"}]
def storage_get_raw (key : String) : RawIO String

#[extern "c" {link_name := "web_storage_set"}]
def storage_set_raw (key : String) (value : String) : RawIO Unit

#[extern "c" {link_name := "web_console_log"}]
def console_log_raw (s : String) : RawIO Unit

/// The export-call state slot. Exports cannot take or return Monad values
/// (the export ABI is i64 words), so a `Ref` is stashed in the JS host and
/// read back by the next export. `Ref A` is one opaque word at runtime and
/// the JS side never dereferences it.
#[extern "c" {link_name := "web_keep_set"}]
def keep_set_raw {A : Type} (r : Ref A) : RawIO Unit

#[extern "c" {link_name := "web_keep_get"}]
def keep_get_raw {A : Type} : RawIO (Ref A)

// ── The current event ────────────────────────────────────────────────
//
// The JS host keeps the live `WebEvent` in a slot for the duration of the
// synchronous `oak_dispatch_event` export call. These getters read it.
// Strings are written into the C side's scratch buffer and copied out, like
// `dom_tag_name`; numeric selectors live in `event.mo` next to their use.

#[extern "c" {link_name := "web_event_i64"}]
def event_i64_raw (which : I64) : RawIO I64

#[extern "c" {link_name := "web_event_f64"}]
def event_f64_raw (which : I64) : RawIO F64

#[extern "c" {link_name := "web_event_str"}]
def event_str_raw (which : I64) : RawIO String

#[extern "c" {link_name := "web_event_data"}]
def event_data_raw (mime : String) : RawIO String

#[extern "c" {link_name := "web_event_types"}]
def event_types_raw : RawIO String

#[extern "c" {link_name := "web_event_files_count"}]
def event_files_count_raw : RawIO I64

#[extern "c" {link_name := "web_event_file_i64"}]
def event_file_i64_raw (index : I64) (which : I64) : RawIO I64

#[extern "c" {link_name := "web_event_file_str"}]
def event_file_str_raw (index : I64) (which : I64) : RawIO String

#[extern "c" {link_name := "web_event_prevent_default"}]
def event_prevent_default_raw : RawIO Unit

#[extern "c" {link_name := "web_event_stop_propagation"}]
def event_stop_propagation_raw : RawIO Unit
