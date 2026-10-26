/// The web boundary as data.
///
/// This is the single source of truth for the imports the JS runtime must
/// provide and the exports it may call. `glue.mo` renders the import map
/// from this list; `runtime/src/platform_web.c` declares the matching
/// `web_*` wrappers; `ffi.mo` declares the Monad side.
///
/// The parameter/result strings are the JS IMPORT SIGNATURES (the values
/// `Glue.loader` renders are forwarded verbatim, so they document what
/// `web_runtime.js` sees): `"i64"` for one wasm word, `"void"` for no
/// result. A Monad `String` crosses as TWO words -- a pointer and a byte
/// length -- and a Node/RequestId as one opaque id word. The C ABI is the
/// authority; the runtime's own declarations cannot be reflected on from
/// Monad, so this list plus the goldens and `runtime/src/platform_web.c`'s
/// matching `web_*` wrappers are the drift guard.

pub struct WebImport {
  module : String,
  name : String,
  params : List String,
  result : String
}

pub struct WebExport {
  name : String
}

pub struct WebAbi {
  imports : List WebImport,
  exports : List WebExport
}

def WebImport.dom_create : WebImport :=
  { module := "monad", name := "dom_create", params := ["i64", "i64"], result := "i64" }

def WebImport.dom_create_text : WebImport :=
  { module := "monad", name := "dom_create_text", params := ["i64", "i64"], result := "i64" }

def WebImport.dom_create_comment : WebImport :=
  { module := "monad", name := "dom_create_comment", params := ["i64", "i64"], result := "i64" }

def WebImport.dom_root : WebImport :=
  { module := "monad", name := "dom_root", params := List.empty, result := "i64" }

def WebImport.dom_append : WebImport :=
  { module := "monad", name := "dom_append", params := ["i64", "i64"], result := "void" }

def WebImport.dom_insert_before : WebImport :=
  { module := "monad", name := "dom_insert_before", params := ["i64", "i64", "i64"], result := "void" }

def WebImport.dom_remove : WebImport :=
  { module := "monad", name := "dom_remove", params := ["i64"], result := "void" }

def WebImport.dom_replace : WebImport :=
  { module := "monad", name := "dom_replace", params := ["i64", "i64"], result := "void" }

def WebImport.dom_set_attr : WebImport :=
  { module := "monad", name := "dom_set_attr", params := ["i64", "i64", "i64", "i64", "i64"], result := "void" }

def WebImport.dom_remove_attr : WebImport :=
  { module := "monad", name := "dom_remove_attr", params := ["i64", "i64", "i64"], result := "void" }

def WebImport.dom_set_text : WebImport :=
  { module := "monad", name := "dom_set_text", params := ["i64", "i64", "i64"], result := "void" }

def WebImport.dom_add_listener : WebImport :=
  { module := "monad", name := "dom_add_listener", params := ["i64", "i64", "i64", "i64", "i64"], result := "void" }

def WebImport.dom_add_listener_global : WebImport :=
  { module := "monad", name := "dom_add_listener_global", params := ["i64", "i64", "i64", "i64", "i64"], result := "void" }

def WebImport.dom_remove_listener_global : WebImport :=
  { module := "monad", name := "dom_remove_listener_global", params := ["i64", "i64", "i64"], result := "void" }

def WebImport.dom_child : WebImport :=
  { module := "monad", name := "dom_child", params := ["i64", "i64"], result := "i64" }

def WebImport.dom_child_count : WebImport :=
  { module := "monad", name := "dom_child_count", params := ["i64"], result := "i64" }

/// Read-only DOM introspection. `nodeType` is a plain word; `tag_name` and
/// `value` are written into a caller-supplied buffer (the C wrapper owns
/// the scratch buffer) and return the byte count, exactly like
/// `storage_get_raw`. `tag_name` is LOWERCASE: the host folds the case, so
/// no Monad-side allocation is spent per node.
def WebImport.dom_node_type : WebImport :=
  { module := "monad", name := "dom_node_type", params := ["i64"], result := "i64" }

def WebImport.dom_tag_name : WebImport :=
  { module := "monad", name := "dom_tag_name", params := ["i64", "i64", "i64"], result := "i64" }

def WebImport.dom_value : WebImport :=
  { module := "monad", name := "dom_value", params := ["i64", "i64", "i64"], result := "i64" }

/// A selector lookup: an SPA event handler only gets a numeric message id,
/// so this is how it finds a node to read (`Dom.value`). The null handle
/// (`0`) means "no match".
def WebImport.dom_query : WebImport :=
  { module := "monad", name := "dom_query", params := ["i64", "i64"], result := "i64" }

def WebImport.fetch_begin : WebImport :=
  { module := "monad", name := "fetch_begin", params := ["i64", "i64", "i64", "i64", "i64"], result := "i64" }

def WebImport.fetch_poll : WebImport :=
  { module := "monad", name := "fetch_poll", params := ["i64"], result := "i64" }

def WebImport.fetch_status : WebImport :=
  { module := "monad", name := "fetch_status", params := ["i64"], result := "i64" }

def WebImport.fetch_read : WebImport :=
  { module := "monad", name := "fetch_read", params := ["i64", "i64", "i64"], result := "i64" }

def WebImport.clipboard_available : WebImport :=
  { module := "monad", name := "clipboard_available", params := List.empty, result := "i64" }

def WebImport.clipboard_read_begin : WebImport :=
  { module := "monad", name := "clipboard_read_begin", params := List.empty, result := "i64" }

def WebImport.clipboard_write_begin : WebImport :=
  { module := "monad", name := "clipboard_write_begin", params := ["i64", "i64"], result := "i64" }

def WebImport.clipboard_poll : WebImport :=
  { module := "monad", name := "clipboard_poll", params := ["i64"], result := "i64" }

def WebImport.clipboard_read : WebImport :=
  { module := "monad", name := "clipboard_read", params := ["i64", "i64", "i64"], result := "i64" }

def WebImport.clipboard_error : WebImport :=
  { module := "monad", name := "clipboard_error", params := ["i64", "i64", "i64"], result := "i64" }

def WebImport.now_ms : WebImport :=
  { module := "monad", name := "now_ms", params := List.empty, result := "i64" }

def WebImport.storage_get_raw : WebImport :=
  { module := "monad", name := "storage_get_raw", params := ["i64", "i64", "i64", "i64"], result := "i64" }

def WebImport.storage_set : WebImport :=
  { module := "monad", name := "storage_set", params := ["i64", "i64", "i64", "i64"], result := "void" }

def WebImport.console_log : WebImport :=
  { module := "monad", name := "console_log", params := ["i64", "i64"], result := "void" }

/// The /try engine's one export channel: `status` plus the four rendered
/// strings, each as (ptr,len). Push rather than pull because an `IO`-typed
/// wasm export cannot return a value and a pure one cannot read engine
/// state; the JS host copies the strings immediately.
def WebImport.try_result : WebImport :=
  { module := "monad", name := "try_result",
    params := ["i64", "i64", "i64", "i64", "i64", "i64", "i64", "i64", "i64"],
    result := "void" }

/// The UI side of the worker channel (`motes/web_wasm/src/worker.mo`):
/// start a run, poll its state, read the finished result's fields, cancel.
def WebImport.worker_run : WebImport :=
  { module := "monad", name := "worker_run", params := ["i64", "i64"], result := "i64" }

def WebImport.worker_poll : WebImport :=
  { module := "monad", name := "worker_poll", params := List.empty, result := "i64" }

def WebImport.worker_status : WebImport :=
  { module := "monad", name := "worker_status", params := ["i64", "i64"], result := "i64" }

def WebImport.worker_value : WebImport :=
  { module := "monad", name := "worker_value", params := ["i64", "i64"], result := "i64" }

def WebImport.worker_type : WebImport :=
  { module := "monad", name := "worker_type", params := ["i64", "i64"], result := "i64" }

def WebImport.worker_error : WebImport :=
  { module := "monad", name := "worker_error", params := ["i64", "i64"], result := "i64" }

def WebImport.worker_notes : WebImport :=
  { module := "monad", name := "worker_notes", params := ["i64", "i64"], result := "i64" }

def WebImport.worker_cancel : WebImport :=
  { module := "monad", name := "worker_cancel", params := List.empty, result := "void" }

/// The export-call state slot: one opaque word in, one out.
def WebImport.keep_set : WebImport :=
  { module := "monad", name := "keep_set", params := ["i64"], result := "void" }

def WebImport.keep_get : WebImport :=
  { module := "monad", name := "keep_get", params := List.empty, result := "i64" }

/// The runtime's own console I/O. `platform_web.c` declares these next to
/// the `web_*` wrappers (module "monad"), so every program that can print
/// needs them in the import object even if it never calls a `web_*` one.
def WebImport.write_stdout : WebImport :=
  { module := "monad", name := "write_stdout", params := ["i64", "i64"], result := "i64" }

def WebImport.write_stderr : WebImport :=
  { module := "monad", name := "write_stderr", params := ["i64", "i64"], result := "i64" }

def WebImport.read_stdin : WebImport :=
  { module := "monad", name := "read_stdin", params := ["i64", "i64"], result := "i64" }

/// `F64.to_string` on the freestanding web profile: the host owns the
/// float -> decimal formatting the profile's missing libc would do. The
/// runtime passes the double's bit pattern, a caller-supplied UTF-8 buffer
/// and its capacity; the host returns the byte count. A program whose
/// reachable code never formats a float does not import it (wasm-ld drops
/// the unreachable runtime function), and every loader may provide it
/// harmlessly.
def WebImport.f64_to_string : WebImport :=
  { module := "monad", name := "f64_to_string", params := ["i64", "i64", "i64"], result := "i64" }

/// The current-event getters. `event_str`/`event_data`/`event_types`/
/// `event_file_str` write UTF-8 into the C scratch buffer and return the byte
/// count; `event_f64` returns an `f64` (the C wrapper bitcasts, and the JS
/// import sees a plain number).
def WebImport.event_i64 : WebImport :=
  { module := "monad", name := "event_i64", params := ["i64"], result := "i64" }

def WebImport.event_f64 : WebImport :=
  { module := "monad", name := "event_f64", params := ["i64"], result := "f64" }

def WebImport.event_str : WebImport :=
  { module := "monad", name := "event_str", params := ["i64", "i64", "i64"], result := "i64" }

def WebImport.event_data : WebImport :=
  { module := "monad", name := "event_data", params := ["i64", "i64", "i64", "i64"], result := "i64" }

def WebImport.event_types : WebImport :=
  { module := "monad", name := "event_types", params := ["i64", "i64"], result := "i64" }

def WebImport.event_files_count : WebImport :=
  { module := "monad", name := "event_files_count", params := List.empty, result := "i64" }

def WebImport.event_file_i64 : WebImport :=
  { module := "monad", name := "event_file_i64", params := ["i64", "i64"], result := "i64" }

def WebImport.event_file_str : WebImport :=
  { module := "monad", name := "event_file_str", params := ["i64", "i64", "i64", "i64"], result := "i64" }

def WebImport.event_prevent_default : WebImport :=
  { module := "monad", name := "event_prevent_default", params := List.empty, result := "void" }

def WebImport.event_stop_propagation : WebImport :=
  { module := "monad", name := "event_stop_propagation", params := List.empty, result := "void" }

def WebExport.oak_mount : WebExport := { name := "oak_mount" }
def WebExport.oak_dispatch_event : WebExport := { name := "oak_dispatch_event" }
def WebExport.oak_tick : WebExport := { name := "oak_tick" }

pub def WebAbi.default : WebAbi :=
  let abi : WebAbi :=
    { imports := [
        WebImport.dom_create, WebImport.dom_create_text, WebImport.dom_create_comment,
        WebImport.dom_root,
        WebImport.dom_append, WebImport.dom_insert_before, WebImport.dom_remove,
        WebImport.dom_replace, WebImport.dom_set_attr, WebImport.dom_remove_attr,
        WebImport.dom_set_text, WebImport.dom_add_listener,
        WebImport.dom_add_listener_global, WebImport.dom_remove_listener_global,
        WebImport.dom_child,
        WebImport.dom_child_count,
        WebImport.dom_node_type, WebImport.dom_tag_name, WebImport.dom_value,
        WebImport.dom_query,
        WebImport.fetch_begin, WebImport.fetch_poll, WebImport.fetch_status,
        WebImport.fetch_read,
        WebImport.clipboard_available, WebImport.clipboard_read_begin,
        WebImport.clipboard_write_begin, WebImport.clipboard_poll,
        WebImport.clipboard_read, WebImport.clipboard_error,
        WebImport.now_ms, WebImport.storage_get_raw,
        WebImport.storage_set, WebImport.console_log, WebImport.try_result,
        WebImport.worker_run, WebImport.worker_poll, WebImport.worker_status,
        WebImport.worker_value, WebImport.worker_type, WebImport.worker_error,
        WebImport.worker_notes, WebImport.worker_cancel,
        WebImport.keep_set, WebImport.keep_get,
        WebImport.write_stdout, WebImport.write_stderr, WebImport.read_stdin,
        WebImport.f64_to_string,
        WebImport.event_i64, WebImport.event_f64, WebImport.event_str,
        WebImport.event_data, WebImport.event_types,
        WebImport.event_files_count, WebImport.event_file_i64,
        WebImport.event_file_str, WebImport.event_prevent_default,
        WebImport.event_stop_propagation
      ],
      exports := [
        WebExport.oak_mount, WebExport.oak_dispatch_event, WebExport.oak_tick
      ] } in
  abi
