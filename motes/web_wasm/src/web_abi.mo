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

/// Presence-aware storage: `has` distinguishes an absent key from an empty
/// stored value (the old `""` sentinel conflated them); `remove`/`clear`
/// delete. `has` returns an i64 truth value.
def WebImport.storage_has : WebImport :=
    { module := "monad", name := "storage_has", params := ["i64", "i64"], result := "i64" }

def WebImport.storage_remove : WebImport :=
    { module := "monad", name := "storage_remove", params := ["i64", "i64"], result := "void" }

def WebImport.storage_clear : WebImport :=
    { module := "monad", name := "storage_clear", params := List.empty, result := "void" }

/// `performance.now()` in milliseconds, for measuring intervals (the page
/// clock `now_ms` is wall-clock only).
def WebImport.monotonic_ms : WebImport :=
    { module := "monad", name := "monotonic_ms", params := List.empty, result := "i64" }

/// `matchMedia(query).matches`, and a `change` listener whose spec carries
/// the handler id (the live event is a `MediaQueryListEvent` snapshot).
def WebImport.media_matches : WebImport :=
    { module := "monad", name := "media_matches", params := ["i64", "i64"], result := "i64" }

def WebImport.media_watch : WebImport :=
    { module := "monad", name := "media_watch", params := ["i64", "i64", "i64", "i64"], result := "void" }

def WebImport.media_unwatch : WebImport :=
    { module := "monad", name := "media_unwatch", params := ["i64", "i64"], result := "void" }

/// A hit test (`document.elementFromPoint`) and an attribute read, so a
/// touch drag can work out which element is under the finger.
def WebImport.dom_element_at : WebImport :=
    { module := "monad", name := "dom_element_at", params := ["f64", "f64"], result := "i64" }

def WebImport.dom_attr : WebImport :=
    { module := "monad", name := "dom_attr", params := ["i64", "i64", "i64", "i64", "i64"], result := "i64" }

/// Move focus to the first node matching a selector (used after a patch, so
/// a dialog inserted this frame can take focus).
def WebImport.dom_focus : WebImport :=
    { module := "monad", name := "dom_focus", params := ["i64", "i64"], result := "void" }

/// One-shot delayed message: returns a timer id in the top bit that
/// `Handler.id` never uses; the wasm runtime stores the Msg and resolves it
/// when the host calls `oak_dispatch_event(id)`.
def WebImport.timer_after : WebImport :=
    { module := "monad", name := "timer_after", params := ["i64"], result := "i64" }

/// Request headers as a length-prefixed blob (`"<klen>:<key><vlen>:<value>"`
/// repeated), plus the response-header reader over the same encoding.
def WebImport.fetch_begin_headers : WebImport :=
    { module := "monad", name := "fetch_begin_headers",
        params := ["i64", "i64", "i64", "i64", "i64", "i64", "i64"], result := "i64" }

def WebImport.fetch_headers : WebImport :=
    { module := "monad", name := "fetch_headers", params := ["i64", "i64", "i64"], result := "i64" }

/// `crypto.getRandomValues` into a caller-owned buffer (1 = filled,
/// 0 = unavailable); SHA-256 is two-phase like fetch.
def WebImport.crypto_random_fill : WebImport :=
    { module := "monad", name := "crypto_random_fill", params := ["i64", "i64"], result := "i64" }

def WebImport.crypto_sha256_begin : WebImport :=
    { module := "monad", name := "crypto_sha256_begin", params := ["i64", "i64"], result := "i64" }

def WebImport.crypto_poll : WebImport :=
    { module := "monad", name := "crypto_poll", params := ["i64"], result := "i64" }

def WebImport.crypto_result_hex : WebImport :=
    { module := "monad", name := "crypto_result_hex", params := ["i64", "i64", "i64"], result := "i64" }

/// `location.reload`/`assign`; a page that wants to recover from heap
/// pressure persists first, then reloads.
def WebImport.window_reload : WebImport :=
    { module := "monad", name := "window_reload", params := List.empty, result := "void" }

def WebImport.window_navigate : WebImport :=
    { module := "monad", name := "window_navigate", params := ["i64", "i64"], result := "void" }

/// The allocator's last word before it traps: `console.error` with the
/// requested and committed sizes.
def WebImport.oom : WebImport :=
    { module := "monad", name := "oom", params := ["i64", "i64"], result := "void" }

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

/// Canvas + WebGL (`canvas.mo`, `gl.mo`). A context is acquired from a
/// `<canvas>` node (WebGL2 first, then WebGL1); GL objects are ids into the
/// host's table; integer state calls share one `gl_state` selector.
def WebImport.canvas_get_context : WebImport :=
    { module := "monad", name := "canvas_get_context", params := ["i64", "i64"], result := "i64" }

def WebImport.canvas_fit : WebImport :=
    { module := "monad", name := "canvas_fit", params := ["i64"], result := "i64" }

def WebImport.dom_metric : WebImport :=
    { module := "monad", name := "dom_metric", params := ["i64", "i64"], result := "f64" }

def WebImport.gl_info : WebImport :=
    { module := "monad", name := "gl_info", params := ["i64", "i64"], result := "i64" }

def WebImport.gl_create : WebImport :=
    { module := "monad", name := "gl_create", params := ["i64", "i64"], result := "i64" }

def WebImport.gl_delete : WebImport :=
    { module := "monad", name := "gl_delete", params := ["i64", "i64", "i64"], result := "void" }

def WebImport.gl_bind : WebImport :=
    { module := "monad", name := "gl_bind",
        params := ["i64", "i64", "i64", "i64"], result := "void" }

def WebImport.gl_shader : WebImport :=
    { module := "monad", name := "gl_shader",
        params := ["i64", "i64", "i64", "i64"], result := "i64" }

def WebImport.gl_link : WebImport :=
    { module := "monad", name := "gl_link",
        params := ["i64", "i64", "i64", "i64"], result := "i64" }

def WebImport.gl_log : WebImport :=
    { module := "monad", name := "gl_log", params := ["i64", "i64"], result := "i64" }

def WebImport.gl_location : WebImport :=
    { module := "monad", name := "gl_location",
        params := ["i64", "i64", "i64", "i64", "i64"], result := "i64" }

def WebImport.gl_vertex_attrib : WebImport :=
    { module := "monad", name := "gl_vertex_attrib",
        params := ["i64", "i64", "i64", "i64", "i64", "i64", "i64"], result := "void" }

def WebImport.gl_uniform_f : WebImport :=
    { module := "monad", name := "gl_uniform_f",
        params := ["i64", "i64", "i64", "f64", "f64", "f64", "f64"], result := "void" }

def WebImport.gl_clear_color : WebImport :=
    { module := "monad", name := "gl_clear_color",
        params := ["i64", "f64", "f64", "f64", "f64"], result := "void" }

def WebImport.gl_state : WebImport :=
    { module := "monad", name := "gl_state",
        params := ["i64", "i64", "i64", "i64", "i64", "i64"], result := "void" }

def WebImport.gl_draw : WebImport :=
    { module := "monad", name := "gl_draw",
        params := ["i64", "i64", "i64", "i64", "i64"], result := "void" }

def WebImport.gl_tex_image_from_image : WebImport :=
    { module := "monad", name := "gl_tex_image_from_image",
        params := ["i64", "i64", "i64"], result := "i64" }

/// Image loading for textures is two-phase like fetch: the promise only
/// updates the host table and `image_info` polls it.
def WebImport.image_load_begin : WebImport :=
    { module := "monad", name := "image_load_begin", params := ["i64", "i64"], result := "i64" }

def WebImport.image_info : WebImport :=
    { module := "monad", name := "image_info", params := ["i64", "i64"], result := "i64" }

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
            WebImport.storage_has, WebImport.storage_remove, WebImport.storage_clear,
            WebImport.monotonic_ms,
            WebImport.media_matches, WebImport.media_watch, WebImport.media_unwatch,
            WebImport.dom_element_at, WebImport.dom_attr, WebImport.dom_focus,
            WebImport.timer_after,
            WebImport.fetch_begin_headers, WebImport.fetch_headers,
            WebImport.crypto_random_fill, WebImport.crypto_sha256_begin,
            WebImport.crypto_poll, WebImport.crypto_result_hex,
            WebImport.window_reload, WebImport.window_navigate, WebImport.oom,
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
            WebImport.event_stop_propagation,
            WebImport.canvas_get_context, WebImport.canvas_fit, WebImport.dom_metric,
            WebImport.gl_info, WebImport.gl_create, WebImport.gl_delete,
            WebImport.gl_bind, WebImport.gl_shader, WebImport.gl_link, WebImport.gl_log,
            WebImport.gl_location, WebImport.gl_vertex_attrib, WebImport.gl_uniform_f,
            WebImport.gl_clear_color, WebImport.gl_state, WebImport.gl_draw,
            WebImport.gl_tex_image_from_image, WebImport.image_load_begin,
            WebImport.image_info
        ],
            exports := [
                WebExport.oak_mount, WebExport.oak_dispatch_event, WebExport.oak_tick
            ] } in
    abi
