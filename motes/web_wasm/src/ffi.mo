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

use lib::types {Node, RequestId, ClipboardOp, CryptoOp, WebKey}
use std::bytebuf {ByteBuf}
use std::buf {Buf}
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

#[extern "c" {link_name := "web_storage_has"}]
def storage_has_raw (key : String) : RawIO I64

#[extern "c" {link_name := "web_storage_remove"}]
def storage_remove_raw (key : String) : RawIO Unit

#[extern "c" {link_name := "web_storage_clear"}]
def storage_clear_raw : RawIO Unit

#[extern "c" {link_name := "web_monotonic_ms"}]
def monotonic_ms_raw : RawIO I64

#[extern "c" {link_name := "web_media_matches"}]
def media_matches_raw (query : String) : RawIO I64

#[extern "c" {link_name := "web_media_watch"}]
def media_watch_raw (query : String) (spec : String) : RawIO Unit

#[extern "c" {link_name := "web_media_unwatch"}]
def media_unwatch_raw (query : String) : RawIO Unit

#[extern "c" {link_name := "web_dom_element_at"}]
def dom_element_at_raw (x : F64) (y : F64) : RawIO Node

#[extern "c" {link_name := "web_dom_attr"}]
def dom_attr_raw (n : Node) (name : String) : RawIO String

#[extern "c" {link_name := "web_dom_focus"}]
def dom_focus_raw (selector : String) : RawIO Unit

#[extern "c" {link_name := "web_timer_after"}]
def timer_after_raw (ms : I64) : RawIO I64

#[extern "c" {link_name := "web_fetch_begin_headers"}]
def fetch_begin_headers_raw (url : String) (method : I64) (body : String)
    (headers : String) : RawIO RequestId

#[extern "c" {link_name := "web_fetch_headers"}]
def fetch_headers_raw (r : RequestId) : RawIO String

/// Random bytes are written into a caller-owned `ByteBuf` (the typed
/// boundary; no address crosses Monad code). The i64 result is 1 when the
/// host filled it and 0 when `crypto.getRandomValues` is unavailable.
#[extern "c" {link_name := "web_crypto_random_fill"}]
def crypto_random_fill_raw (buf : ByteBuf) : RawIO I64

#[extern "c" {link_name := "web_crypto_sha256_begin"}]
def crypto_sha256_begin_raw (buf : ByteBuf) : RawIO CryptoOp

#[extern "c" {link_name := "web_crypto_poll"}]
def crypto_poll_raw (op : CryptoOp) : RawIO I64

#[extern "c" {link_name := "web_crypto_result_hex"}]
def crypto_result_hex_raw (op : CryptoOp) : RawIO String

#[extern "c" {link_name := "web_window_reload"}]
def window_reload_raw : RawIO Unit

#[extern "c" {link_name := "web_window_navigate"}]
def window_navigate_raw (url : String) : RawIO Unit

#[extern "c" {link_name := "web_window_replace"}]
def window_replace_raw (url : String) : RawIO Unit

/// `location` READS. These are the query-parameter half of an OAuth redirect:
/// the provider sends the user back with `code`/`state`/`iss` in the URL, so
/// a wasm SPA has to be able to read them. `search_param` percent-decodes
/// (and turns `+` into a space), which is what makes a base64url `code`
/// survive the trip.
#[extern "c" {link_name := "web_location_origin"}]
def location_origin_raw : RawIO String

#[extern "c" {link_name := "web_location_href"}]
def location_href_raw : RawIO String

#[extern "c" {link_name := "web_location_pathname"}]
def location_pathname_raw : RawIO String

#[extern "c" {link_name := "web_location_search"}]
def location_search_raw : RawIO String

#[extern "c" {link_name := "web_location_search_param"}]
def location_search_param_raw (name : String) : RawIO String

/// The error name of a failed WebCrypto operation (`NotSupportedError`,
/// `InvalidAccessError`, ...), or `""` when it has not failed.
#[extern "c" {link_name := "web_crypto_error"}]
def crypto_error_raw (op : CryptoOp) : RawIO String

/// The ECDSA keypair a `generate_key_begin`/`keystore_get_begin` produced.
/// Opaque host-side id: the private key never enters wasm memory.
#[extern "c" {link_name := "web_crypto_op_key"}]
def crypto_op_key_raw (op : CryptoOp) : RawIO WebKey

/// ECDSA P-256, two-phase like SHA-256. `generate` is non-extractable and
/// sign-only; the exports cover the public half only (a JWK, and the raw
/// 65-byte SEC1 point a multikey needs).
#[extern "c" {link_name := "web_ecdsa_generate_begin"}]
def ecdsa_generate_begin_raw : RawIO CryptoOp

#[extern "c" {link_name := "web_ecdsa_export_jwk_begin"}]
def ecdsa_export_jwk_begin_raw (k : WebKey) : RawIO CryptoOp

#[extern "c" {link_name := "web_ecdsa_export_raw_begin"}]
def ecdsa_export_raw_begin_raw (k : WebKey) : RawIO CryptoOp

#[extern "c" {link_name := "web_ecdsa_sign_begin"}]
def ecdsa_sign_begin_raw (k : WebKey) (data : ByteBuf) : RawIO CryptoOp

/// IndexedDB, so a non-extractable `CryptoKey` survives the OAuth redirect.
/// `get` finishes with state 3 when the slot is empty (not an error).
#[extern "c" {link_name := "web_keystore_put_begin"}]
def keystore_put_begin_raw (slot : String) (k : WebKey) : RawIO CryptoOp

#[extern "c" {link_name := "web_keystore_get_begin"}]
def keystore_get_begin_raw (slot : String) : RawIO CryptoOp

#[extern "c" {link_name := "web_keystore_delete_begin"}]
def keystore_delete_begin_raw (slot : String) : RawIO CryptoOp

/// C-only heap probes (`runtime/src/platform_web.c`): committed linear
/// memory and the collector's used bytes (live + allocated since the last
/// collection). No JS host function.
#[extern "c" {link_name := "web_memory_heap_bytes"}]
def memory_heap_bytes_raw : RawIO I64

#[extern "c" {link_name := "web_memory_heap_used"}]
def memory_heap_used_raw : RawIO I64

#[extern "c" {link_name := "web_console_log"}]
def console_log_raw (s : String) : RawIO Unit

/// The /try engine's export channel (`motes/try_engine`). Not a runtime
/// `monad_*` symbol: the C side is `web_try_result`, which forwards four
/// (ptr,len) pairs to the JS host.
#[extern "c" {link_name := "web_try_result"}]
def try_result_raw (status : I64) (value : String) (typ : String)
    (error : String) (notes : String) : RawIO Unit

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

/// The UI half of the /try worker channel (`worker.mo`). The worker runs
/// `try_engine.wasm`; the main-thread Oak app starts a run, polls, and
/// reads the finished result.
#[extern "c" {link_name := "web_worker_run"}]
def worker_run_raw (source : String) : RawIO I64

#[extern "c" {link_name := "web_worker_poll"}]
def worker_poll_raw : RawIO I64

#[extern "c" {link_name := "web_worker_status"}]
def worker_status_raw : RawIO String

#[extern "c" {link_name := "web_worker_value"}]
def worker_value_raw : RawIO String

#[extern "c" {link_name := "web_worker_type"}]
def worker_type_raw : RawIO String

#[extern "c" {link_name := "web_worker_error"}]
def worker_error_raw : RawIO String

#[extern "c" {link_name := "web_worker_notes"}]
def worker_notes_raw : RawIO String

#[extern "c" {link_name := "web_worker_cancel"}]
def worker_cancel_raw : RawIO Unit

// ── Canvas and WebGL (`canvas.mo`, `gl.mo`) ──────────────────────────
//
// Objects are I64 ids into the JS host's GL table; integer state calls go
// through one `gl_state` selector (`gl.mo` owns the numbering) and every GL
// enum value is mapped in `gl.mo`, never here.

#[extern "c" {link_name := "web_canvas_get_context"}]
def canvas_get_context_raw (canvas : Node) (flags : I64) : RawIO I64

#[extern "c" {link_name := "web_canvas_fit"}]
def canvas_fit_raw (canvas : Node) : RawIO I64

#[extern "c" {link_name := "web_dom_metric"}]
def dom_metric_raw (n : Node) (which : I64) : RawIO F64

#[extern "c" {link_name := "web_gl_info"}]
def gl_info_raw (ctx : I64) (which : I64) : RawIO I64

#[extern "c" {link_name := "web_gl_create"}]
def gl_create_raw (ctx : I64) (kind : I64) : RawIO I64

#[extern "c" {link_name := "web_gl_delete"}]
def gl_delete_raw (ctx : I64) (kind : I64) (id : I64) : RawIO Unit

#[extern "c" {link_name := "web_gl_bind"}]
def gl_bind_raw (ctx : I64) (kind : I64) (target : I64) (id : I64) : RawIO Unit

#[extern "c" {link_name := "web_gl_shader"}]
def gl_shader_raw (ctx : I64) (stage : I64) (source : String) : RawIO I64

#[extern "c" {link_name := "web_gl_link"}]
def gl_link_raw (ctx : I64) (program : I64) (vs : I64) (fs : I64) : RawIO I64

#[extern "c" {link_name := "web_gl_log"}]
def gl_log_raw : RawIO String

#[extern "c" {link_name := "web_gl_location"}]
def gl_location_raw (ctx : I64) (program : I64) (kind : I64) (name : String) : RawIO I64

#[extern "c" {link_name := "web_gl_vertex_attrib"}]
def gl_vertex_attrib_raw (ctx : I64) (index : I64) (size : I64) (typ : I64)
    (normalized : I64) (stride : I64) (offset : I64) : RawIO Unit

#[extern "c" {link_name := "web_gl_uniform_f"}]
def gl_uniform_f_raw (ctx : I64) (loc : I64) (n : I64) (x : F64) (y : F64) (z : F64)
    (w : F64) : RawIO Unit

#[extern "c" {link_name := "web_gl_clear_color"}]
def gl_clear_color_raw (ctx : I64) (r : F64) (g : F64) (b : F64) (a : F64) : RawIO Unit

#[extern "c" {link_name := "web_gl_state"}]
def gl_state_raw (ctx : I64) (which : I64) (a : I64) (b : I64) (c : I64) (d : I64) : RawIO Unit

#[extern "c" {link_name := "web_gl_draw"}]
def gl_draw_raw (ctx : I64) (indexed : I64) (mode : I64) (a : I64) (b : I64) : RawIO Unit

#[extern "c" {link_name := "web_gl_tex_image_from_image"}]
def gl_tex_image_from_image_raw (ctx : I64) (target : I64) (image : I64) : RawIO I64

// Bulk uploads take a `std::buf` buffer. The C side reads the `BufObj`'s
// element kind and count, so a byte length never crosses Monad code; the
// public wrappers in `gl.mo` pin the element type. 1 = uploaded, 0 = the
// buffer was the wrong kind or too short, or the context is unknown.

/// `bufferData` (`sub` = 0, `a` = usage) or `bufferSubData` (`sub` = 1,
/// `a` = byte offset).
#[extern "c" {link_name := "web_gl_buffer_data"}]
def gl_buffer_data_raw {E : Type} (ctx : I64) (target : I64) (sub : I64) (a : I64) (data : Buf E)
    : RawIO I64

/// `uniformMatrix{n}fv` from the first n*n elements of a `Buf F32`.
#[extern "c" {link_name := "web_gl_uniform_matrix"}]
def gl_uniform_matrix_raw (ctx : I64) (loc : I64) (n : I64) (m : Buf F32) : RawIO I64

/// RGBA8 `texImage2D` of w*h pixels from a `Buf U8` of at least w*h*4.
#[extern "c" {link_name := "web_gl_tex_image_pixels"}]
def gl_tex_image_pixels_raw (ctx : I64) (target : I64) (w : I64) (h : I64) (pixels : Buf U8)
    : RawIO I64

#[extern "c" {link_name := "web_image_load_begin"}]
def image_load_begin_raw (url : String) : RawIO I64

#[extern "c" {link_name := "web_image_info"}]
def image_info_raw (image : I64) (which : I64) : RawIO I64
