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

use lib::types {
    Node, RequestId, ClipboardOp, CryptoOp, WebKey, WebSocket, RtcPeer, MediaStream,
    MediaStreamOp,
}
use std::bytebuf {ByteBuf}
use std::buf {Buf}
use std::ref {Ref}

#[extern "c" {link_name := "web_dom_create"}]
def dom_create_raw (tag : String) : RawIO Node

#[extern "c" {link_name := "web_dom_create_svg"}]
def dom_create_svg_raw (tag : String) : RawIO Node

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

#[extern "c" {link_name := "web_dom_in_svg"}]
def dom_in_svg_raw (n : Node) : RawIO I64

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

/// The bytes still unread in a response body. `fetch_read` copies a chunk
/// into a Monad `String`, which is NUL-terminated -- so a BINARY body (an
/// audio file, an image) truncated at its first zero byte. This pair is the
/// byte channel: `fetch_len` sizes a caller-owned `ByteBuf`, and
/// `fetch_read_bytes` fills it. Same shape as `ws_peek`/`ws_read`.
#[extern "c" {link_name := "web_fetch_len"}]
def fetch_len_raw (r : RequestId) : RawIO I64

#[extern "c" {link_name := "web_fetch_read_bytes"}]
def fetch_read_bytes_raw (r : RequestId) (buf : ByteBuf) : RawIO I64

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

/// Bind a media stream to a `<video>`/`<audio>` node as its `srcObject`, so
/// the element plays it.
///
/// One of the boundary's few property writes, and deliberately not general:
/// it takes a typed `MediaStream` and a `Node`, never a property name, so it
/// cannot set an arbitrary JS property the way a `set_prop(name, value)`
/// primitive would. `media_element.mo`'s volume/muted/loop setters are the
/// other family, and each is likewise typed on its own property -- there is
/// no primitive that reaches a property name the caller chooses.
#[extern "c" {link_name := "web_dom_set_src_object"}]
def dom_set_src_object_raw (n : Node) (stream : MediaStream) : RawIO I64

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

/// The float state selector (`gl.mo` numbers it): 0 = `polygonOffset`.
#[extern "c" {link_name := "web_gl_state_f"}]
def gl_state_f_raw (ctx : I64) (which : I64) (a : F64) (b : F64) (c : F64) (d : F64) : RawIO Unit

/// A data-less depth `texImage2D` into the bound `TEXTURE_2D`; 1 = done,
/// 0 = no depth-texture support, bad size, or unknown context.
#[extern "c" {link_name := "web_gl_tex_image_depth"}]
def gl_tex_image_depth_raw (ctx : I64) (w : I64) (h : I64) : RawIO I64

#[extern "c" {link_name := "web_gl_framebuffer_texture"}]
def gl_framebuffer_texture_raw (ctx : I64) (attachment : I64) (texture : I64) : RawIO Unit

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

// ── WebSocket (motes/web_wasm/src/websocket.mo) ────────────────────────
//
// Payloads cross through caller-owned `ByteBuf`s (`ws_read`, `ws_send`), so
// a message larger than the 64 KiB scratch buffer is not truncated. The
// JS callbacks only ever append to a per-socket queue; wasm is re-entered
// through `dispatchWith` from a fresh task, never from a promise.

#[extern "c" {link_name := "web_ws_open"}]
def ws_open_raw (url : String) (protocols : String) : RawIO WebSocket

#[extern "c" {link_name := "web_ws_state"}]
def ws_state_raw (w : WebSocket) : RawIO I64

#[extern "c" {link_name := "web_ws_peek"}]
def ws_peek_raw (w : WebSocket) (which : I64) : RawIO I64

#[extern "c" {link_name := "web_ws_read"}]
def ws_read_raw (w : WebSocket) (buf : ByteBuf) : RawIO I64

#[extern "c" {link_name := "web_ws_info"}]
def ws_info_raw (w : WebSocket) (which : I64) : RawIO I64

#[extern "c" {link_name := "web_ws_text"}]
def ws_text_raw (w : WebSocket) (which : I64) : RawIO String

#[extern "c" {link_name := "web_ws_send"}]
def ws_send_raw (w : WebSocket) (buf : ByteBuf) (is_binary : I64) : RawIO I64

#[extern "c" {link_name := "web_ws_close"}]
def ws_close_raw (w : WebSocket) (code : I64) (reason : String) : RawIO I64

#[extern "c" {link_name := "web_ws_watch"}]
def ws_watch_raw (w : WebSocket) (handler : U32) : RawIO I64

#[extern "c" {link_name := "web_ws_unwatch"}]
def ws_unwatch_raw (w : WebSocket) : RawIO I64

#[extern "c" {link_name := "web_ws_buffered"}]
def ws_buffered_raw (w : WebSocket) : RawIO I64

#[extern "c" {link_name := "web_ws_free"}]
def ws_free_raw (w : WebSocket) : RawIO I64

// ── Sound and audio (`motes/web_wasm/src/{audio,media_element}.mo`) ────
//
// Two browser APIs behind one vocabulary. The Web Audio half synthesizes
// (`AudioContext` + oscillator/noise/buffer nodes); the media half drives
// an `<audio>`/`<video>` ELEMENT a view already mounted, addressed by
// selector the way `Dom.focus` is.
//
// A gain is a plain `F64`, a start/stop offset is in seconds, and
// everything else is a word, so the C wrapper stays a pass-through.

/// Open (or reuse) the page's `AudioContext`. The context starts
/// suspended until a user gesture; see `Audio.resume`.
#[extern "c" {link_name := "web_audio_open"}]
def audio_open_raw : RawIO I64

/// `AudioContext.state` as a word: 0 suspended, 1 running, 2 closed,
/// 3 interrupted. `Audio.state` maps it.
#[extern "c" {link_name := "web_audio_state"}]
def audio_state_raw (ctx : I64) : RawIO I64

/// `AudioContext.resume()` -- the gesture-gated start. Returns 1 when the
/// context is running after the call, 0 otherwise (the promise may not
/// have settled, so a caller polls `Audio.state`).
#[extern "c" {link_name := "web_audio_resume"}]
def audio_resume_raw (ctx : I64) : RawIO I64

/// `currentTime` in whole MICROseconds, so it crosses as an `I64` without
/// losing the sub-millisecond resolution a scheduled envelope needs.
#[extern "c" {link_name := "web_audio_now_us"}]
def audio_now_us_raw (ctx : I64) : RawIO I64

/// `sampleRate` in Hz (e.g. 48000). `Audio.play_pcm` needs it to declare
/// a PCM buffer's own rate.
#[extern "c" {link_name := "web_audio_sample_rate"}]
def audio_sample_rate_raw (ctx : I64) : RawIO I64

/// The context's master gain (0..1, or more for headroom). Applies to
/// every voice, so it is the one place a mute belongs.
#[extern "c" {link_name := "web_audio_set_master"}]
def audio_set_master_raw (ctx : I64) (gain : F64) : RawIO Unit

/// One oscillator voice: `wave` is a `Wave` code (see `audio.mo`), `freq`
/// in Hz, `gain` its peak, `duration_ms` how long it sounds, and
/// `attack_ms`/`release_ms` the linear envelope's two ramps. It starts now
/// and stops itself, so the node is only needed to cut it short.
#[extern "c" {link_name := "web_audio_tone"}]
def audio_tone_raw (ctx : I64) (wave : I64) (freq : F64) (gain : F64)
    (duration_ms : I64) (attack_ms : I64) (release_ms : I64) : RawIO I64

/// Stop a voice early (`stop(0)` now). Safe on an already-finished one.
#[extern "c" {link_name := "web_audio_stop"}]
def audio_stop_raw (node : I64) : RawIO Unit

/// A filtered white-noise burst: `gain` its peak, `duration_ms` how long,
/// `lowpass_hz` the filter cutoff (0 = no filter). The shape a percussive
/// hit or a whoosh needs, without a sample file.
#[extern "c" {link_name := "web_audio_noise"}]
def audio_noise_raw (ctx : I64) (gain : F64) (duration_ms : I64)
    (lowpass_hz : F64) : RawIO I64

/// Play `frames` mono samples from a caller-owned `Buf F32` (values in
/// -1..1), resampled to the context's rate. Returns a node so a long voice
/// can be stopped; a one-shot drops it. The C wrapper validates the
/// buffer's kind and length before the host sees its payload.
#[extern "c" {link_name := "web_audio_play_pcm"}]
def audio_play_pcm_raw (ctx : I64) (frames : Buf F32) (sample_rate : I64)
    (gain : F64) : RawIO I64

/// Start decoding an audio FILE (mp3/ogg/wav/...) from bytes: fetch it,
/// then hand the body here. Two-phase like SHA-256 -- poll
/// `audio_decode_poll`, then read the `Sound`.
#[extern "c" {link_name := "web_audio_decode_begin"}]
def audio_decode_begin_raw (ctx : I64) (bytes : ByteBuf) : RawIO I64

/// 0 pending, 1 done, 2 failed (the fetch/clipboard convention).
#[extern "c" {link_name := "web_audio_decode_poll"}]
def audio_decode_poll_raw (op : I64) : RawIO I64

/// The `Sound` a finished decode produced (the null handle otherwise).
#[extern "c" {link_name := "web_audio_decode_sound"}]
def audio_decode_sound_raw (op : I64) : RawIO I64

/// The `DOMException.name` a failed decode produced (empty otherwise).
#[extern "c" {link_name := "web_audio_decode_error"}]
def audio_decode_error_raw (op : I64) : RawIO String

/// Play a decoded `Sound` whole, or from `offset_ms` for `duration_ms`
/// (0 for both means "all of it"). `gain` is the voice's peak.
#[extern "c" {link_name := "web_audio_play_sound"}]
def audio_play_sound_raw (ctx : I64) (sound : I64) (gain : F64)
    (offset_ms : I64) (duration_ms : I64) : RawIO I64

/// A `Sound`'s length in whole milliseconds (0 for an unknown handle).
#[extern "c" {link_name := "web_audio_sound_duration_ms"}]
def audio_sound_duration_ms_raw (sound : I64) : RawIO I64

// ── `<audio>` / `<video>` element control ──────────────────────────────
//
// The ELEMENT is mounted by the view (`Html.audio`/`Html.video`), so a
// program reaches it by selector exactly as `Dom.focus` does. Every call
// answers 1 when it found and applied to the element, 0 when no element
// matched (a selector typo is silent in the DOM, so the flag is the only
// signal a caller gets).
//
// `autoplay` attributes are deliberately NOT the mechanism: a policy that
// blocks it fails silently, whereas `MediaElement.play` reports the block
// (state 3).

/// `element.play()`. Returns 0 no such element, 1 playing, 3 blocked by
/// the autoplay policy (the promise rejected with `NotAllowedError`).
#[extern "c" {link_name := "web_media_play"}]
def media_play_raw (selector : String) : RawIO I64

#[extern "c" {link_name := "web_media_pause"}]
def media_pause_raw (selector : String) : RawIO I64

/// `currentTime = ms / 1000`, clamped to the media's duration by the host.
#[extern "c" {link_name := "web_media_seek"}]
def media_seek_raw (selector : String) (ms : I64) : RawIO I64

/// `volume` in 0..1 (the host clamps; `F64` because a fade is fractional).
#[extern "c" {link_name := "web_media_set_volume"}]
def media_set_volume_raw (selector : String) (volume : F64) : RawIO I64

#[extern "c" {link_name := "web_media_set_muted"}]
def media_set_muted_raw (selector : String) (muted : I64) : RawIO I64

#[extern "c" {link_name := "web_media_set_loop"}]
def media_set_loop_raw (selector : String) (looping : I64) : RawIO I64

/// Element state as one word, selected by `which` (see `media_element.mo`):
/// 0 paused, 1 ended, 2 readyState, 3 seeking, 4 muted, 5 looping,
/// 6 playbackRate×1000. Reads 0 for a missing element.
#[extern "c" {link_name := "web_media_info"}]
def media_info_raw (selector : String) (which : I64) : RawIO I64

/// `currentTime`/`duration` in whole milliseconds (`which`: 0 current,
/// 1 duration). `duration` is `NaN` before metadata, which reads as -1 so
/// a caller can tell it from a zero-length clip.
#[extern "c" {link_name := "web_media_time_ms"}]
def media_time_ms_raw (selector : String) (which : I64) : RawIO I64

/// The media's `volume`, 0..1 (1 for a missing element).
#[extern "c" {link_name := "web_media_volume"}]
def media_volume_raw (selector : String) : RawIO F64

// ── WebRTC (motes/web_wasm/src/rtc.mo, media_stream.mo) ────────────────
//
// The peer connection's callbacks only ever append to a per-peer queue, so
// wasm is never re-entered from a browser callback and the Monad side drains
// at its own pace -- the same contract as the WebSocket block above. What the
// browser's own setters report (the description it produced, each candidate
// it gathered, every connection- and channel-state change) arrives the same
// way, which is what lets `set_local` answer at the call instead of returning
// a promise.
//
// `getUserMedia` is the one genuinely promise-based operation, so it is
// two-phase like `fetch`/`clipboard`/`crypto`: `*_begin`, then a poll.
//
// One extern per OPERATION, not one merged `(op, blob, num)` entry point. A
// merged control word would have to carry a description, a flag byte and an
// index at once, so its packing would be a second ABI the two sides could
// drift on with no test to catch it. The `which`-selected READERS are the
// other half of that judgement: there a selector only chooses among columns
// of ONE queue entry, which is exactly the "merge twins behind an I64 flag"
// case.

/// Create a peer connection from an ICE-server blob (`encode_ice_servers`).
#[extern "c" {link_name := "web_rtc_open"}]
def rtc_open_raw (servers : String) : RawIO RtcPeer

/// The queue's head, selected by `which`:
/// 0 = the head entry's kind (0 when the queue is empty),
/// 1 = the peer's live connection-state code,
/// 2 = the head entry's payload length in bytes.
#[extern "c" {link_name := "web_rtc_peek"}]
def rtc_peek_raw (p : RtcPeer) (which : I64) : RawIO I64

/// Read the head entry's payload into a caller-owned `ByteBuf` and pop it;
/// answers the entry's kind, exactly like `ws_read`. One buffer for every
/// kind: a description, a candidate blob, a channel label and a message body
/// are all bytes, and the kind tells the caller how to read them.
#[extern "c" {link_name := "web_rtc_read"}]
def rtc_read_raw (p : RtcPeer) (buf : ByteBuf) : RawIO I64

/// A numeric head-entry field, selected by `which`:
/// 0 = the state code, 1 = `ordered` (0/1), 2 = `max_retransmits`,
/// 3 = the binary flag (1 when the message payload is bytes).
#[extern "c" {link_name := "web_rtc_info"}]
def rtc_info_raw (p : RtcPeer) (which : I64) : RawIO I64

/// `setLocalDescription`: `blob` is `encode_sdp`. 1 on success.
#[extern "c" {link_name := "web_rtc_set_local"}]
def rtc_set_local_raw (p : RtcPeer) (blob : String) : RawIO I64

/// `setRemoteDescription`: `blob` is `encode_sdp`. 1 on success.
#[extern "c" {link_name := "web_rtc_set_remote"}]
def rtc_set_remote_raw (p : RtcPeer) (blob : String) : RawIO I64

/// `addIceCandidate`: `blob` is `encode_ice`. 1 on success (also for the
/// end-of-candidates marker).
#[extern "c" {link_name := "web_rtc_add_ice"}]
def rtc_add_ice_raw (p : RtcPeer) (blob : String) : RawIO I64

/// `createDataChannel`. `num` packs `ordered` in bit 0 and
/// `max_retransmits + 1` above it, so -1 (the "reliable" sentinel) becomes 0
/// and a partially reliable channel keeps its small count.
#[extern "c" {link_name := "web_rtc_open_channel"}]
def rtc_open_channel_raw (p : RtcPeer) (label : String) (num : I64) : RawIO I64

/// Send one message on the channel called `label`. `payload` is a `ByteBuf`
/// of the message's bytes and `is_binary` says which way to send it.
#[extern "c" {link_name := "web_rtc_send"}]
def rtc_send_raw (p : RtcPeer) (label : String) (payload : ByteBuf) (is_binary : I64)
    : RawIO I64

/// Send a `MediaStream`'s tracks over the peer. 1 when at least one track was
/// added.
#[extern "c" {link_name := "web_rtc_add_stream"}]
def rtc_add_stream_raw (p : RtcPeer) (stream : MediaStream) : RawIO I64

/// `RTCPeerConnection.close`. Always 1.
#[extern "c" {link_name := "web_rtc_close"}]
def rtc_close_raw (p : RtcPeer) : RawIO I64

/// Have the host dispatch `handler` (an oak handler id) when the peer's queue
/// gains entries. One dispatch drains everything queued.
#[extern "c" {link_name := "web_rtc_watch"}]
def rtc_watch_raw (p : RtcPeer) (handler : U32) : RawIO I64

#[extern "c" {link_name := "web_rtc_unwatch"}]
def rtc_unwatch_raw (p : RtcPeer) : RawIO I64

#[extern "c" {link_name := "web_rtc_free"}]
def rtc_free_raw (p : RtcPeer) : RawIO I64

/// Start a media request for `constraints` (the browser's
/// `MediaStreamConstraints`/`DisplayMediaStreamOptions` as JSON text).
///
/// `display` picks the API: 0 is `getUserMedia` (camera/microphone), 1 is
/// `getDisplayMedia` (screen). One native behind a flag rather than two:
/// the request, the polling and the result are identical, and only the
/// call differs -- a duplicated native would mean two of everything.
#[extern "c" {link_name := "web_media_get_begin"}]
def media_get_begin_raw (constraints : String) (display : I64) : RawIO MediaStreamOp

/// 0 pending, 1 done, 2 failed.
#[extern "c" {link_name := "web_media_poll"}]
def media_poll_raw (op : MediaStreamOp) : RawIO I64

/// The stream a finished operation produced (the null handle until done).
#[extern "c" {link_name := "web_media_stream"}]
def media_stream_raw (op : MediaStreamOp) : RawIO MediaStream

/// The permission error's DOMException name (`NotAllowedError`,
/// `NotFoundError`, ...).
#[extern "c" {link_name := "web_media_error"}]
def media_error_raw (op : MediaStreamOp) : RawIO String

/// Release a stream's host slot (the tracks themselves are the browser's).
#[extern "c" {link_name := "web_media_free"}]
def media_free_raw (stream : MediaStream) : RawIO I64

/// The `MediaStream` a `RtcEvent.track` id names.
///
/// A pure `RtcEvent` carries a bare `I64` (the pure layer must not name a
/// `web_wasm` handle), so this is the bridge back to a typed handle. The host
/// answers the null handle when the id is not a live stream slot, which
/// `MediaStream.attach`/`Rtc.add_stream` already refuse.
#[extern "c" {link_name := "web_media_stream_of"}]
def media_stream_of_raw (id : I64) : RawIO MediaStream

/// Release a finished operation's host slot. `MediaStream.stop` reclaims the
/// op that produced a stream; a FAILED request produces no stream, so its op
/// is released here instead.
#[extern "c" {link_name := "web_media_free_op"}]
def media_free_op_raw (op : MediaStreamOp) : RawIO I64
