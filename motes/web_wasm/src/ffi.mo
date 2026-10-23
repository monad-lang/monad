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

use lib::types {Node, RequestId}
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
def dom_add_listener_raw (n : Node) (event : String) (handler : I64) : RawIO Unit

#[extern "c" {link_name := "web_dom_child"}]
def dom_child_raw (n : Node) (index : I64) : RawIO Node

#[extern "c" {link_name := "web_fetch_begin"}]
def fetch_begin_raw (url : String) (method : I64) (body : String) : RawIO RequestId

#[extern "c" {link_name := "web_fetch_poll"}]
def fetch_poll_raw (r : RequestId) : RawIO I64

#[extern "c" {link_name := "web_fetch_status"}]
def fetch_status_raw (r : RequestId) : RawIO I64

#[extern "c" {link_name := "web_fetch_read"}]
def fetch_read_raw (r : RequestId) (max : I64) : RawIO String

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
