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
  { module := "monad", name := "dom_add_listener", params := ["i64", "i64", "i64", "i64"], result := "void" }

def WebImport.dom_child : WebImport :=
  { module := "monad", name := "dom_child", params := ["i64", "i64"], result := "i64" }

def WebImport.fetch_begin : WebImport :=
  { module := "monad", name := "fetch_begin", params := ["i64", "i64", "i64", "i64", "i64"], result := "i64" }

def WebImport.fetch_poll : WebImport :=
  { module := "monad", name := "fetch_poll", params := ["i64"], result := "i64" }

def WebImport.fetch_status : WebImport :=
  { module := "monad", name := "fetch_status", params := ["i64"], result := "i64" }

def WebImport.fetch_read : WebImport :=
  { module := "monad", name := "fetch_read", params := ["i64", "i64", "i64"], result := "i64" }

def WebImport.now_ms : WebImport :=
  { module := "monad", name := "now_ms", params := List.empty, result := "i64" }

def WebImport.storage_get_raw : WebImport :=
  { module := "monad", name := "storage_get_raw", params := ["i64", "i64", "i64", "i64"], result := "i64" }

def WebImport.storage_set : WebImport :=
  { module := "monad", name := "storage_set", params := ["i64", "i64", "i64", "i64"], result := "void" }

def WebImport.console_log : WebImport :=
  { module := "monad", name := "console_log", params := ["i64", "i64"], result := "void" }

/// The runtime's own console I/O. `platform_web.c` declares these next to
/// the `web_*` wrappers (module "monad"), so every program that can print
/// needs them in the import object even if it never calls a `web_*` one.
def WebImport.write_stdout : WebImport :=
  { module := "monad", name := "write_stdout", params := ["i64", "i64"], result := "i64" }

def WebImport.write_stderr : WebImport :=
  { module := "monad", name := "write_stderr", params := ["i64", "i64"], result := "i64" }

def WebImport.read_stdin : WebImport :=
  { module := "monad", name := "read_stdin", params := ["i64", "i64"], result := "i64" }

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
        WebImport.dom_set_text, WebImport.dom_add_listener, WebImport.dom_child,
        WebImport.fetch_begin, WebImport.fetch_poll, WebImport.fetch_status,
        WebImport.fetch_read, WebImport.now_ms, WebImport.storage_get_raw,
        WebImport.storage_set, WebImport.console_log,
        WebImport.write_stdout, WebImport.write_stderr, WebImport.read_stdin
      ],
      exports := [
        WebExport.oak_mount, WebExport.oak_dispatch_event, WebExport.oak_tick
      ] } in
  abi
