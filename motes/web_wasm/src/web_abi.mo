/// The web boundary as data.
///
/// This is the single source of truth for the imports the JS runtime must
/// provide and the exports it may call. `glue.mo` renders the import map
/// from this list; `runtime/src/platform_web.c` declares the matching
/// `monad_*` wrappers; `ffi.mo` declares the Monad side. A signature test
/// checks the three agree.
///
/// The parameter/result strings are documentation for the generated loader
/// (`"i64"`, `"string"`, `"void"`); the C ABI is the authority.

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
  { module := "monad", name := "storage_get_raw", params := ["i64", "i64"], result := "i64" }

def WebImport.storage_set : WebImport :=
  { module := "monad", name := "storage_set", params := ["i64", "i64", "i64", "i64"], result := "void" }

def WebImport.console_log : WebImport :=
  { module := "monad", name := "console_log", params := ["i64", "i64"], result := "void" }

def WebExport.oak_mount : WebExport := { name := "oak_mount" }
def WebExport.oak_dispatch_event : WebExport := { name := "oak_dispatch_event" }
def WebExport.oak_tick : WebExport := { name := "oak_tick" }

pub def WebAbi.default : WebAbi :=
  let abi : WebAbi :=
    { imports := [
        WebImport.dom_create, WebImport.dom_create_text, WebImport.dom_root,
        WebImport.dom_append, WebImport.dom_insert_before, WebImport.dom_remove,
        WebImport.dom_replace, WebImport.dom_set_attr, WebImport.dom_remove_attr,
        WebImport.dom_set_text, WebImport.dom_add_listener,
        WebImport.fetch_begin, WebImport.fetch_poll, WebImport.fetch_status,
        WebImport.fetch_read, WebImport.now_ms, WebImport.storage_get_raw,
        WebImport.storage_set, WebImport.console_log
      ],
      exports := [
        WebExport.oak_mount, WebExport.oak_dispatch_event, WebExport.oak_tick
      ] } in
  abi
