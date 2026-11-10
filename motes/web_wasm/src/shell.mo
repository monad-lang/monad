/// The browser deployment shell, generated from data.
///
/// This is a LIBRARY, not a compiler command: the shell is web tooling, and
/// an app's `[[script]]` decides where the files go. `index_html` emits the
/// page; `Glue.loader` (also here) emits `web.js`. `web_runtime.js` is the
/// hand-written host and is copied beside them.
///
/// (The hand-written `float_format.js` is still copied beside the runtime
/// until `F64.to_string` becomes pure Monad; that is a separate, larger
/// change: it needs an `F64 -> bits` accessor and a shortest-round-trip
/// decimal algorithm.)

pub struct ShellOptions {
    /// The compiled module's file name (`app.wasm`).
    wasm : String,
    /// The mount selector (`#app`).
    selector : String,
    /// The page title.
    title : String,
    /// Extra CSS, or `""`.
    css : String
}

pub def Shell.default_options (wasm : String) : ShellOptions :=
    { wasm := wasm, selector := "#app", title := "Monad", css := "" }

def Shell.css_block (o : ShellOptions) : String :=
    if String.is_empty o.css
    then ""
    else String.concat "<style>\n" (String.concat o.css "\n</style>\n")

def Shell.script_block (o : ShellOptions) : String :=
    String.concat "<script type=\"module\">\nimport { start } from './web.js';\nstart('./"
        (String.concat o.wasm
            (String.concat "', '" (String.concat o.selector "');\n</script>\n")))

def Shell.mount_div (o : ShellOptions) : String :=
    if String.starts_with "#" o.selector
    then String.concat "<div id=\"" (String.concat (String.drop 1i64 o.selector) "\"></div>\n")
    else "<div></div>\n"

/// The deployable `index.html`.
pub def Shell.index_html (o : ShellOptions) : String :=
    String.concat_list [
        "<!doctype html>\n",
        "<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n",
        "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n",
        "<title>", o.title, "</title>\n", Shell.css_block o,
        "</head>\n<body>\n",
        Shell.mount_div o,
        Shell.script_block o,
        "</body>\n</html>\n",
    ]
