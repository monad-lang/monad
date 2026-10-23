// web_wasm's library root -- bare `use web_wasm` resolves here.
//
// The browser platform boundary: opaque handles, the ABI spec, the
// generated loader, and the thin IO wrappers over the RawIO externs.
// Nothing outside this mote declares a web extern.

pub use lib::types {Node, RequestId}

pub use lib::web_abi {
    WebAbi, WebAbi.default, WebExport, WebImport,
}

pub use lib::glue {Glue.loader}

pub use lib::dom {
    Dom.create, Dom.text_node, Dom.comment, Dom.root, Dom.append, Dom.insert_before,
    Dom.remove, Dom.replace, Dom.set_attr, Dom.remove_attr, Dom.set_text,
    Dom.on, Dom.child,
}

pub use lib::fetch {Fetch.begin, Fetch.poll, Fetch.status, Fetch.read}
pub use lib::clock {Clock.now_ms}
pub use lib::storage {Storage.get, Storage.set}
pub use lib::console {Console.log}
