// web_wasm's library root -- bare `use web_wasm` resolves here.
//
// The browser platform boundary: opaque handles, the ABI spec, the
// generated loader, and the thin IO wrappers over the RawIO externs.
// Nothing outside this mote declares a web extern.

pub use lib::types {Node, RequestId, ClipboardOp}
pub use web_event::event {WebEvent, FileInfo}

pub use lib::web_abi {
    WebAbi, WebAbi.default, WebExport, WebImport,
}

pub use lib::glue {Glue.loader}

pub use lib::dom {
    Dom.create, Dom.text_node, Dom.comment, Dom.root, Dom.append, Dom.insert_before,
    Dom.remove, Dom.replace, Dom.set_attr, Dom.remove_attr, Dom.set_text,
    Dom.on, Dom.on_with, Dom.on_window, Dom.off_window, Dom.on_document,
    Dom.off_document, Dom.on_frame, Dom.off_frame, Dom.child, Dom.child_count,
    Dom.node_type, Dom.tag_name, Dom.value, Dom.query,
}

pub use lib::fetch {Fetch.begin, Fetch.poll, Fetch.status, Fetch.read}
pub use lib::clipboard {
    Clipboard.available, Clipboard.read_begin, Clipboard.write_begin,
    Clipboard.poll, Clipboard.read, Clipboard.error,
    Clipboard.read_result, Clipboard.write_result,
}
pub use lib::event {
    WebEvent.current, WebEvent.prevent_default, WebEvent.stop_propagation, WebEvent.split_lines,
}
pub use lib::clock {Clock.now_ms}
pub use lib::storage {Storage.get, Storage.set}
pub use lib::console {Console.log}
pub use lib::try_bridge {TryBridge.push_result}
pub use lib::worker {Worker.run, Worker.poll, Worker.status, Worker.value, Worker.typ, Worker.error, Worker.notes, Worker.cancel}
pub use lib::keep {Keep.save, Keep.load}
