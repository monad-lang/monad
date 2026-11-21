/// The WebSocket vocabulary shared by the browser boundary and the view
/// layer: what a socket reports and what it can send.
///
/// `web_wasm` builds these from the JS `WebSocket`, `oak` names `WsEvent` in
/// `Subscription.websocket`'s handler, and `oak_wasm` hands them to it. Pure
/// data — no IO, no handles.

/// One message's payload. `text` is the decoded string, `binary` the raw
/// bytes; the socket's `binaryType` decides which a frame becomes.
pub type WsData {
    text (s : String),
    binary (bytes : List U8)
}

/// A socket's lifecycle as the app sees it.
pub type WsEvent {
    /// The upgrade finished; `protocol` is the server's choice ("" when
    /// none was negotiated).
    opened (protocol : String),
    /// A whole message arrived.
    message (data : WsData),
    /// The socket is gone. `clean` is the RFC's "closed by the close
    /// handshake" flag; `code` is 1006 when the transport dropped.
    closed (code : I64) (reason : String) (clean : Bool),
    /// The connection failed before it opened (bad URL, network, refused
    /// upgrade).
    failed
}

/// The payload's text (`""` for a binary message).
pub def WsData.text_of (d : WsData) : String :=
    match d {
        WsData.text s => s,
        WsData.binary _ => ""
    }

/// The payload's bytes (a text message's UTF-8).
pub def WsData.bytes_of (d : WsData) : List U8 :=
    match d {
        WsData.text s => String.to_list s,
        WsData.binary b => b
    }
