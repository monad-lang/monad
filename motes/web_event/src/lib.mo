// web_event's library root -- bare `use web_event` resolves here.

pub use lib::event {
    WebEvent, FileInfo, ListenerFlags, HandlerResult,
    ListenerFlags.none, ListenerFlags.letters, ListenerFlags.encode,
    WebEvent.mod_shift, WebEvent.mod_ctrl, WebEvent.mod_alt, WebEvent.mod_meta,
    HandlerResult.msg, HandlerResult.ignore, HandlerResult.prevent, HandlerResult.map,
}

pub use lib::websocket {WsData, WsEvent, WsData.text_of, WsData.bytes_of}

pub use lib::rtc {
    RtcSdp, RtcIce, RtcIceServer, RtcState, RtcData, RtcChannel, RtcEvent,
    RtcSdp.kind_of, RtcSdp.text_of, RtcData.text_of, RtcData.bytes_of,
    RtcState.channel_name, RtcState.connection_name,
    encode_sdp, decode_sdp, encode_ice, decode_ice, decode_message,
    encode_ice_servers, state_of_code,
}
