// web_event's library root -- bare `use web_event` resolves here.

pub use lib::event {
    WebEvent, FileInfo, ListenerFlags, HandlerResult,
    ListenerFlags.none, ListenerFlags.letters, ListenerFlags.encode,
    WebEvent.mod_shift, WebEvent.mod_ctrl, WebEvent.mod_alt, WebEvent.mod_meta,
    HandlerResult.msg, HandlerResult.ignore, HandlerResult.prevent, HandlerResult.map,
}

pub use lib::websocket {WsData, WsEvent, WsData.text_of, WsData.bytes_of}

// The sound-effect and media-transport vocabulary: pure DATA an `update`
// returns (`Command.sound`/`Command.media`), with no handle and no IO.
pub use lib::sound {
    SoundFx, MediaCmd, Wave, SoundFx.is_silence, Wave.code,
}
