// web_event's library root -- bare `use web_event` resolves here.

pub use lib::event {
    WebEvent, FileInfo, ListenerFlags, HandlerResult,
    ListenerFlags.none, ListenerFlags.letters, ListenerFlags.encode,
    WebEvent.mod_shift, WebEvent.mod_ctrl, WebEvent.mod_alt, WebEvent.mod_meta,
    HandlerResult.msg, HandlerResult.ignore, HandlerResult.prevent,
}
