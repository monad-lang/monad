/// Page navigation. Both are synchronous; `reload`/`navigate` may unload
/// the page, so persist state first.

use lib::ffi {window_reload_raw, window_navigate_raw}

pub def Window.reload : IO Unit := IO.mk window_reload_raw

pub def Window.navigate (url : String) : IO Unit := IO.mk (window_navigate_raw url)
