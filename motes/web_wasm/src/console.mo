/// `console.log`, for diagnostics from browser code.

use lib::ffi {console_log_raw}

pub def Console.log (s : String) : IO Unit := IO.mk (console_log_raw s)
