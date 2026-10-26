/// Drift guard for constants the Monad side and `wasm/web/web_runtime.js`
/// must agree on: the event attribute prefix and the listener flag letters.
///
/// Runs from the repository root (where both `monad test` and the Rust host
/// run tests).

use web_event::event {ListenerFlags}
use oak::typed {Handler.prefix}

#[test]
def test_event_prefix_matches_host : IO Bool := do {
  let expected : String := String.concat "const EVENT_PREFIX = '" (String.concat Handler.prefix "';");
  matches_host expected
}

#[test]
def test_listener_flags_match_host : IO Bool := do {
  let expected : String := String.concat "const EVENT_FLAGS = '" (String.concat ListenerFlags.letters "';");
  matches_host expected
}

def matches_host (line : String) : IO Bool := do {
  let r <- IO.read_file (Path.path "wasm/web/web_runtime.js");
  match r {
    Result.err _ => return false,
    Result.ok text => return (String.contains text line)
  }
}
