/// The roadmap PR 2 app gate on its own: a 100-tool auto turn must not grow
/// RSS by the old ~21 MB per tool call. Run with the pty harness:
/// `WEAVER_PTY=1 WEAVER_PTY_REQUIRED=1 WV_BIN=<weaver> monad test <this>`.
use weaver::pty::rss {run_a_100_tool_turn_stays_bounded}

#[test]
def test_a_100_tool_turn_stays_bounded : IO Bool := run_a_100_tool_turn_stays_bounded
