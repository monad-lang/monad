# The weaver TUI pty repros

The pty drivers live in `motes/weaver/test/` and run under `monad test`
(the harness is `motes/pty`, documented in `motes/pty/README.md`; the
fixtures are in `motes/weaver/test/fixtures/`). `scripts/ci-weaver-pty.sh`
builds a release weaver from the same commit and runs that suite. The last
Python driver (`pty_repro_sessions.py`, including the 18 MB RSS scenario)
has been ported and deleted.

## Parser probes (`probes/`)

Ten-line repros for the three compiler findings recorded in the
UI-repair changelog; `monad check <probe>` shows each:

- `comment_after_assign.mo` -- a `--` comment line directly after
  `:=` breaks the parse (the def's body does not parse; the error
  reports misleading "remaining text" positions).
- `expr_project_bind_looser.mo` -- `(expr).field == rhs` parses as
  `(. expr) (field == rhs)`: the projection binds looser than `==`.
  Bind the expression to a `let` first.
- `over_application.mo` -- a two-arg def called with three arguments
  checks clean on both hosts and crashes at runtime.
