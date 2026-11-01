# The weaver TUI pty repro

The pty drivers now live in `motes/weaver/test/` and run under `monad test`
(the harness is `motes/mty`, documented in `motes/mty/README.md`; the
fixtures are in `motes/weaver/test/fixtures/`). `scripts/ci-weaver-pty.sh`
runs that suite against a release weaver built from the same commit.

## The remaining Python driver

`pty_repro_sessions.py` is the last one. Its S1–S5 scenarios are covered by
`motes/weaver/test/sessions_tests.mo`; **S6** (an 18 MB session with a
startup-RSS bound and flat idle growth) is not ported yet. Resuming that
session SIGSEGVs the compiled test driver in a runtime fiber thread
(`GC_inner_start_routine -> monad_get_tag`), whether the session is
synthesized in-process or by a separate process. Until that runtime bug is
fixed, this driver stays the CI oracle for S6. It generates its own turn
fixtures and session stores under a pid-qualified temp root, so nothing here
is shared with the Monad suite.

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
