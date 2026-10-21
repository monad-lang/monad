# Subagents: design and roadmap

The v1 shipped now is a **read-only plan subagent**: the model can call
`task {prompt, max_turns}` and a child `Loop.run_state` investigates with
`read`/`grep`/`glob` under `Gate.read_only`, then returns its last
assistant message plus a usage footer. The child is synchronous (inside
the parent's tool dispatch), depth 1 (its registry has no `task`), and
its usage is logged/reported but not added to the parent's
`session.spent`. This document is the roadmap beyond that.

## Why it is small

`shuttle::loop` is already reusable: `Loop.initial_state` builds a
`RunState` (session, registry, budget, emit, gate, on_usage) and
`Loop.run_state` drives it to a final `Session`. A tool is
`String -> Json -> ResultT String IO Content`, so a tool can run a child
loop without changing the harness. Weaver rebuilds its registry each turn
(`drive_tui`/`drive`) to add `Subagent.task_tool cfg log store`; that is
how the child sees the **current** provider/model and the run's store.

## Child lifecycle

- `Session` = parent `ProviderConfig`, child system prompt, child history
  seeded with one user prompt, empty `spent`, zero turns.
- Registry = read-side tools only. No `write`/`edit`/`shell`/`task`.
- Gate = `Gate.read_only` (precheck denies non-read even for a cached
  pick).
- Budget = `max_turns`, clamped 1-20 (default 8). No wall-clock timeout:
  the harness has no cancellation primitive.
- Persistence (v1): `Session.save` under `<session>/agents/<pid>-<ns>.json`;
  a future `/agents` can list these.
- Result = child's last assistant text + `[subagent turns=… tokens …]`.

## Planned phases

1. **Plan-first execution (next).** Keep the read-only child, but let the
   parent request an **execute** phase after the user approves the plan.
   Two child runs (plan, then execute) or one run whose gate is swapped;
   the plan text is the contract. Execute-phase approvals reuse the
   parent's dialog through the existing `Gate.weaver_tui`.
2. **`/agents` monitor.** A list of child runs with status, elapsed,
   last emit line and token totals (the debug log already records
   `subagent_start/end/usage`; persisted sessions give the plan text).
   Model it on the `/processes` snapshot first, then a live overlay once
   the modal renderer is fixed.
3. **Background children.** Run the child on a fiber so the parent turn
   does not block, and poll it with `pollFiber`. This needs a
   fiber-to-model progress channel: today `Cmd.perform_async` delivers
   one message at completion, and there is no mvar/channel in `std`.
4. **Approval forwarding.** A background child's `ask` cannot open the
   parent's modal (stdin is serial). Either deny non-read picks with a
   clear reason (v1), surface a queue after the parent turn, or give the
   child a fixed capability (read-only / allow_edit). Document the choice
   in the UI.
5. **Parallel children.** `forkIO`/`pollFiber` and the TUI's fiber list
   already support several handles; the missing pieces are the progress
   channel, per-child emit attribution, and a budget/cancellation story.
6. **Nesting.** Depth 1 now. Depth N needs a budget tree and a
   cancellation sentinel checked in the child `emit`.

## Constraints and risks

- **Accounting:** child usage should eventually be added to the parent
  `session.spent`; today only the footer/log carries it.
- **Cancellation:** nothing can interrupt a running `ResultT`/IO action
  coherently. `cancel_fiber` exists but a blocked provider/tool read
  cannot be unwound. Bound every child by `turns_left`.
- **Security:** the child never broadens capabilities, inherits no
  `always` cache, runs with the parent's environment/keys, and its output
  is untrusted input to the parent prompt (cap the summary length).
- **Prompt injection:** a child plan is text; never treat it as an
  instruction to the parent outside the normal model loop.
- **Store:** child sessions hold the same data class as the parent; no
  key material, and `/save`/resume semantics must be defined before
  exposing `/agents`.
