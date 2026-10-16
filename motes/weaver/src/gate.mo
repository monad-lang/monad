/// Weaver's interactive gate -- weaver.md Phase 3's dumb-mode half: the
/// `Gate` shuttle's loop consults (shuttle `gate.mo`'s seam),
/// implemented as "ask the human". The MODE decides first (policy.mo's
/// table): `allow` proceeds without a word, `refuse` denies with the
/// table's reason (printed inline, Phase 5), `ask` prints the pick --
/// with the old -> new diff for `write`/`edit` picks -- and reads
/// `y`/`n`/`a`.
///
/// The `a` answer is `Approval.always`, which the LOOP caches per
/// capability in `RunState.always` (shuttle's Elm state -- there is no
/// `IORef`), so later picks of the same capability never reach this
/// gate. Per-session by construction: the cache is never serialized.
///
/// The read/write seams are injected, not `IO.read_line`/stdout
/// directly: the dumb loop passes its own pair, and the e2e passes a
/// scripted pair -- the gate is testable without a tty, the same
/// discipline as the mock wire.
use shuttle::gate {Capability, Pick, Approval, Gate}
use weaver::policy {Mode, Decision, Policy.decide}
use weaver::diff {Diff.for_input, Diff.render}
use json::json {Json, Json.to_string}

/// The display name of a capability, in prompts and `/tools`.
pub def cap_name (c : Capability) : String :=
    match c {
        Capability.read => "read",
        Capability.write => "write",
        Capability.exec => "exec",
        Capability.net => "net",
    }

/// The gate for one mode. Rebuilt by the dumb loop whenever the mode
/// changes -- the gate closes over the mode it was built with, so a
/// stale gate would enforce a stale policy.
///
/// The read seam is `Unit -> IO (Option String)`, not a naked
/// `IO (Option String)`: a naked IO value is performed once, at the
/// point it is passed (the compiled backend's `RawIO.io` is a strict
/// box), so every approval would read the SAME line. The function form
/// re-reads per ask.
pub def Gate.weaver (mode : Mode) (read : Unit -> IO (Option String)) (write : String -> IO Unit) : Gate :=
    let g : Gate := { ask := weaver_ask mode read write } in
    g

def weaver_ask (mode : Mode) (read : Unit -> IO (Option String)) (write : String -> IO Unit) (p : Pick) : IO Approval :=
    match Policy.decide p.cap mode {
        Decision.allow => IO.pure Approval.once,
        Decision.ask => prompt_pick read write p,
        Decision.refuse reason => refused write reason,
    }

/// A policy refusal is visible to the HUMAN too, not only to the
/// model: the loop turns the denial into a tool_result the model
/// reads, but the terminal would otherwise stay silent about WHY
/// nothing ran -- the plan-mode inline reason (weaver.md Phase 5).
def refused (write : String -> IO Unit) (reason : String) : IO Approval := do {
    let _ <- write (String.concat "refused: " (String.concat reason "\n"));
    IO.pure (Approval.deny reason)
}

/// The `ask` cell: print the pick (name, capability, input summary,
/// and for file mutations the old -> new diff), read one word. EOF
/// during an approval is a denial, not an approval -- a closed stdin
/// must never green-light a mutation.
def prompt_pick (read : Unit -> IO (Option String)) (write : String -> IO Unit) (p : Pick) : IO Approval := do {
    let _ <- write (pick_header p);
    let r <- Diff.for_input p.name p.input;
    let _ <- write_diff write r;
    let _ <- write "[y/n/a]: ";
    let line <- read unit;
    answer_of line
}

/// One line: `[approve] write edit {...}` -- for a `write`/`edit`
/// pick the diff block follows on its own lines, then the answer
/// prompt. The model's input JSON is the whole contract, truncated
/// only so a huge pick cannot bury the prompt.
def pick_header (p : Pick) : String :=
    String.concat "[approve] "
        (String.concat (cap_name p.cap)
        (String.concat " "
        (String.concat p.name
        (String.concat " "
        (String.concat (summarize p.input) " ")))))

/// The diff block: a blank line, the capped render, a blank line.
/// `(no changes)` covers an edit whose two sides are identical --
/// the human must still see that there is nothing to approve.
def write_diff (write : String -> IO Unit) (r : Option (Pair String String)) : IO Unit :=
    match r {
        Option.none => IO.pure unit,
        Option.some pr => match pr {
            Pair.pair old new => write (String.concat "\n" (String.concat (capped_diff old new) "\n")),
        },
    }

/// The same display-only truncation discipline as `summarize`: a
/// huge write must not bury the terminal in a diff.
def capped_diff (old : String) (new : String) : String :=
    let d : String := Diff.render old new in
    if String.is_empty d
    then "(no changes)"
    else if String.length d > 1200
    then String.concat (String.slice d 0 1200) "\n... (diff truncated)"
    else d

/// The first 200 bytes of the input's JSON -- byte-slicing is safe
/// here for the same reason it is in prompts: a truncated render is
/// display, not data.
def summarize (input : Json) : String :=
    let s := Json.to_string input in
    if String.length s > 200
    then String.concat (String.slice s 0 200) "..."
    else s

def answer_of (line : Option String) : IO Approval :=
    match line {
        Option.none => IO.pure (Approval.deny "declined by user (eof)"),
        Option.some s => answer_word (String.trim s),
    }

def answer_word (s : String) : IO Approval :=
    if s == "y" then IO.pure Approval.once
    else if s == "a" then IO.pure Approval.always
    else IO.pure (Approval.deny "declined by user")
