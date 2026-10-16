/// Weaver's interactive gate -- weaver.md Phase 3's dumb-mode half: the
/// `Gate` shuttle's loop consults (shuttle `gate.mo`'s seam),
/// implemented as "ask the human". The MODE decides first (policy.mo's
/// table): `allow` proceeds without a word, `refuse` denies with the
/// table's reason, `ask` prints the pick and reads `y`/`n`/`a`.
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
        Decision.refuse reason => IO.pure (Approval.deny reason),
    }

/// The `ask` cell: print the pick (name, capability, input summary),
/// read one word. EOF during an approval is a denial, not an approval
/// -- a closed stdin must never green-light a mutation.
def prompt_pick (read : Unit -> IO (Option String)) (write : String -> IO Unit) (p : Pick) : IO Approval := do {
    let _ <- write (pick_prompt p);
    let line <- read unit;
    answer_of line
}

/// One line: `[approve] write stamp {...} [y/n/a]: ` -- the model's
/// input JSON is the whole contract, truncated only so a huge pick
/// cannot bury the prompt.
def pick_prompt (p : Pick) : String :=
    String.concat "[approve] "
        (String.concat (cap_name p.cap)
        (String.concat " "
        (String.concat p.name
        (String.concat " "
        (String.concat (summarize p.input) " [y/n/a]: ")))))

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
