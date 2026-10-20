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
    let g : Gate := { ask := weaver_ask mode read write, precheck := weaver_precheck mode write } in
    g

/// The policy half runs on EVERY pick, cached capability or not: an `a`
/// in manual mode must not let a later plan mode run writes. A refusal
/// is also visible to the human (the line-based UI would otherwise stay
/// silent about why nothing ran).
def weaver_precheck (mode : Mode) (write : String -> IO Unit) (p : Pick) : IO (Option Approval) :=
    match Policy.decide p.cap mode {
        Decision.refuse reason => do {
            let _ <- write (String.concat "refused: " (String.concat reason "\n"));
            IO.pure (Option.some (Approval.deny reason))
        },
        _ => IO.pure Option.none,
    }

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
    ask_again read write p 1
}

/// Ask once; an unrecognized answer re-prompts once (a typo must not
/// silently deny). A trailing text after `y`/`a`/`n` is the note: the
/// model sees it on the tool result, or as the denial's reason.
#[partial]
def ask_again (read : Unit -> IO (Option String)) (write : String -> IO Unit) (p : Pick) (tries : I64) : IO Approval := do {
    let _ <- write (gate_answer_prompt p.cap);
    let line <- read unit;
    match line {
        Option.none => do {
            let ap : Approval := Approval.deny "declined by user (eof)";
            let _ <- write (String.concat (gate_answer_feedback p.cap ap) "\n");
            return ap
        },
        Option.some s => match answer_line (String.trim s) {
            Option.none =>
                if tries < 2 then do {
                    let _ <- write "answer y, a or n (an optional note follows the letter)\n";
                    ask_again read write p (tries + 1)
                } else do {
                    let ap : Approval := Approval.deny "declined by user";
                    let _ <- write (String.concat (gate_answer_feedback p.cap ap) "\n");
                    return ap
                },
            Option.some ap => do {
                let _ <- write (String.concat (gate_answer_feedback p.cap ap) "\n");
                return ap
            },
        },
    }
}

#[terminating]
def answer_split (s : String) (i : I64) : Option I64 :=
    if Bool.not (i < String.length s) then Option.none
    else if String.slice s i 1 == " " then Option.some i
    else answer_split s (i + 1)

/// The answer's word and its optional note.
def answer_line (s : String) : Option Approval :=
    match answer_split s 0 {
        Option.none => answer_word_note s "",
        Option.some sp =>
            let word : String := String.slice s 0 sp in
            let note : String := String.trim (String.drop (sp + 1) s) in
            answer_word_note word note,
    }

/// The answer line, both UIs' shared prompt. The `a` semantics used to
/// be undocumented -- "grant read access to a whole repo" is exactly
/// what `always` does (cached per capability for the whole session,
/// `RunState.always`) -- so the prompt names it.
pub def gate_answer_prompt (cap : Capability) : String :=
    String.concat "[y] once  [n] deny  [a] = all "
        (String.concat (cap_name cap) "s this session: ")

/// What the gate echoes back once the answer lands. One piece of
/// immediate feedback: answering USED to show nothing for the whole
/// rest of the turn, so under a slow provider the prompt looked dead
/// (the recorded UI-repair finding).
pub def gate_answer_feedback (cap : Capability) (ap : Approval) : String :=
    match ap {
        Approval.once => "y -- approved",
        Approval.once_note _ => "y -- approved (note added to the tool result)",
        Approval.always => String.concat "a -- all "
            (String.concat (cap_name cap) "s approved for this session"),
        Approval.always_note _ => String.concat "a -- all "
            (String.concat (cap_name cap) "s approved for this session (note added)"),
        Approval.deny reason =>
            String.concat "n -- denied (" (String.concat reason ")"),
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

def answer_word_note (s : String) (note : String) : Option Approval :=
    if s == "y"
    then (if String.is_empty note then Option.some Approval.once else Option.some (Approval.once_note note))
    else if s == "a"
    then (if String.is_empty note then Option.some Approval.always else Option.some (Approval.always_note note))
    else if Bool.or (s == "n") (String.is_empty s)
    then Option.some (Approval.deny (if String.is_empty note then "declined by user" else note))
    else Option.none
