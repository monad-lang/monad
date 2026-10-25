/// Weaver's interactive gate -- weaver.md Phase 3's dumb-mode half: the
/// `Gate` shuttle's loop consults (shuttle `gate.mo`'s seam),
/// implemented as "ask the human". The MODE decides first (policy.mo's
/// table): `allow` proceeds without a word, `refuse` denies with the
/// table's reason (printed inline, Phase 5), `ask` either matches a
/// session grant or prints the pick -- with the old -> new diff for
/// `write`/`edit` picks -- and reads `y`/`r`/`n`/`a`.
///
/// The grant list is WEAVER's (a `Ref (List PermGrant)`), not shuttle's
/// `RunState.always`: grants carry a scope (`repo` = the pick's target
/// is inside the workspace root, `anywhere` = the whole capability), and
/// `/permissions` can inspect and clear them, which the loop's cache
/// cannot. The gate never returns `Approval.always`; it records the
/// grant and returns `once`, and `precheck` re-checks the policy before
/// every pick so a grant can never bypass plan mode.
///
/// The read/write seams are injected, not `IO.read_line`/stdout
/// directly: the dumb loop passes its own pair, and the e2e passes a
/// scripted pair -- the gate is testable without a tty, the same
/// discipline as the mock wire.
use shuttle::gate {Capability, Pick, Approval, Gate}
use weaver::policy {Mode, Decision, Policy.decide}
use weaver::diff {Diff.for_input, Diff.render}
use weaver::permissions {
    PermGrant, PermScope, Permissions.matches, Permissions.pick_in_repo, Permissions.get,
    Permissions.add,
}
use std::ref {Ref}
use json::json {Json, Json.to_string}

/// What one user answer to a prompt means. `here` records a repo-scoped
/// grant (only offered when the pick's target is inside the workspace
/// root); `any` is the old "all <cap>s this session". Both run the pick
/// now by returning `Approval.once` -- weaver owns the grant list, so
/// shuttle's per-capability `always` cache is never used.
pub type PickAnswer {
    pick_once,
    pick_here,
    pick_any,
    pick_deny (reason : String),
}

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
pub def Gate.weaver (mode : Mode) (grants : Option (Ref (List PermGrant))) (root : Option String) (read : Unit -> IO (Option String)) (write : String -> IO Unit) : Gate :=
    let g : Gate := {
        ask := weaver_ask mode grants root read write,
        precheck := weaver_precheck mode grants root write,
    } in
    g

/// The policy half runs on EVERY pick, cached capability or not: a grant
/// in manual mode must not let a later plan mode run writes, and a
/// repo-scoped grant must not cover a pick outside the root. A refusal
/// is also visible to the human (the line-based UI would otherwise stay
/// silent about why nothing ran).
def weaver_precheck (mode : Mode) (grants : Option (Ref (List PermGrant))) (root : Option String) (write : String -> IO Unit) (p : Pick) : IO (Option Approval) :=
    match Policy.decide p.cap mode {
        Decision.refuse reason => do {
            let _ <- write (String.concat "refused: " (String.concat reason "\n"));
            IO.pure (Option.some (Approval.deny reason))
        },
        Decision.ask => do {
            let gs <- Permissions.get grants;
            if Permissions.matches root gs p.cap (pick_target p)
            then IO.pure (Option.some Approval.once)
            else IO.pure Option.none
        },
        Decision.allow => IO.pure Option.none,
    }

def weaver_ask (mode : Mode) (grants : Option (Ref (List PermGrant))) (root : Option String) (read : Unit -> IO (Option String)) (write : String -> IO Unit) (p : Pick) : IO Approval :=
    match Policy.decide p.cap mode {
        Decision.allow => IO.pure Approval.once,
        Decision.ask => prompt_pick grants root read write p,
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
def prompt_pick (grants : Option (Ref (List PermGrant))) (root : Option String) (read : Unit -> IO (Option String)) (write : String -> IO Unit) (p : Pick) : IO Approval := do {
    let _ <- write (pick_header p);
    let r <- Diff.for_input p.name p.input;
    let _ <- write_diff write r;
    let repo_ok : Bool := Permissions.pick_in_repo root (pick_target p);
    ask_again grants root repo_ok read write p 1
}

/// Ask once; an unrecognized answer re-prompts once (a typo must not
/// silently deny). A trailing text after the letter is the note: the
/// model sees it on the tool result, or as the denial's reason.
#[partial]
def ask_again (grants : Option (Ref (List PermGrant))) (root : Option String) (repo_ok : Bool) (read : Unit -> IO (Option String)) (write : String -> IO Unit) (p : Pick) (tries : I64) : IO Approval := do {
    let _ <- write (gate_answer_prompt p.cap repo_ok);
    let line <- read unit;
    match line {
        Option.none => do {
            let ap : Approval := Approval.deny "declined by user (eof)";
            let _ <- write (String.concat (gate_answer_feedback p.cap (PickAnswer.pick_deny "declined by user (eof)")) "\n");
            return ap
        },
        Option.some s => match answer_line repo_ok (String.trim s) {
            Option.none =>
                if tries < 2 then do {
                    let _ <- write (gate_answer_help repo_ok);
                    ask_again grants root repo_ok read write p (tries + 1)
                } else do {
                    let ap : Approval := Approval.deny "declined by user";
                    let _ <- write (String.concat (gate_answer_feedback p.cap (PickAnswer.pick_deny "declined by user")) "\n");
                    return ap
                },
            Option.some pr => do {
                let ans : PickAnswer := pair_first pr;
                let note : String := pair_second pr;
                let _ <- record_answer grants p ans;
                let ap : Approval := answer_approval ans note;
                let _ <- write (String.concat (gate_answer_feedback p.cap ans) "\n");
                return ap
            },
        },
    }
}

def pair_first (p : Pair PickAnswer String) : PickAnswer :=
    match p { Pair.pair a _ => a }

def pair_second (p : Pair PickAnswer String) : String :=
    match p { Pair.pair _ s => s }

/// A `here`/`any` answer extends the session grant list; `once` and
/// `deny` change nothing.
pub def record_answer (grants : Option (Ref (List PermGrant))) (p : Pick) (ans : PickAnswer) : IO Unit :=
    match ans {
        PickAnswer.pick_here =>
            let g : PermGrant := { cap := p.cap, scope := PermScope.repo } in
            Permissions.add grants g,
        PickAnswer.pick_any =>
            let g : PermGrant := { cap := p.cap, scope := PermScope.anywhere } in
            Permissions.add grants g,
        _ => IO.pure unit,
    }

/// Every approval runs THIS pick by returning `once`; the grant, when
/// one was recorded, is consulted by `precheck` on later picks.
pub def answer_approval (ans : PickAnswer) (note : String) : Approval :=
    match ans {
        PickAnswer.pick_deny reason =>
            Approval.deny (if String.is_empty note then reason else note),
        _ =>
            if String.is_empty note then Approval.once else Approval.once_note note,
    }

#[terminating]
def answer_split (s : String) (i : I64) : Option I64 :=
    if Bool.not (i < String.length s) then Option.none
    else if String.slice s i 1 == " " then Option.some i
    else answer_split s (i + 1)

/// The answer's word and its optional note. `r` is accepted only when a
/// repo scope was offered (a path-bearing pick inside the root).
pub def answer_line (repo_ok : Bool) (s : String) : Option (Pair PickAnswer String) :=
    match answer_split s 0 {
        Option.none => answer_word_note repo_ok s "",
        Option.some sp =>
            let word : String := String.slice s 0 sp in
            let note : String := String.trim (String.drop (sp + 1) s) in
            answer_word_note repo_ok word note,
    }

/// The answer line, both UIs' shared prompt. The `a` semantics used to
/// be undocumented -- "grant read access to a whole repo" is exactly
/// what `always` does (cached per capability for the whole session,
/// `RunState.always`) -- so the prompt names it.
pub def gate_answer_prompt (cap : Capability) (repo_ok : Bool) : String :=
    let repo_hint : String := if repo_ok
        then String.concat "[r] all " (String.concat (cap_name cap) "s in this repo  ")
        else "" in
    String.concat "[y] once  "
        (String.concat repo_hint
            (String.concat "[n] deny  [a] all "
                (String.concat (cap_name cap) "s (anywhere) this session: ")))

pub def gate_answer_help (repo_ok : Bool) : String :=
    if repo_ok
    then "answer y, r, a or n (an optional note follows the letter)\n"
    else "answer y, a or n (an optional note follows the letter)\n"

/// What the gate echoes back once the answer lands. One piece of
/// immediate feedback: answering USED to show nothing for the whole
/// rest of the turn, so under a slow provider the prompt looked dead
/// (the recorded UI-repair finding). It names the SCOPE that was
/// granted -- "all reads" and "all reads in this repo" are different
/// promises.
pub def gate_answer_feedback (cap : Capability) (ans : PickAnswer) : String :=
    match ans {
        PickAnswer.pick_once => "y -- approved",
        PickAnswer.pick_here => String.concat "r -- all "
            (String.concat (cap_name cap) "s under the workspace root approved for this session"),
        PickAnswer.pick_any => String.concat "a -- all "
            (String.concat (cap_name cap) "s approved anywhere for this session"),
        PickAnswer.pick_deny reason =>
            String.concat "n -- denied (" (String.concat reason ")"),
    }

/// The `path` a pick's input names (`write`, `edit`, `read`), when it
/// has one: the dialog must say WHICH file is about to change.
pub def pick_target (p : Pick) : Option String :=
    match Json.get_object p.input {
        Result.err _ => Option.none,
        Result.ok obj => match Json.object_get "path" obj {
            Option.none => Option.none,
            Option.some j => match Json.get_str j {
                Result.ok path => Option.some path,
                Result.err _ => Option.none,
            },
        },
    }

/// One line: `[approve] write write -> /path`, or the input JSON when
/// the tool names no path. For a `write`/`edit` pick the diff block
/// follows on its own lines, then the answer prompt. The model's input
/// JSON is the whole contract, truncated only so a huge pick cannot
/// bury the prompt.
def pick_header (p : Pick) : String :=
    let base : String := String.concat "[approve] "
        (String.concat (cap_name p.cap) (String.concat " " p.name)) in
    match pick_target p {
        Option.some path => String.concat base (String.concat " -> " path),
        Option.none => String.concat base (String.concat " " (String.concat (summarize p.input) " ")),
    }

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

def answer_word_note (repo_ok : Bool) (word : String) (note : String) : Option (Pair PickAnswer String) :=
    let ans : Option PickAnswer :=
        if word == "y"
        then Option.some PickAnswer.pick_once
        else if word == "r"
        then (if repo_ok then Option.some PickAnswer.pick_here else Option.none)
        else if word == "a"
        then Option.some PickAnswer.pick_any
        else if Bool.or (word == "n") (String.is_empty word)
        then Option.some (PickAnswer.pick_deny (if String.is_empty note then "declined by user" else note))
        else Option.none in
    match ans {
        Option.none => Option.none,
        Option.some a => Option.some (Pair.pair a note),
    }
