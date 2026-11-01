/// The agent-generated session title: after a session's first turn (or
/// after a plan lands) one small model call turns the opening exchange
/// into a short name and a one-line description for `/resume`. The
/// derived first-message title stays the fallback whenever this fails,
/// and `/name`/`/describe` still win (the caller only writes fields that
/// still hold the derived value).
///
/// The call reuses shuttle's loop with an EMPTY tool registry and a
/// one-call budget: no tools, no gate, no session state.
use shuttle::loop {Loop.run}
use shuttle::registry {ToolRegistry}
use shuttle::gate {Gate}
use shuttle::session {Session}
use shuttle::provider {ProviderConfig}
use shuttle::message {Message}
use shuttle::message_types {Role, Content}
use init::transformers {ResultT}
use std::list {List.filter}
use weaver::text {Text.cut, Text.first_line}
use weaver::theme {theme_split_lines}

pub def Title.max_name : I64 := 60
pub def Title.max_description : I64 := 160

/// One request/answer pair is all the title needs; more is cost.
pub def Title.max_input : I64 := 2000

pub def Title.max_reply_tokens : I64 := 256

pub def Title.system_prompt : String :=
    "You name coding-agent sessions for a session picker. Reply with exactly two lines and nothing else:\nname: <3 to 6 words, no quotes>\ndescription: <one sentence, at most 20 words>"

/// Should this turn ask for a title? The first completed turn, or any
/// turn that produced a plan -- skipped offline (the mock wire would
/// consume a scripted turn) and for unsaved sessions.
pub def Title.needed (has_store : Bool) (mock_wire : Bool) (turns : I64) (plan : Bool) : Bool :=
    if Bool.not has_store then false
    else if mock_wire then false
    else if plan then true
    else turns == 1

pub def Title.user_prompt (request : String) (answer : String) : String :=
    let r : String := Text.cut Title.max_input (String.trim request) in
    let a : String := Text.cut Title.max_input (String.trim answer) in
    String.concat "First request from the user:\n" (String.concat r
        (String.concat "\n\nWhat the assistant did (or the plan it wrote):\n" a))

// ── parsing the reply ──────────────────────────────────────────────────

/// Strip one matching pair of surrounding quotes or backticks.
def unquote (s : String) : String :=
    let n : I64 := String.length s in
    if I64.lt n 2 then s
    else
        let first : String := String.slice s 0 1 in
        let last : String := String.slice s (n - 1) 1 in
        if Bool.and (first == last)
            (Bool.or (first == "\"") (Bool.or (first == "`") (first == "'")))
        then String.trim (String.slice s 1 (n - 2))
        else s

/// One line as a title field: one line, trimmed, unquoted, byte-capped
/// (UTF-8 safe).
def clean (max : I64) (s : String) : String :=
    let t : String := unquote (String.trim (Text.first_line s)) in
    Text.cut max t

#[partial]
def labelled_go (p : String) (lines : List String) (acc : Option String) : Option String :=
    match lines {
        List.empty => acc,
        List.cons l rest =>
            if String.starts_with p l
            then labelled_go p rest (Option.some (String.trim (String.drop (String.length p) l)))
            else labelled_go p rest acc,
    }

/// The first line carrying `p` (last wins, so a model that repeats the
/// label still ends on its final answer), without the label.
def labelled (p : String) (lines : List String) : Option String :=
    labelled_go p lines Option.none

def name_line (lines : List String) : Option String :=
    match labelled "name:" lines {
        Option.some s => Option.some s,
        Option.none => labelled "Name:" lines,
    }

def desc_line (lines : List String) : Option String :=
    match labelled "description:" lines {
        Option.some s => Option.some s,
        Option.none => labelled "Description:" lines,
    }

/// A bullet/heading marker off a free-form line.
#[partial]
def drop_markers_go (s : String) (n : I64) : String :=
    if I64.gt n 8 then s
    else
        let c : String := String.slice s 0 1 in
        if Bool.or (c == "-") (Bool.or (c == "*") (Bool.or (c == "#") (Bool.or (c == "`") (c == " "))))
        then drop_markers_go (String.drop 1 s) (n + 1)
        else s

def free_line (s : String) : String :=
    drop_markers_go (String.trim s) 0

/// No labels at all: the first two non-empty lines are the name and the
/// description.
def free_pair (lines : List String) : Option (Pair String String) :=
    match lines {
        List.empty => Option.none,
        List.cons a rest =>
            let name : String := clean Title.max_name (free_line a) in
            if String.is_empty name then Option.none
            else match rest {
                List.empty => Option.some (Pair.pair name ""),
                List.cons b _ => Option.some (Pair.pair name (clean Title.max_description (free_line b))),
            },
    }

/// A reply's name/description pair, or none when there is no usable
/// name. A missing description is "" -- the caller keeps the derived
/// one.
pub def Title.parse (reply : String) : Option (Pair String String) :=
    let lines : List String := List.filter (fn (l : String) => Bool.not (String.is_empty l))
        (List.map String.trim (theme_split_lines reply)) in
    match name_line lines {
        Option.some raw =>
            let name : String := clean Title.max_name raw in
            let desc : String := match desc_line lines {
                Option.some d => clean Title.max_description d,
                Option.none => "",
            } in
            if String.is_empty name then Option.none else Option.some (Pair.pair name desc),
        Option.none => free_pair lines,
    }

// ── the call ───────────────────────────────────────────────────────────

#[partial]
def texts_of (cs : List Content) (acc : String) : String :=
    match cs {
        List.empty => acc,
        List.cons c rest =>
            match c {
                Content.text s => texts_of rest (String.concat acc s),
                _ => texts_of rest acc,
            },
    }

#[partial]
def last_assistant_go (ms : List Message) (acc : Option String) : Option String :=
    match ms {
        List.empty => acc,
        List.cons m rest =>
            let next : Option String := match m.role {
                Role.assistant => Option.some (texts_of m.content ""),
                _ => acc,
            } in
            last_assistant_go rest next,
    }

pub def Title.last_text (s : Session) : String :=
    match last_assistant_go s.history Option.none {
        Option.none => "",
        Option.some t => t,
    }

def user_message (text : String) : Message :=
    { role := Role.user, content := List.cons (Content.text text) List.empty }

pub def Title.silent_emit (frag : String) : IO Unit := IO.pure unit

/// One model call, no tools. `none` on any provider/parse failure: a
/// missing title is a cosmetic miss, never a turn failure.
pub def Title.generate (cfg : ProviderConfig) (request : String) (answer : String) : IO (Option (Pair String String)) := do {
    let hist : List Message := List.cons (user_message (Title.user_prompt request answer)) List.empty;
    let cfg2 : ProviderConfig := { cfg with max_tokens := Title.max_reply_tokens, thinking := false };
    let r <- ResultT.run (Loop.run cfg2 ToolRegistry.empty Title.system_prompt hist 1 Title.silent_emit Gate.auto);
    match r {
        Result.err _ => IO.pure Option.none,
        Result.ok s => IO.pure (Title.parse (Title.last_text s)),
    }
}
