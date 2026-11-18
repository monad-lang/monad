/// Resume-time context folding: the pure half of "do not re-upload the whole
/// session when a run restarts".
///
/// A resume hands `Store.load_session` EVERY committed history block
/// (`load_history_seq` walks `history_base` .. `history_next-1`), and
/// `set_session` zeroes `last_context`, so the first resumed turn pays the
/// whole session -- possibly twice, since autocompact's own prompt
/// re-renders that same history. `Fold` replaces the older prefix with ONE
/// system digest and keeps the newest tail verbatim.
///
/// Three properties, all load-bearing:
///
/// 1. **No provider call.** A resume must not block on the network and must
///    not cost tokens to *start*; the digest is built from the messages.
///    (`Compact.compact` is the summarizer; this is not it.)
/// 2. **Nothing is lost from reach.** The dropped turns stay on disk, and
///    the digest names the session's own history directory so the model can
///    read them back with the read tool. They leave the DEFAULT context,
///    not the session.
/// 3. **A session under the budget is not touched at all**, so a short
///    resume replays byte-for-byte.
///
/// The cut is `Compact.keep_tail`'s, so the kept tail begins at a user
/// message or is empty -- never an orphan tool result, never the second half
/// of a tool_use/tool_result pair (both wires reject those).
///
/// History stays append-only: the fold is committed through
/// `Store.record_compacted` (one block + a moved `history_base`), never
/// applied as a turn delta.
use shuttle::message {Message}
use shuttle::message_types {Role, Content}
use shuttle::session {Session}
use shuttle::context {history_tokens}
use weaver::compact {Compact.Outcome, Compact.estimate, Compact.keep_budget, Compact.keep_tail, Compact.threshold}
use weaver::text {Text.cut, Text.first_line}
use std::path {Path, Path.to_string}
use std::list {List.intercalate}

/// The most of one text block the digest quotes. The digest is a summary of
/// what happened, not a second copy of it.
pub def Fold.line_max : I64 := 160

/// The tail budget: the same share of the window compaction keeps, so a
/// folded resume and a compacted session leave the model the same room.
/// `0` when autocompact itself is off -- a zero window, or `compact_at = 0`
/// -- because the fold's off switch IS autocompact's: a resume must never be
/// what turns a deliberately disabled context window back on.
/// `Compact.keep_budget` floors at 1 token to guard its own division, so the
/// threshold is tested here rather than left to that floor.
pub def Fold.tail_budget (window : I64) (compact_at : I64) : I64 :=
    let t : I64 := Compact.threshold window compact_at in
    if t < 1i64 then 0i64 else Compact.keep_budget t

/// The tail budget a resume actually uses: the explicit `resume_fold`
/// setting when it spoke, else the window-derived default. `0` (either
/// spelling) disables folding -- and a window of 0 or a `compact_at` of
/// 0 keeps it off too, so a resume never re-enables a deliberately
/// disabled context window.
pub def Fold.resume_budget (setting : Option I64) (window : I64) (compact_at : I64) : I64 :=
    match setting {
        Option.some n => n,
        Option.none => Fold.tail_budget window compact_at,
    }

/// Does this history already fit its tail budget? A fitting history is not
/// folded at all.
pub def Fold.fits (history : List Message) (budget : I64) : Bool :=
    Bool.not (I64.gt (history_tokens history) budget)

/// A text block's first line, capped: enough to recognize the turn, never
/// enough to re-upload it.
def first_line_cut (s : String) : String :=
    Text.cut Fold.line_max (Text.first_line s)

/// A text block's LAST line, capped, or "" when it has only one line. A
/// tool result's tail is usually where the verdict is ("ok", "3 failed"),
/// so it is worth its one line.
def last_line_cut (s : String) : String :=
    let i : I64 := String.find_last s "\n" in
    if i < 0i64 then ""
    else Text.cut Fold.line_max (String.drop (i + 1i64) s)

/// `1234 bytes` -- what tells the model a real result existed, and roughly
/// how much it has been spared.
def bytes_note (n : I64) : String :=
    String.concat (I64.to_string n) " bytes"

def role_label (r : Role) : String :=
    match r {
        Role.user => "user",
        Role.assistant => "assistant",
        Role.tool => "tool",
        Role.system_ => "system",
    }

/// One digest line for one content block. Tool output is DROPPED (its size,
/// first and last line survive); thinking is dropped to its size; a text
/// block survives as its first line.
def content_line (c : Content) : String :=
    match c {
        Content.text s => first_line_cut s,
        Content.tool_use _ name _ => String.concat "[call " (String.concat name "]"),
        Content.tool_result _ output is_error =>
            let mark : String := if is_error then "[tool result error, " else "[tool result, " in
            let head : String := String.concat mark (String.concat (bytes_note (String.length output)) "]") in
            let first : String := first_line_cut output in
            let last : String := last_line_cut output in
            let shown : String :=
                if String.is_empty last
                then first
                else String.concat first (String.concat " .. " last) in
            String.concat head (String.concat ": " shown),
        Content.thinking s _ =>
            String.concat "[thinking, " (String.concat (bytes_note (String.length s)) "]"),
    }

#[partial]
def content_lines (cs : List Content) (acc : List String) : List String :=
    match cs {
        List.empty => acc,
        List.cons c rest =>
            let l : String := content_line c in
            if String.is_empty l then content_lines rest acc
            else content_lines rest (List.cons l acc),
    }

/// `user: the ask; [call read_file]` -- one line per message.
def message_line (m : Message) : String :=
    let parts : List String := content_lines m.content List.empty in
    String.concat (role_label m.role)
        (String.concat ": " (String.concat (List.intercalate "; " (List.reverse parts)) "\n"))

#[partial]
def message_lines (ms : List Message) (acc : List String) : List String :=
    match ms {
        List.empty => acc,
        List.cons m rest => message_lines rest (List.cons (message_line m) acc),
    }

/// The digest BODY: one line per dropped message. Exposed (rather than only
/// reachable through `fold_session`) so the tests can pin the sizing and
/// quoting rules without building a whole session.
pub def Fold.digest_body (ms : List Message) : String :=
    String.concat_list (List.reverse (message_lines ms List.empty))

/// The pointer that keeps the dropped turns REACHABLE: where the verbatim
/// messages live, and which read-tool knobs walk them.
pub def Fold.pointer_line (dir : String) (seq : I64) : String :=
    String.concat_list [
        "\nThe full transcript of these earlier turns is on disk, unmodified, at\n",
        dir,
        "/history blocks, starting at ",
        I64.to_string seq,
        ".json (one JSON block per turn). Read it with the read tool's\n",
        "`offset` and `limit` arguments when the summary above is not enough.\n",
    ]

/// The whole digest message body.
pub def Fold.digest_text (dropped : List Message) (dir : String) (seq : I64) : String :=
    String.concat_list [
        "[earlier conversation, folded at resume: ",
        I64.to_string (List.length dropped),
        " messages]\n",
        Fold.digest_body dropped,
        Fold.pointer_line dir seq,
    ]

/// The digest as the message that replaces the dropped turns: a SYSTEM
/// message, not a user turn (a system message mid-history folds into the
/// wire's own system blocks).
def digest_message (dropped : List Message) (dir : String) (seq : I64) : Message :=
    { role := Role.system_, content := [Content.text (Fold.digest_text dropped dir seq)] }

/// The one startup note line: what was folded and where the original is.
pub def Fold.digest_note (n : I64) (dir : String) : String :=
    String.concat_list [
        "context folded: ",
        I64.to_string n,
        " earlier messages became one digest (originals in ",
        dir,
        "/history)",
    ]

/// The first `n` messages, in order. (`Compact` has a private `drop_messages`
/// but nothing takes a prefix; this is the one shape the fold needs.)
#[partial]
def take_n (n : I64) (ms : List Message) (acc : List Message) : List Message :=
    if n < 1i64 then List.reverse acc
    else match ms {
        List.empty => List.reverse acc,
        List.cons m rest => take_n (n - 1i64) rest (List.cons m acc),
    }

/// One fold: cut the history at a user-message boundary with
/// `Compact.keep_tail`, replace the older prefix with the digest, and report
/// the new session. `none` when nothing had to happen -- an empty history, a
/// zero budget, or a history that already fits.
///
/// `seq` is the block number the loaded history STARTS at (the store's
/// `history_base`): the dropped prefix is the head of the concatenation of
/// blocks `seq` .., so the pointer must name `seq`, not a constant. An
/// already-compacted session resumes from `history_base > 1`, and pointing
/// the model at a block that is not there is worse than no pointer at all.
pub def Fold.fold_session (s : Session) (dir : Path) (seq : I64) (budget : I64) : Option Compact.Outcome :=
    if I64.lt budget 1i64 then Option.none
    else if Fold.fits s.history budget then Option.none
    else
        let keep : List Message := Compact.keep_tail s.history budget in
        let dropped_n : I64 := List.length s.history - List.length keep in
        if I64.lt dropped_n 1i64 then Option.none
        else
            let dropped : List Message := take_n dropped_n s.history List.empty in
            let d : String := Path.to_string dir in
            let digest : Message := digest_message dropped d seq in
            let history2 : List Message := List.cons digest keep in
            let sess2 : Session := { s with history := history2 } in
            let out : Compact.Outcome := {
                session := sess2,
                before := List.length s.history,
                after := List.length history2,
                tokens := Compact.estimate sess2,
            } in
            Option.some out
