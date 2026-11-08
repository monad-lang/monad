/// Side commands: the read-only `/` forms the TUI runs at once, even while
/// a turn is running, and shows in a dialog instead of the transcript.
/// Anything with an argument, and anything that opens a picker or changes
/// state, keeps the ordinary path (run when idle, queued during a turn).
use std::map {Map, BTreeMap}
use std::list {List.any, List.length}

def side_map (names : List String) : BTreeMap String Bool :=
    match names {
        List.empty => BTreeMap.empty,
        List.cons n rest => Map.insert n true (side_map rest),
    }

/// The exact lines that read and show, never change.
def side_names : BTreeMap String Bool :=
    side_map ["/help", "/h", "/todos", "/tools", "/log", "/mcp", "/memory", "/budget", "/mode", "/btw"]

/// Whether `text` is a side command. Bare `/plan` is the read-only plan
/// view outside plan mode; in plan mode it is the approval dialog, which
/// changes the mode, so it stays a command there. A bare `/btw` shows its
/// usage; `/btw <question>` is its own path (`Side.btw_question`).
pub def Side.wanted (in_plan : Bool) (text : String) : Bool :=
    if text == "/plan" then Bool.not in_plan
    else match Map.lookup text side_names {
        Option.some _ => true,
        Option.none => false,
    }

/// `/btw <question>`'s question, or none for any other line (a bare
/// `/btw` included: it is a side command showing the usage).
pub def Side.btw_question (text : String) : Option String :=
    if String.starts_with "/btw " text
    then
        let q : String := String.trim (String.drop 5 text) in
        if String.is_empty q then Option.none else Option.some q
    else Option.none

/// A side dialog fills the screen when its text would not sit comfortably
/// in the centred box: many lines, or lines wider than it.
pub def Side.fullscreen (lines : List String) : Bool :=
    Bool.or (I64.lt 16 (List.length lines))
        (List.any (fn (l : String) => I64.lt 82 (String.length l)) lines)
