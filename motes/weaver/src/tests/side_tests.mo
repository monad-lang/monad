/// Side commands (`side.mo`): which lines run at once in a dialog, the
/// `/btw` question split, and when a side dialog fills the screen.
use weaver::side {Side.wanted, Side.btw_question, Side.fullscreen}

#[test]
def test_bare_read_only_forms_are_side_commands : Bool :=
    Side.wanted false "/help" && Side.wanted false "/h" && Side.wanted false "/todos"
        && Side.wanted false "/tools" && Side.wanted false "/log" && Side.wanted false "/mcp"
        && Side.wanted false "/memory" && Side.wanted false "/budget" && Side.wanted false "/mode"
        && Side.wanted false "/btw"

#[test]
def test_arguments_and_mutations_are_not_side_commands : Bool :=
    Bool.not (Side.wanted false "/mode plan") && Bool.not (Side.wanted false "/model")
        && Bool.not (Side.wanted false "/plan approve manual") && Bool.not (Side.wanted false "/settings")
        && Bool.not (Side.wanted false "/memory reload") && Bool.not (Side.wanted false "hello")

/// Bare `/plan` is the read-only view outside plan mode only.
#[test]
def test_plan_is_a_side_command_outside_plan_mode : Bool :=
    Side.wanted false "/plan" && Bool.not (Side.wanted true "/plan")

#[test]
def test_btw_question_split : Bool :=
    let q : Bool := match Side.btw_question "/btw  why the retry? " { Option.some s => s == "why the retry?", Option.none => false } in
    let bare : Bool := match Side.btw_question "/btw" { Option.some _ => false, Option.none => true } in
    let blank : Bool := match Side.btw_question "/btw   " { Option.some _ => false, Option.none => true } in
    let other : Bool := match Side.btw_question "/btwx" { Option.some _ => false, Option.none => true } in
    q && bare && blank && other

#[test]
def test_fullscreen_for_long_or_wide_text : Bool :=
    Bool.not (Side.fullscreen ["mode: manual"])
        && Side.fullscreen [String.repeat "x" 90]
        && Side.fullscreen ["1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15", "16", "17"]
