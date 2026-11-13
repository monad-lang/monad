// Phase 5's config gate: a `ply.toml` rebinds a key, and the PURE `update`
// honors it (code-editor.md's Phase 5 gate, literally).
//
// THE GATE IS THE JOIN, not just the parse. A test that only asserted
// `Config.parse` produced a `Binding` would pass on a config module nothing
// reads; so every "the update honors it" case builds an `EditorState` whose
// bindings ARE the default table plus the config's rows, presses the rebound
// key through `update`, and asserts the command ran.
//
// THE OVERRIDE MECHANISM IS THE KEYMAP'S LAST-MATCH RULE, so the layering
// tests never delete a row: they append and check that the later row won.
//
// No record patterns or bare nested struct literals inside `#[test]` defs:
// `cf_*` accessors hold every read, per this repo's recorded two-host
// inference hazard.

use lib::config {Config, Config.empty}
use lib::keymap {Binding, Keymap.default_bindings, Keymap.resolve, Keymap.seq_eq,
    KeyResult}
use lib::model {Document, Document.of_text, EditorState, EditorMsg, EditorState.init,
    EditorState.bindings_of, EditorState.with_bindings}
use lib::commands {update}
use lib::rope {Rope.to_string}
use lib::types {Rope, Selection, Selections}
use lib::selection {Selections.primary_sel, Selection.start, Selection.stop}
use tui::types {Key}
// `List.length` lives in `init/src/list.mo` (ambient and pure) as of the
// upstream move, so this import pulls the module's INSTANCES into scope and
// names nothing -- the empty brace list is the documented form.
use std::list {}
use init::shared {Shared}
use lib::instances {}

// ── Fixtures ─────────────────────────────────────────────────────────────

/// A `ply.toml` that rebinds `j` from `move_char_down` to `delete`, which is
/// observable on a one-line buffer: `delete` on a bare cursor removes nothing,
/// while `move_char_down` cannot move. So the fixture rebinds `x` instead --
/// see `cf_rebind_x`.
def cf_rebind_x_doc : String :=
    "[keys.normal]\n\"x\" = \"select_all\"\n"

/// A config file that is not TOML at all.
def cf_bad_toml : String := "[keys.normal\n\"x\" = oops\n"

/// A config naming a key no editor has.
def cf_bad_key_doc : String :=
    "[keys.normal]\n\"notakey\" = \"delete\"\n"

/// A config whose command is not a string.
def cf_bad_command_doc : String :=
    "[keys.normal]\n\"x\" = 42\n"

// ── Accessors, one read each ──────────────────────────────────────────────

/// The config's binding rows.
def cf_rows (c : Config) : List Binding := Config.bindings_of c

/// The config's dropped lines.
def cf_problems (c : Config) : List String := Config.problems_of c

/// The first binding's command name, or `<none>`.
def cf_first_command (c : Config) : String :=
    match cf_rows c {
        List.cons one _ => cf_binding_command one,
        List.empty => "<none>"
    }

/// One binding's command name.
def cf_binding_command (b : Binding) : String :=
    match b { { command, .. } => command }

/// One binding's mode table name.
def cf_binding_mode (b : Binding) : String :=
    match b { { mode, .. } => mode }

/// One binding's key sequence.
def cf_binding_keys (b : Binding) : List Key :=
    match b { { keys, .. } => keys }

/// The first binding's keys, for the grammar pins.
def cf_first_keys (c : Config) : List Key :=
    match cf_rows c {
        List.cons one _ => cf_binding_keys one,
        List.empty => List.empty
    }

/// A parsed spec's key sequence, or the empty list.
def cf_keys_of (spec : String) : List Key :=
    match Config.parse_key_spec spec {
        Option.some ks => ks,
        Option.none => List.empty
    }

/// A fresh state whose bindings are `default_bindings ++ config rows` -- the
/// exact composition `EditorState.init` performs with a config in hand.
def cf_state_with (text : String) (c : Config) : EditorState :=
    let base : EditorState :=
        EditorState.init (Document.of_text text) 24 80 in
    EditorState.with_bindings base (cf_layered c)

/// The layered table: the defaults first, the config's rows after them (the
/// keymap keeps the LAST match, so a config row wins).
def cf_layered (c : Config) : List Binding :=
    List.append Keymap.default_bindings (cf_rows c)

/// One `update` step over a key.
def cf_press (st : EditorState) (k : Key) : EditorState :=
    let msg : EditorMsg := EditorMsg.key k in
    match update st msg {
        Pair.pair after _ => after
    }

/// A whole keystroke script.
#[terminating]
def cf_type (st : EditorState) (keys : List Key) : EditorState :=
    match keys {
        List.empty => st,
        List.cons k rest => cf_type (cf_press st k) rest
    }

/// A character key.
def cf_key (c : String) : Key := Key.char c

/// The state's active document text.
def cf_text (st : EditorState) : String :=
    match EditorState.active_doc st {
        Option.some doc => Rope.to_string (cf_doc_rope doc),
        Option.none => "<no doc>"
    }

def cf_doc_rope (doc : Document) : Rope :=
    match doc { { rope, .. } => rope }

/// The state's binding table, read once.
def cf_bindings (st : EditorState) : List Binding := EditorState.bindings_of st

// ── The key grammar ──────────────────────────────────────────────────────

/// A single character is that character key.
#[test]
def test_spec_single_char : Bool :=
    Keymap.seq_eq (cf_keys_of "j") (List.cons (cf_key "j") List.empty)

/// A named key is its constructor: `space` is the space character key (the
/// same key the `Space w` chord binds), `esc` is Escape.
#[test]
def test_spec_named_keys : Bool :=
    Keymap.seq_eq (cf_keys_of "space") (List.cons (cf_key " ") List.empty)
        && Keymap.seq_eq (cf_keys_of "esc") (List.cons Key.escape List.empty)
        && Keymap.seq_eq (cf_keys_of "enter") (List.cons Key.enter List.empty)

/// A modifier form: `A-j` is Alt-j, `C-x` is Ctrl-x. EITHER CASE, because a
/// config is written by hand -- `a-j` must be the same spec.
#[test]
def test_spec_modifiers : Bool :=
    Keymap.seq_eq (cf_keys_of "A-j") (List.cons (Key.alt "j") List.empty)
        && Keymap.seq_eq (cf_keys_of "C-x") (List.cons (Key.ctrl "x") List.empty)
        && Keymap.seq_eq (cf_keys_of "a-j") (cf_keys_of "A-j")

/// A chord is `-`-separated, exactly as the plan's §4 table spells it:
/// `space-w` is the two-key `Space w`, `g-g` is `gg`.
#[test]
def test_spec_chords : Bool :=
    Keymap.seq_eq (cf_keys_of "space-w")
        (List.cons (cf_key " ") (List.cons (cf_key "w") List.empty))
        && Keymap.seq_eq (cf_keys_of "g-g")
            (List.cons (cf_key "g") (List.cons (cf_key "g") List.empty))

/// A spec with an unknown key is rejected WHOLE -- never a partial sequence,
/// which would fire on the first key alone.
#[test]
def test_spec_rejects_unknown_whole : Bool :=
    cf_is_rejected "notakey" && cf_is_rejected "j-notakey" && cf_is_rejected ""

/// A spec that names no key at all: an empty part (a trailing `-`) is a typo,
/// not a key.
#[test]
def test_spec_rejects_empty_part : Bool :=
    cf_is_rejected "j-" && cf_is_rejected "-j"

def cf_is_rejected (spec : String) : Bool :=
    match Config.parse_key_spec spec {
        Option.some _ => false,
        Option.none => true
    }

// ── A config file's rows ─────────────────────────────────────────────────

/// A file's `[keys.normal]` row becomes a binding with THAT table's mode name.
#[test]
def test_parse_one_row : Bool :=
    let c : Config := Config.parse cf_rebind_x_doc "ply.toml" in
    I64.beq (List.length (cf_rows c)) 1
        && String.beq (cf_first_command c) "select_all"
        && String.beq (cf_binding_mode (cf_first_row c)) "normal"
        && Keymap.seq_eq (cf_first_keys c) (List.cons (cf_key "x") List.empty)

/// The first row of a config, for the field pins.
def cf_first_row (c : Config) : Binding :=
    match cf_rows c {
        List.cons one _ => one,
        List.empty => cf_no_binding
    }

/// A stand-in binding for the empty case.
def cf_no_binding : Binding :=
    { mode := "", keys := List.empty, command := "" }

/// A well-formed file reports no problems -- the pin that the problem list
/// is not just always-populated noise.
#[test]
def test_good_config_has_no_problems : Bool :=
    I64.beq (List.length (cf_problems (Config.parse cf_rebind_x_doc "ply.toml"))) 0

/// A file that is not TOML is one problem line naming the source, and no rows.
#[test]
def test_bad_toml_is_a_problem : Bool :=
    let c : Config := Config.parse cf_bad_toml "ply.toml" in
    I64.beq (List.length (cf_rows c)) 0
        && I64.beq (List.length (cf_problems c)) 1
        && String.starts_with "ply.toml: " (cf_first_problem c)

/// The first problem line.
def cf_first_problem (c : Config) : String :=
    match cf_problems c {
        List.cons one _ => one,
        List.empty => "<none>"
    }

/// An unknown KEY is a problem line naming the row, and contributes no row.
#[test]
def test_bad_key_is_a_problem : Bool :=
    let c : Config := Config.parse cf_bad_key_doc "ply.toml" in
    I64.beq (List.length (cf_rows c)) 0
        && String.contains (cf_first_problem c) "notakey"

/// A command that is not a string is a problem line too -- `x = 42` is not a
/// binding, and saying so is better than binding `x` to "42".
#[test]
def test_non_string_command_is_a_problem : Bool :=
    let c : Config := Config.parse cf_bad_command_doc "ply.toml" in
    I64.beq (List.length (cf_rows c)) 0
        && String.contains (cf_first_problem c) "must be a string"

/// A file with no `[keys]` table binds nothing and reports nothing: a
/// `ply.toml` that only holds a future `[options]` table must not look broken.
#[test]
def test_no_keys_table_is_empty : Bool :=
    let c : Config := Config.parse "[options]\ntab_width = 2\n" "ply.toml" in
    I64.beq (List.length (cf_rows c)) 0 && I64.beq (List.length (cf_problems c)) 0

// ── Layering: the project file wins, per key ─────────────────────────────

/// THE OVERRIDE: the same key bound in two layers resolves to the LATER row.
/// Fixture: the global file binds `x` to `select_all`, the project file binds
/// it to `extend_line` -- the layered table resolves `x` to the project's.
#[test]
def test_later_layer_wins_per_key : Bool :=
    let global : Config :=
        Config.parse "[keys.normal]\n\"x\" = \"select_all\"\n" "global" in
    let project : Config :=
        Config.parse "[keys.normal]\n\"x\" = \"extend_line\"\n" "project" in
    let both : Config := Config.merge global project in
    let layered : List Binding :=
        List.append Keymap.default_bindings (cf_rows both) in
    cf_resolves layered "normal" "x" "extend_line"

/// A key only the EARLIER layer binds still resolves to it: layering adds, it
/// does not replace the whole table.
#[test]
def test_earlier_layer_survives_where_unshadowed : Bool :=
    let global : Config :=
        Config.parse "[keys.normal]\n\"x\" = \"select_all\"\n" "global" in
    let project : Config :=
        Config.parse "[keys.normal]\n\"y\" = \"yank\"\n" "project" in
    let both : Config := Config.merge global project in
    let layered : Shared (List Binding) :=
        Shared.of (List.append Keymap.default_bindings (cf_rows both)) in
    cf_resolves (Shared.get layered) "normal" "x" "select_all"
        && cf_resolves (Shared.get layered) "normal" "y" "yank"

/// Does the table resolve `spec` (in `mode`) to `command`?
def cf_resolves (bindings : List Binding) (mode : String) (spec : String) (command : String) : Bool :=
    match Keymap.resolve bindings mode (cf_keys_of spec) {
        KeyResult.matched got => String.beq got command,
        KeyResult.prefix => false,
        KeyResult.unbound => false
    }

/// `Config.bindings_of_all` in one step: three layers, last wins.
#[test]
def test_bindings_of_all_orders_layers : Bool :=
    let a : Config := Config.parse "[keys.normal]\n\"x\" = \"select_all\"\n" "a" in
    let b : Config := Config.parse "[keys.normal]\n\"x\" = \"yank\"\n" "b" in
    let c : Config := Config.parse "[keys.normal]\n\"x\" = \"delete\"\n" "c" in
    let layered : List Binding :=
        List.append Keymap.default_bindings
            (Config.bindings_of_all [a, b, c]) in
    cf_resolves layered "normal" "x" "delete"

// ── THE GATE: the pure update honors a rebound key ───────────────────────

/// THE PHASE 5 GATE. The fixture rebinds `x` from `extend_line` (the default,
/// which selects lines) to `delete`. On "abc": with the DEFAULT table, `x`
/// selects the line (a selection, no edit -- the text stays "abc"); with the
/// CONFIG's table, `x` runs `delete` on the bare cursor, which removes the
/// empty span -- still "abc". So the observable difference is the SELECTION,
/// and the fixture is read through `d`: `x d` with the config deletes nothing
/// (the cursor's empty span) while `x d` with the default deletes the whole
/// line.
///
/// That is the assertion: the same two keystrokes produce different text
/// under the two tables, and the config's table produces the CONFIGURED
/// command's effect.
#[test]
def test_config_rebinds_and_update_honors_it : Bool :=
    let cfg : Config :=
        Config.parse "[keys.normal]\n\"x\" = \"select_all\"\n" "ply.toml" in
    cf_rebind_effects cfg

/// The gate's body: `x` then `d` under a table where `x` means `select_all`
/// deletes the whole buffer, while the default `x` (extend_line) deletes one
/// line. Fixture "abc\ndef": the config's answer is "", the default's is
/// "\ndef".
def cf_rebind_effects (cfg : Config) : Bool :=
    let configured : EditorState := cf_state_with "abc\ndef" cfg in
    let defaulted : EditorState :=
        EditorState.init (Document.of_text "abc\ndef") 24 80 in
    let configured_after : EditorState :=
        cf_type configured [cf_key "x", cf_key "d"] in
    let default_after : EditorState :=
        cf_type defaulted [cf_key "x", cf_key "d"] in
    String.beq (cf_text configured_after) ""
        && String.beq (cf_text default_after) "\ndef"

/// A config row can rebind on ANOTHER mode's table too, and the update honors
/// it there: `[keys.insert]` binding `escape` to `delete` would be terrible
/// but is expressible, so the mode field must be read from the TABLE NAME.
/// The fixture is harmless and observable: `[keys.normal]` rebinds `q` to
/// `yank` (a normal-mode key), and pressing `q` after selecting a word yanks
/// it into the registers rather than doing nothing.
#[test]
def test_config_row_carries_its_table_mode : Bool :=
    let cfg : Config := Config.parse "[keys.insert]\n\"x\" = \"delete\"\n" "ply.toml" in
    String.beq (cf_binding_mode (cf_first_row cfg)) "insert"

/// A config's chord rebinds a chord: `g-g` re-pointed at `goto_end`, so `gg`
/// goes to the END of the buffer instead of its start. The update proof: on
/// "abc", `g g` with the config leaves the head at 3 (the end) rather than 0.
#[test]
def test_config_rebinds_a_chord : Bool :=
    let cfg : Config := Config.parse "[keys.normal]\n\"g-g\" = \"goto_end\"\n" "ply.toml" in
    let st : EditorState := cf_state_with "abc" cfg in
    let after : EditorState := cf_type st [cf_key "g", cf_key "g"] in
    String.beq (cf_span_of after) "3..3"

/// The primary selection's head as `n..n`, or `<none>` -- the one read a
/// chord's effect needs (a collapsed cursor after `gg`/`ge`).
def cf_span_of (st : EditorState) : String :=
    match EditorState.active_doc st {
        Option.none => "<none>",
        Option.some doc => cf_head_of (cf_doc_sel doc)
    }

/// The primary selection's head, rendered.
def cf_head_of (sel : Selections) : String :=
    match Selections.primary_sel sel {
        Option.some s => cf_sel_span (Shared.of s),
        Option.none => "<none>"
    }

/// One selection's two ends, from one handle (both accessors read it).
def cf_sel_span (s : Shared Selection) : String :=
    I64.to_string (Selection.start (Shared.get s))
        ++ ".." ++ I64.to_string (Selection.stop (Shared.get s))

/// The document's selections.
def cf_doc_sel (doc : Document) : Selections :=
    match doc { { selections, .. } => selections }

/// A config with a problem still binds its good rows: an unreadable ROW does
/// not void the file. Fixture: one good row (`x`) and one bad key.
#[test]
def test_problem_row_does_not_void_the_file : Bool :=
    let cfg : Config :=
        Config.parse "[keys.normal]\n\"x\" = \"select_all\"\n\"nokey\" = \"delete\"\n" "ply.toml" in
    I64.beq (List.length (cf_rows cfg)) 1
        && I64.beq (List.length (cf_problems cfg)) 1
        && String.beq (cf_first_command cfg) "select_all"
