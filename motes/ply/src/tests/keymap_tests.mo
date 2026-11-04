// Phase 2's keymap gate: what a key sequence resolves to.
//
// THE THREE-ANSWER CONTRACT (the plan's Decision 4): a sequence names a
// command (`matched`), is a strict prefix of one that exists (`prefix` --
// the normal state of a chord's first key, not an error), or matches
// nothing (`unbound`, which clears `pending`). Every expectation below
// pins one answer against the default table's own rows, with the chord
// spelled out beside it.
//
// No record patterns or bare struct literals inside `#[test]` defs: the
// `KeyResult` answers go through the `km_*` accessors below, per the
// recorded two-host inference hazard (AGENTS.md's "bind to an annotated
// local first" and this mote's Phase 1 selection-test lesson).

use lib::types {Mode}
use lib::keymap {KeyResult, Binding, Keymap.resolve, Keymap.default_bindings,
    Keymap.mode_table}
use tui::types {Key}
use lib::instances {}

// --- Accessors: one read per binding, each used once ---

/// The command a `matched` names, or `none` for any other answer.
def km_matched (r : KeyResult) : Option String :=
    match r {
        KeyResult.matched cmd => Option.some cmd,
        _ => Option.none
    }

/// Whether the answer is `prefix` (a chord's first key).
def km_is_prefix (r : KeyResult) : Bool :=
    match r {
        KeyResult.prefix => true,
        _ => false
    }

/// Whether the answer is `unbound`.
def km_is_unbound (r : KeyResult) : Bool :=
    match r {
        KeyResult.unbound => true,
        _ => false
    }

// --- Key builders: the table's own spellings, not raw literals ---

/// One character key.
def km_char (c : String) : Key := Key.char c

/// The sequence for a chord, one character key per byte -- `mi(` is three
/// keys, the third of which is `(`. One `String.from_list` per byte; these
/// are test fixtures of a few bytes, not hot paths.
#[terminating]
def km_chars (s : String) : List Key :=
    km_char_bytes (String.to_list s)

#[terminating]
def km_char_bytes (bs : List U8) : List Key :=
    match bs {
        List.empty => List.empty,
        List.cons b rest => List.cons (km_one_key b) (km_char_bytes rest)
    }

/// One byte as a one-character key.
def km_one_key (b : U8) : Key := Key.char (String.from_list (List.cons b List.empty))

/// `Space` is `Key.char " "` in the decoder's spelling.
def km_space : Key := Key.char " "

// ── Single keys: matched ────────────────────────────────────────────────

#[test]
def test_h_moves_left : Bool :=
    String.beq (km_expect_matched (km_resolve "normal" [km_char "h"])) "move_char_left"

#[test]
def test_d_deletes : Bool :=
    String.beq (km_expect_matched (km_resolve "normal" [km_char "d"])) "delete"

#[test]
def test_u_undoes : Bool :=
    String.beq (km_expect_matched (km_resolve "normal" [km_char "u"])) "undo"

/// The `%` select-all and `x` extend-line single keys.
#[test]
def test_x_and_percent : Bool :=
    String.beq (km_expect_matched (km_resolve "normal" [km_char "x"])) "extend_line"
        && String.beq (km_expect_matched (km_resolve "normal" [km_char "%"])) "select_all"

/// The `matched` accessor's unwrapping, as a helper so a failing test
/// reports `<none>` rather than just false.
def km_expect_matched (r : KeyResult) : String :=
    match km_matched r {
        Option.some cmd => cmd,
        Option.none => "<none>"
    }

/// One resolution against the default table.
def km_resolve (mode : String) (keys : List Key) : KeyResult :=
    Keymap.resolve Keymap.default_bindings mode keys

// ── Chords: prefix, then matched ────────────────────────────────────────

/// THE GATE CASE: a bare `g` is a PREFIX of `gg`/`ge`/`gd`/`gr`, never a
/// command of its own -- the answer is a value, not an error, because a
/// partial sequence is the normal state of the input (the plan's Decision 4).
#[test]
def test_bare_g_is_prefix : Bool :=
    km_is_prefix (km_resolve "normal" [km_char "g"])

/// THE GATE CASE: `g d` names `goto_definition` (the command itself is a
/// Phase 6 stub; the BINDING exists now and that is what this gate pins).
#[test]
def test_gd_matches_goto_definition : Bool :=
    String.beq (km_expect_matched (km_resolve "normal" [km_char "g", km_char "d"])) "goto_definition"

#[test]
def test_gg_matches_goto_start : Bool :=
    String.beq (km_expect_matched (km_resolve "normal" [km_char "g", km_char "g"])) "goto_start"

/// `m i` is a prefix; `m i (` names match-inside. Pinned together so a
/// resolver that answered `unbound` for the prefix could not pass by
/// accident on the full chord.
#[test]
def test_mi_prefix_then_match_inside : Bool :=
    km_is_prefix (km_resolve "normal" [km_char "m", km_char "i"])
        && String.beq (km_expect_matched (km_resolve "normal" (km_chars "mi("))) "match_inside"

#[test]
def test_ma_matches_match_around : Bool :=
    String.beq (km_expect_matched (km_resolve "normal" (km_chars "ma("))) "match_around"

/// `Space` is a prefix; `Space w` names write, `Space q` quit, `Space f`
/// the file picker.
#[test]
def test_space_prefix_then_children : Bool :=
    km_is_prefix (km_resolve "normal" [km_space])
        && String.beq (km_expect_matched (km_resolve "normal" [km_space, km_char "w"])) "write"
        && String.beq (km_expect_matched (km_resolve "normal" [km_space, km_char "q"])) "quit"
        && String.beq (km_expect_matched (km_resolve "normal" [km_space, km_char "f"])) "file_picker"

// ── Unbound ─────────────────────────────────────────────────────────────

/// A key nothing starts with answers `unbound`, and the caller (update)
/// clears `pending` -- the gate's third case.
#[test]
def test_z_is_unbound : Bool :=
    km_is_unbound (km_resolve "normal" [km_char "z"])

/// A key that starts a chord but leads nowhere: `g` then `z` matches no
/// binding and is not a prefix of one, so it answers `unbound` -- not
/// `prefix` by virtue of `g` alone.
#[test]
def test_gz_is_unbound : Bool :=
    km_is_unbound (km_resolve "normal" [km_char "g", km_char "z"])

// ── Mode tables ──────────────────────────────────────────────────────────

/// `escape` in the insert table names `normal_mode` -- the mode table's
/// name, not the `Mode` value (the plan's §3 note).
#[test]
def test_escape_in_insert_is_normal_mode : Bool :=
    String.beq (km_expect_matched (km_resolve "insert" [Key.escape])) "normal_mode"

#[test]
def test_escape_in_select_is_normal_mode : Bool :=
    String.beq (km_expect_matched (km_resolve "select" [Key.escape])) "normal_mode"

#[test]
def test_escape_in_command_is_normal_mode : Bool :=
    String.beq (km_expect_matched (km_resolve "command" [Key.escape])) "normal_mode"

#[test]
def test_escape_in_search_is_normal_mode : Bool :=
    String.beq (km_expect_matched (km_resolve "search" [Key.escape])) "normal_mode"

/// A normal-mode key does not answer in the insert table: `d` types in
/// insert mode, it does not delete. Pinned so a resolver that ignored the
/// mode column cannot pass.
#[test]
def test_d_in_insert_is_unbound : Bool :=
    km_is_unbound (km_resolve "insert" [km_char "d"])

/// The `Mode` value's table name, as data -- the one place the mapping
/// lives, so a new mode updates one def (and the `mode_table` test below
/// pins that every mode HAS one).
#[test]
def test_every_mode_has_a_table : Bool :=
    Bool.not (String.beq (km_mode_table Mode.normal) "<none>")
        && Bool.not (String.beq (km_mode_table Mode.insert) "<none>")
        && Bool.not (String.beq (km_mode_table Mode.select) "<none>")
        && Bool.not (String.beq (km_mode_table (Mode.command "")) "<none>")
        && Bool.not (String.beq (km_mode_table (Mode.search "")) "<none>")

def km_mode_table (m : Mode) : String :=
    match Keymap.mode_table m {
        Option.some t => t,
        Option.none => "<none>"
    }

// ── The table is data: a binding built by hand resolves ─────────────────

/// Rebinding works with no code (the plan's Decision 4): a hand-built
/// binding table resolves the SAME way the default table does, so
/// `ply.toml` (Phase 5) can merge its rows in as data.
#[test]
def test_a_hand_built_table_resolves : Bool :=
    String.beq (km_expect_matched (Keymap.resolve (km_rebound) "normal" [Key.alt "j"])) "join_selections"
        && km_is_unbound (Keymap.resolve (km_rebound) "normal" [km_char "h"])

/// The one-row table the test above resolves against -- a binding that
/// does not exist in the default table, so passing by accident is
/// impossible. The literal is the sole element of a `List.cons`, i.e. an
/// argument position, so it is bound inside a def with a declared return
/// type (the nested-literal half of the two-host gotcha).
def km_rebound : List Binding :=
    List.cons km_one_binding List.empty

/// The row itself, on its own line with its own annotation.
def km_one_binding : Binding := { mode := "normal", keys := [Key.alt "j"], command := "join_selections" }
