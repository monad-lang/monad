// Ply's keymap: bindings as data, commands by name (code-editor.md Design
// §3 first block and §4 table, Decision 4).
//
// A BINDING MAPS A KEY SEQUENCE TO A COMMAND *NAME*, never to a function:
// that is what makes rebinding a config edit rather than a code change
// (the plan's Decision 4, and how Helix's own config works). The registry
// that pairs names with functions lives in `commands.mo`; this module
// knows nothing about it.
//
// RESOLUTION ANSWERS A VALUE, NOT AN ERROR (the same reason
// `toolkit::framing` returns `need_more`): a partial chord is the normal
// state of the input. `matched` names a command, `prefix` says some
// binding starts with the sequence (wait for more keys), `unbound` says
// nothing does (the caller clears the pending prefix).
//
// NO DERIVES HERE: this file holds function bodies, and a derive-bearing
// file must hold none (`motes/tui/src/types.mo`'s rule). `KeyResult`'s
// answers are compared through the constructor matches in the tests,
// not through a derived `==`.

use init::shared {Shared}
use lib::types {Mode}
use tui::types {Key}

/// Where a key sequence lands in a mode's table.
pub type KeyResult {
    /// The sequence names a command.
    matched (command : String),
    /// The sequence is a strict prefix of at least one binding: wait
    /// for more keys.
    prefix,
    /// Nothing starts with this sequence.
    unbound
}

/// One binding: in `mode`, the key sequence `keys` runs the command named
/// `command`. `mode` is the mode TABLE's name (`"normal"`, `"insert"`),
/// not a `Mode` value -- config files address tables by name (the plan's
/// §3 note).
pub struct Binding {
    mode : String,
    keys : List Key,
    command : String
}

/// A key sequence's byte equality: element-wise over the two lists, with
/// `Key`'s own derived `==` per element. Hand-rolled rather than a generic
/// `BEq (List A)` dispatch, whose runtime instance resolution is a
/// recorded hazard (`std/src/map.mo`'s TODO; the same reasoning as
/// `List.contains_by`'s explicit comparator).
#[terminating]
pub def Keymap.seq_eq (a : List Key) (b : List Key) : Bool :=
    match a {
        List.empty => List.is_empty b,
        List.cons x arest =>
            match b {
                List.empty => false,
                List.cons y brest => if x == y then Keymap.seq_eq arest brest else false
            }
    }

/// Whether `xs` starts with `prefix` and is strictly longer -- the test
/// behind the `prefix` answer. Strictly longer, so a COMPLETE sequence
/// never answers `prefix` (a binding that exists is `matched`, even if
/// a longer binding also starts with it).
#[terminating]
pub def Keymap.has_prefix (xs : List Key) (prefix : List Key) : Bool :=
    match prefix {
        List.empty => Bool.not (List.is_empty xs),
        List.cons p prest =>
            match xs {
                List.empty => false,
                List.cons x xrest => if x == p then Keymap.has_prefix xrest prest else false
            }
    }

/// Resolve a key sequence against a binding table, in one mode.
///
/// The answer rules, in order:
///   1. a binding whose keys EQUAL the sequence, in this mode ->
///      `matched` (the LAST such binding wins, so a later row overrides
///      an earlier one -- the merge order `ply.toml` will rely on);
///   2. no equality, but some binding's keys START WITH the sequence ->
///      `prefix`;
///   3. otherwise -> `unbound`.
///
/// The LAST-match rule makes override-by-append work with no deletion
/// pass: a config layer appends its rows and they win over the defaults
/// below them, the same way `list_append`'s head-first scans already
/// behave elsewhere in this repo.
pub def Keymap.resolve (bindings : List Binding) (mode : String) (keys : List Key) : KeyResult :=
    Keymap.resolve_go bindings mode keys KeyResult.unbound false

/// The one-pass scan, carrying the best `matched` seen (so a later row
/// overrides an earlier one) and whether any row makes the sequence a
/// strict prefix. `unbound` is the starting answer because it is also the
/// empty table's answer -- a `List.empty` table needs no case of its own.
#[terminating]
def Keymap.resolve_go (bindings : List Binding) (mode : String) (keys : List Key)
    (best : KeyResult) (saw_prefix : Bool) : KeyResult :=
    // The sequence is compared up to three times per row, so it is shared
    // -- `Shared A` is the affine rule's own remedy for a multi-read
    // value, and a `List` is deliberately not `Copy` (`init/src/copy.mo`'s
    // absent list), so the share is explicit here rather than an
    // instance away.
    let shared : Shared (List Key) := Shared.of keys in
    Keymap.resolve_rows bindings mode shared best saw_prefix

/// The row scan, with the sequence pre-shared. Split out so `resolve_go`
/// reads as one shape and the share happens once per call, not per row.
#[terminating]
def Keymap.resolve_rows (bindings : List Binding) (mode : String) (keys : Shared (List Key))
    (best : KeyResult) (saw_prefix : Bool) : KeyResult :=
    match bindings {
        List.empty =>
            if saw_prefix then KeyResult.prefix else best,
        List.cons b rest =>
            if String.beq b.mode mode
            then
                if Keymap.seq_eq b.keys (Shared.get keys)
                then Keymap.resolve_rows rest mode keys (KeyResult.matched b.command) saw_prefix
                else
                    if Keymap.has_prefix b.keys (Shared.get keys)
                    then Keymap.resolve_rows rest mode keys best true
                    else Keymap.resolve_rows rest mode keys best saw_prefix
            else Keymap.resolve_rows rest mode keys best saw_prefix
    }

/// The mode TABLE's name for a `Mode` value -- the one place the mapping
/// lives, so a new mode is one def's edit. `command`/`search` carry their
/// in-progress text, which the table name ignores.
pub def Keymap.mode_table (m : Mode) : Option String :=
    match m {
        Mode.normal => Option.some "normal",
        Mode.insert => Option.some "insert",
        Mode.select => Option.some "select",
        Mode.command _ => Option.some "command",
        Mode.search _ => Option.some "search"
    }

// ── The default table (the plan's §4) ─────────────────────────────────────
//
// Data, not dispatch: this list IS the Phase 2 deliverable's key half.
// Commands that need a later phase (`gd`/`gr`/`K` need the LSP client,
// Phase 6; `write`/`quit` need the binary, Phase 4) are bound NOW and
// stubbed in the registry, so the bindings are stable data from day one.

/// The mode table's name each builder below takes -- spelled out here so
/// a typo in a row is a visible constant, not a string in a list.

/// One binding, built from a one-key sequence.
def km_bind (mode : String) (k : Key) (command : String) : Binding :=
    { mode := mode, keys := List.cons k List.empty, command := command }

/// One binding over a chord (two or more keys; `km_keys2`/`km_keys3`
/// spell the lengths, since a list literal of `Key`s in argument position
/// is the nested-literal shape the Rust host mis-infers).
def km_bind2 (mode : String) (k1 : Key) (k2 : Key) (command : String) : Binding :=
    { mode := mode, keys := List.cons k1 (List.cons k2 List.empty), command := command }

def km_bind3 (mode : String) (k1 : Key) (k2 : Key) (k3 : Key) (command : String) : Binding :=
    { mode := mode, keys := List.cons k1 (List.cons k2 (List.cons k3 List.empty)), command := command }

/// The default table: the plan's §4, one row per line, in the plan's
/// order. Later rows override earlier ones on a full match (see
/// `resolve`'s LAST-match rule).
pub def Keymap.default_bindings : List Binding :=
    List.append (km_normal_bindings) (km_other_mode_bindings)

/// The normal table's rows, in the plan's §4 order. Each row is a
/// `km_bind*` call -- a function call, not a struct literal, so the
/// Rust host's argument-position inference never sees a `{ .. }` here.
def km_normal_bindings : List Binding :=
    [km_bind "normal" (Key.char "h") "move_char_left",
     km_bind "normal" (Key.char "j") "move_char_down",
     km_bind "normal" (Key.char "k") "move_char_up",
     km_bind "normal" (Key.char "l") "move_char_right",
     km_bind "normal" Key.left "move_char_left",
     km_bind "normal" Key.down "move_char_down",
     km_bind "normal" Key.up "move_char_up",
     km_bind "normal" Key.right "move_char_right",
     km_bind "normal" (Key.char "w") "select_next_word",
     km_bind "normal" (Key.char "b") "select_prev_word",
     km_bind "normal" (Key.char "e") "select_word_end",
     km_bind "normal" (Key.char "x") "extend_line",
     km_bind "normal" (Key.char "%") "select_all",
     km_bind "normal" (Key.char "s") "select_regex",
     km_bind "normal" (Key.char ";") "collapse_selection",
     km_bind "normal" (Key.char ",") "keep_primary_selection",
     km_bind "normal" (Key.char "d") "delete",
     km_bind "normal" (Key.char "c") "change",
     km_bind "normal" (Key.char "y") "yank",
     km_bind "normal" (Key.char "p") "paste",
     km_bind "normal" (Key.char "i") "insert_before",
     km_bind "normal" (Key.char "a") "insert_after",
     km_bind "normal" (Key.char "o") "open_below",
     km_bind "normal" (Key.char "O") "open_above",
     km_bind "normal" (Key.char "u") "undo",
     km_bind "normal" (Key.char "U") "redo",
     km_bind3 "normal" (Key.char "m") (Key.char "i") (Key.char "(") "match_inside",
     km_bind3 "normal" (Key.char "m") (Key.char "a") (Key.char "(") "match_around",
     km_bind2 "normal" (Key.char "g") (Key.char "g") "goto_start",
     km_bind2 "normal" (Key.char "g") (Key.char "e") "goto_end",
     km_bind2 "normal" (Key.char "g") (Key.char "d") "goto_definition",
     km_bind2 "normal" (Key.char "g") (Key.char "r") "goto_references",
     km_bind "normal" (Key.char "K") "hover",
     km_bind2 "normal" (Key.char " ") (Key.char "f") "file_picker",
     km_bind2 "normal" (Key.char " ") (Key.char "w") "write",
     km_bind2 "normal" (Key.char " ") (Key.char "q") "quit",
     km_bind "normal" (Key.char ":") "command_mode",
     km_bind "normal" (Key.char "/") "search_mode"]

/// The other modes' rows: `escape` returns to normal from every one of
/// them (the §4 table's last row). Insert mode's printable keys never
/// reach the table -- `update` treats a character key in insert mode as
/// `insert_char` before consulting `resolve`, so typing is the default
/// case rather than a row per character (see `commands.mo`).
def km_other_mode_bindings : List Binding :=
    [km_bind "insert" Key.escape "normal_mode",
     km_bind "select" Key.escape "normal_mode",
     km_bind "command" Key.escape "normal_mode",
     km_bind "search" Key.escape "normal_mode"]

/// The answer as `(command, is_prefix)`: `some name` with `false` for a
/// match, `none` with `true` for a waiting chord, `none`/`false` for
/// unbound. ONE match, in the one place `KeyResult`'s constructors are
/// in scope, so no consumer of the keymap needs them.
pub def KeyResult.as_pair (r : KeyResult) : Pair (Option String) Bool :=
    match r {
        KeyResult.matched cmd => Pair.pair (Option.some cmd) false,
        KeyResult.prefix => Pair.pair Option.none true,
        KeyResult.unbound => Pair.pair Option.none false
    }
