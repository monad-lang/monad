// Ply's config: `ply.toml` -> the keymap's binding rows (code-editor.md
// Phase 5, Design §3's Decision 4).
//
// A BINDING NAMES A COMMAND, NEVER A FUNCTION -- that is what makes
// rebinding a config edit (the plan's Decision 4). This module is the other
// half of that promise: it turns a `ply.toml` into `Binding` rows, so
// `[keys.normal]` with `"A-j" = "move_char_down"` reaches the very table the
// default keymap builds.
//
// LAYERING IS BY APPEND, AND THE KEYMAP'S LAST-MATCH RULE IS THE OVERRIDE.
// `Keymap.resolve` keeps the LAST matching row, so the layers simply
// concatenate in precedence order -- global file, then project file, then
// what the caller adds -- and nothing has to delete or rewrite a row. The
// plan's "merged per key the way Weaver merges settings" is therefore one
// `List.append`, which is also why a config can rebind a default without
// knowing what the default was.
//
// NO IO HERE. Reading the files is `main.mo`'s job (it has an `IO` and a
// current directory); this module is pure, so a test can drive the whole
// merge with string fixtures and the `monad_eval` interpreter can run it.
//
// NO `#[derive]` HERE: this file holds function bodies, and a derive-bearing
// file must hold none (`motes/tui/src/types.mo`'s rule).
//
// NO LOCAL IS NAMED `insert`/`select`/`prefix`/`tick`: whole-program
// constructor names that shadow same-named locals are the plan's named risk.

use init::shared {Shared}
use init::copy {Copy}
use lib::keymap {Binding}
use tui::types {Key}
use toml {Toml.Value, Toml.parse, Toml.table_get, Toml.ParseError}
use toml::toml {Toml.get_string, Toml.get_table}
use std::map {BTreeMap, BTreeMap.to_list}

// ── The key grammar ────────────────────────────────────────────────────────
//
// A KEY SPEC IS THE SEQUENCE SPELLED WITH `-` BETWEEN ITS KEYS, each key
// being either a modifier letter plus a character (`C-x`, `A-j`) or one of
// the named keys (`space`, `esc`, `enter`, `tab`, `bs`, `up`, `down`, `left`,
// `right`, `home`, `end`, `pgup`, `pgdn`, `del`, `ins`). `C-x` and `ctrl-x`
// are the same spec, in either case, because a config file is written by
// hand and a case rule nobody can remember is a rule that gets reported as
// a bug.
//
// MULTI-KEY CHORDS ARE `-`-separated TOO (`space-w`, `g-g`, `m-i-(`), which
// reads the way the plan's §4 table writes them. The one spec that cannot be
// spelled that way is a literal `-` character: `-` is the separator, so a
// config cannot bind a bare hyphen. That limitation is stated here rather
// than silently mis-parsing the row.
//
// THE MODIFIER IS PEELED OFF BEFORE THE SPLIT, and it has to be: `A-j` is ONE
// key whose own spelling contains the separator, so splitting first reads it
// as the two-key chord `a` then `j` -- a binding that loads with no problem
// line and then fires on the wrong keys. `Config.parse_key_spec` therefore
// consumes a leading modifier itself and splits only the remainder, applying
// the modifier to the tail's keys.

/// Parse one key spec (`A-j`, `space`, `g-g`) into the key sequence it names,
/// or `none` when a key in it is not a key this editor has.
///
/// THE WHOLE SPEC IS REJECTED, never partially: a binding that silently
/// dropped its second key would fire on the first, which is a worse failure
/// than a row that does not load.
pub def Config.parse_key_spec (spec : String) : Option (List Key) :=
    let low : String := String.to_lowercase spec in
    match parse_prefix_modifier low {
        Option.some peeled => peel_and_parse peeled,
        Option.none => parse_seq (String.split low "-")
    }

/// A spec that OPENS with a modifier, as `(modifier, text after it)`: `A-j`
/// peels to `("alt", "j")`, `ctrl-space` to `("ctrl", "space")`. `none` when
/// the spec opens with neither form.
///
/// WHY THE HEAD AND NOT EACH PART: `-` is both the chord separator and part of
/// the modifier's own spelling, so a per-part reading of `A-j` cannot tell the
/// two apart and answers the chord `[a, j]`. Peeling first leaves only real
/// separators in the tail.
def parse_prefix_modifier (low : String) : Option (Pair String String) :=
    if String.starts_with "ctrl-" low
    then Option.some (Pair.pair "ctrl" (String.drop 5 low))
    else peel_alt low

/// The `alt-`/`a-` forms, tried after `ctrl-`.
def peel_alt (low : String) : Option (Pair String String) :=
    if String.starts_with "alt-" low
    then Option.some (Pair.pair "alt" (String.drop 4 low))
    else peel_single low

/// The one-letter forms (`c-x`, `a-j`), which the plan's §4 table uses. A LONE
/// `c`/`a` stays a character key: the form always has a NON-EMPTY tail after
/// the dash, and `single_modifier` is what requires it.
def peel_single (low : String) : Option (Pair String String) :=
    if Bool.not (String.length low > 2)
    then Option.none
    else if String.get low 1 != Option.some 0x2du8
    then Option.none
    else single_modifier (String.slice low 0 1) (String.drop 2 low)

/// `head` as a one-letter modifier over `rest`, or `none` when `head` is
/// neither letter or `rest` is empty.
def single_modifier (head : String) (rest : String) : Option (Pair String String) :=
    if String.is_empty rest
    then Option.none
    else if is_ctrl_part head
    then Option.some (Pair.pair "ctrl" rest)
    else if is_alt_part head
    then Option.some (Pair.pair "alt" rest)
    else Option.none

/// Apply a peeled modifier to the rest of the spec: parse the tail as a plain
/// spec, then put the modifier on every key of it.
///
/// THE MODIFIER APPLIES TO THE TAIL'S KEYS, all of them. A tail that is itself
/// a chord (`ctrl-g-g`) is therefore that chord with Ctrl on both, which is
/// what a user typing it means -- there is no reading in which a modifier
/// covers only some of the keys it was written in front of.
def peel_and_parse (peeled : Pair String String) : Option (List Key) :=
    match peeled {
        Pair.pair mod tail =>
            match parse_seq (String.split tail "-") {
                Option.none => Option.none,
                Option.some ks => Option.some (List.map (apply_modifier mod) ks)
            }
    }

/// One key with `mod` applied. A non-character key (a named key, an arrow)
/// cannot carry a modifier in this editor's `Key` type, so it is returned
/// unchanged rather than silently dropped.
pub def apply_modifier (mod : String) (k : Key) : Key :=
    match k {
        Key.char c => if String.beq mod "ctrl" then Key.ctrl c else Key.alt c,
        Key.escape => Key.escape,
        Key.enter => Key.enter,
        Key.tab => Key.tab,
        Key.backspace => Key.backspace,
        Key.up => Key.up,
        Key.down => Key.down,
        Key.left => Key.left,
        Key.right => Key.right,
        Key.home => Key.home,
        Key.end => Key.end,
        Key.page_up => Key.page_up,
        Key.page_down => Key.page_down,
        Key.delete => Key.delete,
        Key.insert => Key.insert,
        Key.function_key n => Key.function_key n,
        Key.ctrl c => Key.ctrl c,
        Key.alt c => Key.alt c
    }

/// The sequence a spec's parts name, or `none` if any part is not a key. An
/// empty spec (`""`, or `"a-"`) is `none`: a binding with no keys could never
/// be typed, so accepting it would only hide the typo.
///
/// THE EMPTY-PARTS CASE IS SUCCESS, and it has to be: `parse_seq` is called on
/// the TAIL of the part list, so the recursion always ends here. Answering
/// `none` would reject every spec there is -- including `"j"`, whose single
/// part is the whole of it -- while the tests that only assert the `none`
/// cases (`"j-"`, `"-j"`, `""`) went on passing. An empty spec still fails,
/// but in `parse_key`: `String.split "" "-"` is one empty piece, and that
/// piece is not a key.
#[terminating]
def parse_seq (parts : List String) : Option (List Key) :=
    match parts {
        List.empty => Option.some List.empty,
        List.cons one rest =>
            match parse_key one {
                Option.none => Option.none,
                Option.some k =>
                    match parse_seq rest {
                        Option.none => Option.none,
                        Option.some ks => Option.some (List.cons k ks)
                    }
            }
    }

/// One part of a split spec: a named key, or a single character. A modifier
/// never arrives here -- `Config.parse_key_spec` peels it off the spec's head
/// before any split (`parse_prefix_modifier`).
def parse_key (part : String) : Option Key :=
    parse_plain part

/// Is the modifier letter the control prefix? `c` or `C` (already lowered).
def is_ctrl_part (head : String) : Bool := String.beq head "c"

/// Is the modifier letter the alt prefix? `a`.
def is_alt_part (head : String) : Bool := String.beq head "a"

/// A part that is exactly one character is that character key; a named key
/// (`space`, `esc`, ...) is its own constructor; anything else is `none`.
def parse_plain (part : String) : Option Key :=
    match parse_named part {
        Option.some k => Option.some k,
        Option.none =>
            if I64.beq (String.length part) 1
            then Option.some (Key.char part)
            else Option.none
    }

/// The named keys, in the spelling a config file writes. The names follow the
/// plan's §4 table (`space`, `esc`) where it names one, and the view's own
/// `ply_key_name` spelling (`<enter>`, `<pgup>`) is deliberately NOT reused:
/// a config is written by a human, and `enter` is what a human writes.
def parse_named (part : String) : Option Key :=
    if String.beq part "space" then Option.some (Key.char " ")
    else if String.beq part "esc" then Option.some Key.escape
    else if String.beq part "escape" then Option.some Key.escape
    else if String.beq part "enter" then Option.some Key.enter
    else if String.beq part "return" then Option.some Key.enter
    else if String.beq part "tab" then Option.some Key.tab
    else if String.beq part "bs" then Option.some Key.backspace
    else if String.beq part "backspace" then Option.some Key.backspace
    else if String.beq part "up" then Option.some Key.up
    else if String.beq part "down" then Option.some Key.down
    else if String.beq part "left" then Option.some Key.left
    else if String.beq part "right" then Option.some Key.right
    else if String.beq part "home" then Option.some Key.home
    else if String.beq part "end" then Option.some Key.end
    else if String.beq part "pgup" then Option.some Key.page_up
    else if String.beq part "pgdn" then Option.some Key.page_down
    else if String.beq part "del" then Option.some Key.delete
    else if String.beq part "ins" then Option.some Key.insert
    else Option.none

// ── A config file's rows ──────────────────────────────────────────────────

/// What a `ply.toml` said: the binding rows, and the lines that were dropped
/// because they named something this editor does not have.
///
/// THE DROPPED LINES ARE PART OF THE ANSWER, not a debug detail. A config
/// that silently ignored `"A-j" = "join_selections"` would leave a user
/// believing the key was bound; the editor's status line says which lines
/// were dropped, so "my config does nothing" has an answer.
pub struct Config {
    /// The binding rows, in file order (a later row overrides an earlier one,
    /// which is the keymap's LAST-match rule).
    bindings : List Binding,
    /// One line per row that could not be used: the key it names, or why the
    /// row is not a binding at all.
    problems : List String
}

/// The empty config: no rows, nothing to report. The answer for a missing
/// file, so a caller never needs a special case for "no ply.toml".
pub def Config.empty : Config :=
    { bindings := List.empty, problems := List.empty }

/// `Config` is a small immutable record over persistent lists -- read several
/// times per fold step (its rows, its problems) -- so a duplicate of the VALUE
/// is the correct duplicate. The same reading `Copy RowView` records
/// (`view.mo`) and `Copy Rope` (`rope.mo`): nothing here mutates in place, and
/// field-wise copies keep the two owners from aliasing a list cell.
pub instance Copy Config {
    def copy (c : Config) : Pair Config Config :=
        match c {
            { bindings, problems } =>
                let one : Config := { bindings := cp_bindings bindings, problems := cp_strs problems } in
                let two : Config := { bindings := cp_bindings bindings, problems := cp_strs problems } in
                Pair.pair one two
        }
}

/// Field-wise binding copy, so a duplicated config owns its own list cells.
#[terminating]
def cp_bindings (bs : List Binding) : List Binding :=
    match bs {
        List.empty => List.empty,
        List.cons one rest => List.cons one (cp_bindings rest)
    }

/// Field-wise string copy, for the same reason.
#[terminating]
def cp_strs (ss : List String) : List String :=
    match ss {
        List.empty => List.empty,
        List.cons one rest => List.cons one (cp_strs rest)
    }

/// The config's binding rows, read once.
pub def Config.bindings_of (c : Config) : List Binding :=
    match c { { bindings, .. } => bindings }

/// The config's dropped lines, read once.
pub def Config.problems_of (c : Config) : List String :=
    match c { { problems, .. } => problems }

/// A config file's text as a `Config`. A parse failure is one problem line
/// and no rows: a config that cannot be read is exactly a config that binds
/// nothing, and the user has to be told which one it was.
pub def Config.parse (text : String) (source : String) : Config :=
    match Toml.parse text {
        Result.err e => { bindings := List.empty,
            problems := List.cons (source ++ ": " ++ Toml.ParseError.to_string e) List.empty },
        Result.ok root => rows_of_root root source
    }

/// Every `[keys.<mode>]` table in the file, in that order. Each row of each
/// table is one binding.
///
/// ONLY `keys` IS READ TODAY. The plan's §3 sketch also mentions options
/// (a tab width, a wrap toggle); a key nothing consults is worse than a key
/// that is absent, because it silently does nothing -- so an `[options]`
/// table is a row this module will grow when something reads it.
def rows_of_root (root : BTreeMap String Toml.Value) (source : String) : Config :=
    match Toml.table_get "keys" root {
        Option.none => Config.empty,
        Option.some keys_value => keys_of keys_value source
    }

/// The `[keys]` table: one sub-table per mode table name.
def keys_of (value : Toml.Value) (source : String) : Config :=
    match Toml.get_table value {
        Result.err _ => { bindings := List.empty,
            problems := List.cons (source ++ ": [keys] must be a table") List.empty },
        Result.ok modes => fold_modes (BTreeMap.to_list modes) source Config.empty
    }

/// Fold each mode's table over the config, in the file's key order (the map
/// is a B-tree, so the order is stable across runs -- a config fixture's
/// expectations do not depend on hash order).
#[terminating]
def fold_modes (modes : List (Pair String Toml.Value)) (source : String) (acc : Config)
    : Config :=
    match modes {
        List.empty => acc,
        List.cons one rest =>
            match one {
                Pair.pair mode value =>
                    fold_modes rest source (add_mode mode value source acc)
            }
    }

/// One mode's table: each (key spec, command name) row becomes a `Binding`
/// whose `mode` is THIS table's name.
def add_mode (mode : String) (value : Toml.Value) (source : String) (acc : Config) : Config :=
    match Toml.get_table value {
        Result.err _ =>
            { bindings := Config.bindings_of acc,
                problems := List.append (Config.problems_of acc)
                    (List.cons (source ++ ": [keys." ++ mode ++ "] must be a table") List.empty) },
        Result.ok rows => fold_rows mode (BTreeMap.to_list rows) source acc
    }

/// Fold one mode's rows over the config.
#[terminating]
def fold_rows (mode : String) (rows : List (Pair String Toml.Value)) (source : String)
    (acc : Config) : Config :=
    match rows {
        List.empty => acc,
        List.cons one rest =>
            match one {
                Pair.pair spec value =>
                    fold_rows mode rest source (add_row mode spec value source acc)
            }
    }

/// One row: a key spec and a command name, or a problem line naming what was
/// wrong. The command name is NOT checked against the registry here -- this
/// module does not import `commands.mo` (the registry is the other side of
/// the layering, and a config may legitimately name a command a later phase
/// adds). An unknown name is reported by `run_command` the first time the key
/// is pressed, which is where a user can see the status line.
def add_row (mode : String) (spec : String) (value : Toml.Value) (source : String)
    (acc : Config) : Config :=
    match Config.parse_key_spec spec {
        Option.none =>
            { bindings := Config.bindings_of acc,
                problems := List.append (Config.problems_of acc)
                    (List.cons (row_label source mode spec "not a key this editor has") List.empty) },
        Option.some keys =>
            match Toml.get_string value {
                Result.err _ =>
                    { bindings := Config.bindings_of acc,
                        problems := List.append (Config.problems_of acc)
                            (List.cons (row_label source mode spec "the command must be a string")
                                List.empty) },
                Result.ok command =>
                    { bindings := List.append (Config.bindings_of acc)
                        (List.cons (mk_binding mode keys command) List.empty),
                        problems := Config.problems_of acc }
            }
    }

/// One binding, built here so the record literal is never in an argument
/// position (the two-host inference gotcha).
def mk_binding (mode : String) (keys : List Key) (command : String) : Binding :=
    { mode := mode, keys := keys, command := command }

/// A problem line's text: the source, the table, the key and the reason, so
/// the status line can name the exact row a user has to fix.
def row_label (source : String) (mode : String) (spec : String) (why : String) : String :=
    source ++ ": [keys." ++ mode ++ "] " ++ spec ++ ": " ++ why

// ── Layering ──────────────────────────────────────────────────────────────

/// Two configs, `later` winning per key: the rows concatenate (the keymap
/// keeps the LAST match, so the later layer overrides) and the problems
/// concatenate.
///
/// THIS IS THE WHOLE MERGE. The plan's "merged per key the way Weaver merges
/// settings" needs no per-key fold, because a binding table's resolution
/// already has the override rule; deleting the shadowed row would be a second
/// implementation of it.
pub def Config.merge (earlier : Config) (later : Config) : Config :=
    // Each config is read twice (its rows, its problems), so both go through
    // one `Shared` handle -- the affine rule's own remedy.
    let shared_e : Shared Config := Shared.of earlier in
    let shared_l : Shared Config := Shared.of later in
    { bindings := List.append (Config.bindings_of (Shared.get shared_e))
        (Config.bindings_of (Shared.get shared_l)),
        problems := List.append (Config.problems_of (Shared.get shared_e))
            (Config.problems_of (Shared.get shared_l)) }

/// A list of configs' rows in one step, in the order given (so the last one
/// wins). `Config.default_bindings`'s companion: the defaults are the FIRST
/// layer, so a config row shadows a default without replacing it.
#[terminating]
pub def Config.bindings_of_all (cs : List Config) : List Binding :=
    match cs {
        List.empty => List.empty,
        List.cons one rest =>
            List.append (Config.bindings_of one) (Config.bindings_of_all rest)
    }

/// Every problem line from every layer, in layer order.
#[terminating]
pub def Config.problems_of_all (cs : List Config) : List String :=
    match cs {
        List.empty => List.empty,
        List.cons one rest =>
            List.append (Config.problems_of one) (Config.problems_of_all rest)
    }
