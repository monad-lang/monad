// `Copy` instances for ply's value records.
//
// WHY THIS FILE EXISTS: `types.mo` holds the `#[derive BEq]` declarations,
// and a derive-bearing file must hold no function bodies -- the Rust
// host's meta-capture path re-checks it and loses def-signature expected
// types (`motes/tui/src/types.mo` records the rule this mote's scaffold
// inherited). An `instance` is a body, so the instances live here instead.
//
// WHY `Copy` AT ALL: these are immutable value records -- two or three
// `I64`s and a `String` -- the same shape as `motes/tui`'s `Rect`/
// `TextStyle`, which carry field-wise instances for exactly this reason.
// `Copy` licenses the checker to share a binder (the affine-by-default
// rule's one escape for a value whose duplicate IS the right duplicate);
// `init/src/copy.mo`'s own doctrine covers each one:
//
//   * `Selection`, `Change`: field-wise records of `Copy` fields, so a
//     duplicate is a copy of each field. Built by hand below, like
//     `tui`'s, because `#[derive Copy]` is not one of the derive macros
//     this repo has (`std/src/derive.mo` derives BEq/Lens/Show shapes).
//   * `Mode`: an enum whose payloads are `String`s (themselves `Copy`) and
//     `I64`s (scalars); the nullary form is a register move
//     (`motes/http`'s `Method` instance is the same reasoning), and a
//     payload form duplicates a pointer to immutable bytes.

use lib::types {Selection, Change, Mode}

pub instance Copy Selection {
    def copy (s : Selection) : Pair Selection Selection :=
        let one : Selection := { anchor := s.anchor, head := s.head } in
        let two : Selection := { anchor := s.anchor, head := s.head } in
        Pair.pair one two
}

pub instance Copy Change {
    def copy (c : Change) : Pair Change Change :=
        let one : Change := { start := c.start, stop := c.stop, text := c.text } in
        let two : Change := { start := c.start, stop := c.stop, text := c.text } in
        Pair.pair one two
}

pub instance Copy Mode {
    def copy (m : Mode) : Pair Mode Mode :=
        match m {
            Mode.normal => Pair.pair Mode.normal Mode.normal,
            Mode.insert => Pair.pair Mode.insert Mode.insert,
            Mode.select => Pair.pair Mode.select Mode.select,
            Mode.command line => Pair.pair (Mode.command line) (Mode.command line),
            Mode.search q => Pair.pair (Mode.search q) (Mode.search q),
            Mode.picker q sel => Pair.pair (Mode.picker q sel) (Mode.picker q sel)
        }
}
