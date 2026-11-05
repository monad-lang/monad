/// `fmt!` — efficient, Lean-style format strings, built entirely here in
/// Monad on top of the `meta!` intrinsic (`init/meta.mo`'s value types plus
/// `rust/core/src/eval/macro_expand.rs`). No new compiler intrinsic exists
/// for formatting: `fmt!` is an ordinary `defmacro` whose body is one
/// `meta!` call, and everything format-specific is pure Monad code that
/// runs at EXPANSION time, not at run time.
///
/// ## Calling convention: in-string variable references only
///
/// Like Lean's `s!"..."`/`format!`, the interpolation holes name variables
/// that must ALREADY be in scope at the call site — `fmt!` takes exactly
/// ONE argument (the format string):
///
/// ```monad
/// def greet (name : String) (n : I64) : String :=
///     fmt! "hi {name}, you are {n:>4}"
/// ```
///
/// expands to roughly
///
/// ```monad
/// String.concat_list ["hi ", FmtDisplay.fmt_display name, ", you are ",
///                     Format.apply_align (FormatAlign.right 4)
///                         (FmtDisplay.fmt_display n)]
/// ```
///
/// — one allocation, direct `FmtDisplay` calls, and no runtime parsing of
/// the template. The expansion introduces NO binders: each hole is the
/// call site's own variable, and the surrounding `def`/`fn` that already
/// binds it is the only binder involved. That is why an out-of-scope hole
/// is an ordinary unbound-variable error at the call site, and why the
/// macro has nothing to capture with.
///
/// ## The pieces
///
/// - `FormatPiece` — the parsed template: literal text, or one hole with
///   its own spec.
/// - `Format.parse` — one left-to-right byte pass over the template.
/// - `Format.emit` — the `Expr` that builds the result string.
/// - `fmt_meta` — their composition, `String -> Expr`, called by `meta!`.
///
/// ## Hygiene
///
/// `Format.emit` builds a CORE `Expr` (`init/meta.mo`), so each hole's
/// `e_var` names the call site's own binder directly. Since the expansion
/// introduces NO binders at all, a call site that already binds `name`
/// keeps ITS binding — there is no new scope to capture anything in.
/// `Format.emit`'s own helper binders never reach the output.
///
/// ## Scope
///
/// `{name}`, `{name:>N}`, `{name:^N}` and `{{`/`}}` escapes. A hole must
/// NAME a variable: `{}`/`{:>N}` have nothing to refer to
/// (there is no positional argument to fall back on) and are rejected at
/// expansion time. Fill characters, `{:x}`/`{:o}`/`{:b}`/`{:?}` and
/// precision are deliberately out: each needs a per-type instance or a
/// second class, and none has a caller yet. An unsupported `:spec` is a
/// COMPILE error, not a silent pass-through — see `Format.parse`.

use init::meta {Expr}

open Expr {e_var, e_str, e_int, e_app, e_error}

/// One hole's alignment, with the width it pads to. `width` counts the
/// display string's own BYTES (`String.length` is byte-oriented), so
/// `{n:>4}` on `"ab"` yields `"  ab"`; a multi-byte character counts once
/// per byte, not once per column.
pub type FormatAlign {
    left,
    right (width : I64),
    centre (width : I64)
}

/// One piece of a parsed format template: literal text, or one
/// interpolation hole carrying the variable's name and its alignment.
pub type FormatPiece {
    literal (text : String),
    hole (name : String) (align : FormatAlign),
}

/// The constructors this module both builds and matches on, bound by their
/// bare names — the house convention for a type whose cases are used as
/// constructors in code (`open Bool {and, false, not, or, true}`,
/// `open Result {err, ok}`) rather than only as patterns. Declaring a
/// constructor is not enough to make it usable unqualified in an
/// expression; without this, `ok left` and `hole name align` are unbound.
open FormatPiece {literal, hole}
open FormatAlign {left, right, centre}

/// How one value is rendered by a `fmt!` hole.
///
/// A separate class from `ToString` rather than reusing it, because a
/// format hole is allowed to render differently from `to_string` (padding,
/// later specifiers, `Debug`-style quoting) and a type may reasonably want
/// one without the other. The blanket instance below makes every `ToString`
/// type work in a hole with no extra declaration; a type that wants its own
/// hole rendering declares `FmtDisplay` alone.
pub class FmtDisplay A {
    def fmt_display (a : A) : String
}

/// Every `ToString` type is displayable in a hole. This is what lets
/// `"{}" <n>"` work for `I64`/`U64`/`F64`/`String` and every existing
/// `ToString` instance without touching them.
pub instance [ToString A] FmtDisplay A {
    def fmt_display (a : A) : String := ToString.to_string a
}

/// `Bool` has no `ToString` instance (its only rendering used to be
/// `Debug`'s), so the blanket instance above cannot reach it. Declared here
/// rather than in `init/number.mo`/`string.mo` because formatting is what
/// needs it: `fmt! "{flag}"` on a `Bool` must not be "no instance" error.
pub instance ToString Bool {
    def to_string (b : Bool) : String :=
        if b then "true" else "false"
}

/// Pad `s` to `width` characters with spaces on the left
/// (`Format.pad_left "ab" 4` is `"  ab"`). A string already at or beyond
/// `width` is returned unchanged — a format width is a MINIMUM, never a
/// truncation.
pub def Format.pad_left (s : String) (width : I64) : String :=
    let pad := I64.sub width (String.length s) in
    if I64.gt pad 0 then String.concat (Format.spaces pad) s else s

/// Pad `s` to `width` with spaces on the right. See `Format.pad_left`.
pub def Format.pad_right (s : String) (width : I64) : String :=
    let pad := I64.sub width (String.length s) in
    if I64.gt pad 0 then String.concat s (Format.spaces pad) else s

/// Pad `s` to `width` with spaces split between both sides, the extra one
/// (an odd count) on the right. See `Format.pad_left`.
pub def Format.pad_centre (s : String) (width : I64) : String :=
    let pad := I64.sub width (String.length s) in
    if I64.gt pad 0 then
        let left := I64.div pad 2 in
        let right := I64.sub pad left in
        String.concat (Format.spaces left) (String.concat s (Format.spaces right))
    else s

/// `n` spaces; `""` for `n <= 0`.
#[terminating]
pub def Format.spaces (n : I64) : String :=
    if I64.lt n 1 then "" else String.concat " " (Format.spaces (I64.sub n 1))

/// Apply one hole's alignment to an already-rendered value.
pub def Format.apply_align (align : FormatAlign) (s : String) : String :=
    match align {
        left => s,
        right width => Format.pad_left s width,
        centre width => Format.pad_centre s width,
    }

/// The `Expr` for one piece: literal text becomes `e_str`, a hole becomes
/// its display call (padded only when it has a width) — the class method
/// applied directly to the call site's own variable, with no intermediate
/// `to_string` call and no runtime template walking.
pub def Format.emit_piece (piece : FormatPiece) : Expr :=
    match piece {
        literal text => e_str text,
        hole name align => Format.emit_hole name align,
    }

/// One hole's whole `Expr`. A bare `{name}` is JUST the display call — the
/// common case pays no padding call at all; only `:>N`/`:^N` wrap it in
/// `Format.apply_align`.
///
/// `FormatAlign.right`/`.centre` are qualified `e_var`s applied with
/// `e_app` — the same `e_ctor`-free spelling `std/derive.mo` uses for
/// constructors it applies, which the checker instantiates correctly where
/// a raw `Con` node would not. (The arm rebuilds the constructor from its
/// own field rather than reusing `align`: an unannotated binder may be
/// used only once, and the scrutinee already counts as one use.)
def Format.emit_hole (name : String) (align : FormatAlign) : Expr :=
    match align {
        left => Format.display_expr name,
        right width =>
            e_app (e_app (e_var "Format.apply_align")
                (e_app (e_var "FormatAlign.right") (e_int width)))
                (Format.display_expr name),
        centre width =>
            e_app (e_app (e_var "Format.apply_align")
                (e_app (e_var "FormatAlign.centre") (e_int width)))
                (Format.display_expr name),
    }

/// `FmtDisplay.fmt_display <name>` — the value a hole displays.
def Format.display_expr (name : String) : Expr :=
    e_app (e_var "FmtDisplay.fmt_display") (e_var name)

/// Every piece's `Expr`, in template order.
pub def Format.emit_pieces (pieces : List FormatPiece) : List Expr :=
    match pieces {
        empty => List.empty,
        cons p rest => List.cons (Format.emit_piece p) (Format.emit_pieces rest),
    }

/// Fold a list of `Expr`s into one `List`-building `Expr` — the emitted
/// code's `[...]` argument to `String.concat_list`. Built as `List.cons`
/// cells because `init/meta.mo`'s `Expr` has no list literal.
pub def Format.emit_list (items : List Expr) : Expr :=
    match items {
        empty => e_var "List.empty",
        cons hd tl => e_app (e_app (e_var "List.cons") hd) (Format.emit_list tl),
    }

/// `Format.emit` — the whole template as ONE `Expr`
/// (`String.concat_list <pieces>`), which the macro emits once per call.
pub def Format.emit (pieces : List FormatPiece) : Expr :=
    e_app (e_var "String.concat_list") (Format.emit_list (Format.emit_pieces pieces))

// ── Parsing ─────────────────────────────────────────────────────────────
//
// One left-to-right pass over the template's BYTES (`String.get` is an
// O(1) byte read; `String.get_char` decodes the whole string per call and
// is unusable for scanning -- AGENTS.md). `String.slice` is byte-oriented
// and returns "" for a mid-character offset, so literal runs are cut at
// bytes this scanner has already proved are ASCII delimiters (`{`/`}` are
// 0x7B/0x7D, both below 0x80), never at an arbitrary index.

/// `{`, `}`, `:`, `>` and `^` as bytes -- all below 0x80, so a scan that
/// only ever cuts at one of them can never split a UTF-8 character.
def byte_lbrace : U8 := 123u8
def byte_rbrace : U8 := 125u8
def byte_colon : U8 := 58u8
def byte_gt : U8 := 62u8
def byte_caret : U8 := 94u8

/// The byte at `i`, or 0 when out of range (0 is never a delimiter this
/// scanner looks for, so an out-of-range read simply fails every test).
def byte_at (s : String) (i : I64) : U8 :=
    match String.get s i {
        some b => b,
        none => 0u8,
    }

/// Whether `s` starts with `{` at `i` -- i.e. a hole or an escape.
def is_lbrace_at (s : String) (i : I64) : Bool :=
    U8.beq (byte_at s i) byte_lbrace

def is_rbrace_at (s : String) (i : I64) : Bool :=
    U8.beq (byte_at s i) byte_rbrace

/// Scan forward from `i` to the next `{` or `}`, returning its index (or
/// the string's length when the run reaches the end).
#[terminating]
def scan_literal (s : String) (i : I64) (len : I64) : I64 :=
    if I64.gt i len then len
    else if is_lbrace_at s i then i
    else if is_rbrace_at s i then i
    else scan_literal s (I64.add i 1) len

/// Index just past the `}` closing the hole that opens at `i`, or `-1` if
/// the template ends first.
#[terminating]
def scan_to_rbrace (s : String) (i : I64) (len : I64) : I64 :=
    if I64.gt i len then -1
    else if is_rbrace_at s i then I64.add i 1
    else scan_to_rbrace s (I64.add i 1) len

/// The identifier starting at `start` in `body` (a hole's inside text):
/// returns `(name, index just past it)`. An empty name is NOT a hole --
/// `Format.parse_hole` rejects it with the reason (there is no positional
/// argument for `{}` to mean).
#[terminating]
def scan_name (body : String) (start : I64) (len : I64) : Pair String I64 :=
    scan_name_at body start start len

#[terminating]
def scan_name_at (body : String) (start : I64) (i : I64) (len : I64) : Pair String I64 :=
    if I64.lt i len then
        let b := byte_at body i in
        if U8.beq b byte_colon then Pair.pair (String.slice body start (I64.sub i start)) i
        else scan_name_at body start (I64.add i 1) len
    else Pair.pair (String.slice body start (I64.sub len start)) len

/// Digits of a decimal width: `(width, index just past the digits)`. A
/// non-digit stops the scan (`width` is then 0), which is what makes a
/// trailing unknown specifier a parse error rather than a silent zero.
#[terminating]
def scan_digits (s : String) (i : I64) (len : I64) (acc : I64) : Pair I64 I64 :=
    if I64.lt i len then
        let d := I64.sub (U8.to_i64 (byte_at s i)) 48 in
        if I64.lt d 0 then Pair.pair acc i
        else if I64.gt d 9 then Pair.pair acc i
        else scan_digits s (I64.add i 1) len (I64.add (I64.mul acc 10) d)
    else Pair.pair acc i

/// One hole's alignment from its `:spec` text (the part after `:`).
///
/// Total by construction: `left` (no spec at all), `>N`/`^N` with a
/// positive width, and everything else is an `err` carrying the offending
/// spec so the author sees it. Being total is what lets `fmt_meta` promise
/// a compile-time error instead of emitting code that fails later.
pub def Format.parse_spec (spec : String) : Result String FormatAlign :=
    let len := String.length spec in
    if I64.beq len 0 then ok left
    else
        let first := byte_at spec 0 in
        if Bool.not (Bool.or (U8.beq first byte_gt) (U8.beq first byte_caret)) then
            err (String.concat "fmt!: unknown format spec `:"
                (String.concat spec "`"))
        else
            let scanned := scan_digits spec 1 len 0 in
            let width := match scanned { pair w _ => w } in
            let stop := match scanned { pair _ s => s } in
            if Bool.not (I64.beq stop len) then
                err (String.concat "fmt!: trailing characters after a width in `:"
                    (String.concat spec "`"))
            else if I64.lt width 1 then
                err (String.concat "fmt!: a format width must be at least 1, got `:"
                    (String.concat spec "`"))
            else if U8.beq first byte_gt then ok (right width)
            else ok (centre width)

/// Split one hole's inside text (`body`, the text between `{` and `}`, at
/// most `brace` bytes) into its name and alignment.
pub def Format.parse_hole (body : String) : Result String FormatPiece :=
    let len := String.length body in
    let scanned := scan_name body 0 len in
    let name := match scanned { pair n _ => n } in
    let stop := match scanned { pair _ s => s } in
    let spec :=
        if I64.beq stop len then ""
        // `stop` sits on the `:`; skip it.
        else String.slice body (I64.add stop 1) (I64.sub (I64.sub len stop) 1)
    in
    // `fmt!` takes exactly ONE argument — the template — so a hole CANNOT
    // mean "the single argument": an unnamed hole has nothing to refer to
    // (it would emit `e_var ""`, surfacing much later as `unbound variable
    // \`\``). Reject it at expansion time with the real reason.
    if String.is_empty name then err "fmt!: a hole must name a variable"
    else match Format.parse_spec spec {
        ok align => ok (hole name align),
        err message => err message,
    }

/// `Format.parse` -- split a template into its pieces.
///
/// `{name}`/`{name:>N}`/`{name:^N}` are holes — every hole
/// must name a variable; `{{` and `}}` are the literal brace characters.
/// An unterminated hole, an unnamed hole, an unknown spec or an unclosed
/// escape is an `err` carrying the reason (the offending spec, or the byte
/// offset for a brace error), so the expansion fails with a message naming
/// the author's own text rather than emitting broken code.
pub def Format.parse (template : String) : Result String (List FormatPiece) :=
    parse_pieces template 0 (String.length template) List.empty

/// Accumulates pieces in REVERSE (cheaper than appending) and reverses once
/// at the end.
#[terminating]
def parse_pieces (s : String) (i : I64) (len : I64) (acc : List FormatPiece)
    : Result String (List FormatPiece) :=
    // `i >= len`, NOT `i > len`: at `i == len` there is nothing left to
    // scan, and `scan_literal` would report `stop == i`, so an empty
    // literal would be appended and the same index re-scanned forever.
    if i >= len then ok (List.reverse acc)
    else if is_lbrace_at s i then
        if U8.beq (byte_at s (I64.add i 1)) byte_lbrace then
            // `{{` -> one literal `{`.
            parse_pieces s (I64.add i 2) len (List.cons (literal "{") acc)
        else
            let close := scan_to_rbrace s (I64.add i 1) len in
            if I64.lt close 0 then
                err (String.concat "fmt!: unclosed `{` at byte " (I64.to_string i))
            else
                let body := String.slice s (I64.add i 1) (I64.sub (I64.sub close 1) (I64.add i 1)) in
                match Format.parse_hole body {
                    ok piece => parse_pieces s close len (List.cons piece acc),
                    err message => err message,
                }
    else if is_rbrace_at s i then
        if U8.beq (byte_at s (I64.add i 1)) byte_rbrace then
            // `}}` -> one literal `}`.
            parse_pieces s (I64.add i 2) len (List.cons (literal "}") acc)
        else err (String.concat "fmt!: unmatched `}` at byte " (I64.to_string i))
    else
        let stop := scan_literal s i len in
        let text := String.slice s i (I64.sub stop i) in
        parse_pieces s stop len (List.cons (literal text) acc)

/// `fmt_meta` — the meta function `fmt!` hands its template to: `String ->
/// Expr`, the signature `meta!`'s subject/function pair requires. Both
/// parsing and emitting happen at EXPANSION time, so the call site pays
/// nothing for either: no template survives into the emitted code and no
/// piece count is walked at run time.
///
/// A malformed template reifies as `e_error`, which fails the expansion
/// with the message `Format.parse` produced — the author reads it at the
/// call site, and nothing is spliced in.
pub def fmt_meta (template : String) : Expr :=
    match Format.parse template {
        ok pieces => Format.emit pieces,
        err message => e_error message,
    }

// ── The macro ───────────────────────────────────────────────────────────

/// `fmt! "...{x}..."` — the format string as ONE argument.
///
/// `fmt_meta` lives in THIS module rather than beside the macro in a
/// second file, because `meta!` resolves its function argument against the
/// modules the calling file can reach: a file that imports only the macro
/// must also get the meta function, so one `use init::format {fmt}` has to
/// bring both. (`std/derive.mo` has the same shape — `derive_lens` and
/// `derive_lens_meta` in one file — for the same reason.)
///
/// `#[at term]` records that this macro is a TERM-position macro: its body
/// is a `quote` (an expression), so using it where a declaration belongs is
/// an error naming the macro rather than a puzzling "not a Term value"
/// failure. `#[returns expr]` states the same fact positively; the expander
/// checks it against the body form at this definition, so the two can never
/// drift apart.
#[at term]
#[returns expr]
defmacro fmt template := quote {
    meta! template fmt_meta
}
