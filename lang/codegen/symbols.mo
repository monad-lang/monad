/// How a Monad name becomes an LLVM symbol.
///
/// `def_symbol_name` and `ref_symbol_name` are the load-bearing pair:
/// the name a def is DEFINED under and the name a REFERENCE to it
/// compiles a call to must agree exactly, and `compile_db_def_ir`'s own
/// comment records the link failure from the last time they diverged.
/// They live together, in one small module, so that they cannot drift
/// apart unnoticed again.
///
/// A symbol is the def's fully qualified source name verbatim
/// (`lang.typecheck.infer::inductive_bare_name`) -- see
/// `lang.codegen.qualify` for where the `module::name` form comes from,
/// and `def_symbol_name` for why nothing is mangled into underscores
/// any more.
use lang.types {Identifier, ModulePath, show_module_path}
use std.map {}

/// A genuine, previously-undiscovered bug lived here (and in
/// `string_find_last_loop` below) until this session: `String.slice`'s
/// own signature (`init/string.mo`) is `(s, start, LEN)` -- a LENGTH,
/// not an end index -- but both call sites here passed `String.length
/// name` (the WHOLE string's own length, an end-index-shaped value) as
/// the LEN argument, silently reading past the intended suffix's real
/// length. Latent/unnoticed for a long time because `constructor_tag`'s
/// own "check qualified names first" tier (whole-string comparisons
/// against `"IO.io"`/`"Unit.unit"`/... ) never needed this "base name"
/// fallback tier to work correctly for any of the ~16 hardcoded
/// builtins; only surfaced once the new dynamic `ctor_tags` fallback
/// (`build_constructor_tag_map`) started relying on `extract_base_name`
/// actually stripping a qualifier correctly. Confirmed via an isolated
/// unit test bypassing the whole self-hosted pipeline: `extract_base_
/// name "Option.Some"` returned `"Option.Some"` unchanged (the `last_dot
/// > -1` branch's own slice never actually fired due to `string_find_
/// last`'s OWN identical bug below, so this line's fix matters once that
/// one is fixed too).
#[partial]
def extract_base_name (name : String) : String :=
    let last_dot := string_find_last name "." in
    if I64.gt last_dot (-1)
    then String.slice name (last_dot + 1) (String.length name - last_dot - 1)
    else name

/// An identifier as it should appear in a generated LLVM symbol name:
/// the raw text with any `'` quote characters stripped.
///
/// Named `symbol_identifier`, NOT `show_identifier`: this file used to
/// import `lang.types`' own `show_identifier` (which returns the text
/// verbatim, quotes included) while also defining this one, and since the
/// global name table is not module-scoped the two collided -- which one
/// each call site actually got was decided by registration order, even
/// though they produce DIFFERENT strings. See AGENTS.md item 18.
#[partial]
def symbol_identifier (id : Identifier) : String := match id {
    Identifier.id s => remove_quotes_from_identifier s,
}

#[partial]
def remove_quotes_from_identifier (s : String) : String := 
    remove_quotes_loop s ""

#[partial]
def remove_quotes_loop (s : String) (acc : String) : String :=
    if String.beq s "" then acc
    else
        let first_byte : U8 := match String.get s 0 {
            Option.some b => b,
            Option.none => 0u8
        } in
        let single_quote : U8 := 39u8 in
        // `String.slice`'s own third argument is a LENGTH, not an end
        // index (`init/string.mo` -- see `extract_base_name`'s own
        // already-fixed calls just above for the same story). These two
        // calls were still using the OLD, wrong convention
        // (`String.slice s 1 (String.length s)`, i.e. "take `length s`
        // characters starting at index 1" -- one character too many,
        // out of bounds by construction) -- confirmed live via a real
        // self-compiled binary's own SIGSEGV/stack-overflow: `String.
        // slice`'s out-of-bounds length request never actually SHRANK
        // `s` on the recursive call, so this looped effectively forever
        // (until the native stack overflowed, ~22700 frames deep in
        // `remove_quotes_loop` itself) instead of terminating once `s`
        // became empty.
        if U8.beq first_byte single_quote then
            remove_quotes_loop (String.slice s 1 (String.length s - 1)) acc
        else
            remove_quotes_loop (String.slice s 1 (String.length s - 1)) (String.concat acc (String.slice s 0 1))

/// Find the last occurrence of a substring in a string, return its index or -1
#[partial]
def string_find_last (haystack : String) (needle : String) : I64 :=
    if String.beq needle "" then -1
    else if I64.gt (String.length needle) (String.length haystack) then -1
    else string_find_last_loop haystack needle (String.length haystack - String.length needle)

/// `String.slice`'s own third argument is a LENGTH (`init/string.mo`),
/// not an end index -- see `extract_base_name`'s own doc comment for
/// the full story on this bug (fixed alongside it here).
#[partial]
def string_find_last_loop (haystack : String) (needle : String) (start_idx : I64) : I64 :=
    if I64.lt start_idx 0 then -1
    else if String.beq (String.slice haystack start_idx (String.length needle)) needle then start_idx
    else string_find_last_loop haystack needle (start_idx - 1)

#[partial]
def module_path_to_str (mp : ModulePath) : String := match mp {
    ModulePath.mp ids => mangle_identifiers ids,
}

/// Join a module path's segments with `__` for use in an LLVM symbol
/// name (`Foo.bar` -> `Foo__bar`).
///
/// Named `mangle_identifiers`, NOT `join_identifiers`: `lang/types.mo`
/// exports its own `join_identifiers` that joins with `.` instead, and
/// this file IMPORTS that one (see the `use lang.types` list above).
/// Since the global name table is not module-scoped, the two collided
/// and which one `module_path_to_str` actually called was decided by
/// registration order -- a real hazard, since the two produce different
/// symbol names. See AGENTS.md item 18.
#[partial]
def mangle_identifiers (ids : List Identifier) : String :=
    List.intercalate "__" (List.map symbol_identifier ids)

/// The LLVM symbol a top-level `def` is emitted under, and the symbol a
/// REFERENCE to one compiles a call to. These two must agree exactly --
/// `compile_db_def_ir`'s own comment records the link failure from the
/// last time they diverged (a dotted name like `Option.get_or_default`
/// defining itself one way while every call site spelled it another).
/// Keeping them as a pair, in one place, is the guard against a repeat:
/// there is no second spelling of this derivation anywhere.
/// The symbol is the source name VERBATIM -- no flattening of `.` to
/// `_`, which was itself lossy: it made `String.a` and `String_a` the
/// same symbol, and `mangle_identifiers`' `__` join likewise conflates
/// `mp [a, b]` with `mp [a__b]`. Neither pair collides in today's
/// corpus (4271 distinct def names, checked), but qualifying every def
/// with its module path multiplies the opportunities, and conflating
/// two distinct names is precisely the bug class this whole change
/// exists to remove. `lang.codegen.ir`'s `llvm_symbol_ref` quotes every
/// emitted `@` reference so a dotted name needs no escaping.
#[partial]
def def_symbol_name (name : ModulePath) : String :=
    show_module_path name

/// Reference-side counterpart to `def_symbol_name` -- see there.
#[partial]
def ref_symbol_name (id : Identifier) : String :=
    symbol_identifier id

/// Replace dots with underscores in a string for use as LLVM identifier
#[partial]
def replace_dots_with_underscores (s : String) : String := 
    replace_dots_loop s ""

#[partial]
def replace_dots_loop (s : String) (acc : String) : String := 
    if String.beq s "" then acc
    else
        let first_char : U8 := match String.get s 0 {
            Option.some b => b,
            Option.none => 0u8
        } in
        let rest := String.slice s 1 (String.length s - 1) in
        let dot_byte : U8 := 46u8 in  // '.' character
        if U8.beq first_char dot_byte then
            replace_dots_loop rest (String.concat acc "_")
        else
            replace_dots_loop rest (String.concat acc (String.slice s 0 1))

/// Check if a function name is a main function (handles both "main" and module_main)
#[partial]
def ends_with_main (name : String) : Bool :=
    // On the UNQUALIFIED tail: a symbol is `lang.main::main` now, which
    // ends in neither `main`-the-whole-string nor `_main`.
    let src := unqualify_def_name name in
    if String.beq src "main" then true
    else if String.length src > 3 then
        let suffix := String.slice src (String.length src - 3) (String.length src) in
        String.beq suffix "_main"
    else false

/// The source name inside a qualified symbol -- `init.string::String.beq`
/// back to `String.beq`. A name that was never qualified (a synthesized
/// or already-flat one) comes back unchanged, so this is safe to apply
/// anywhere a source-level name is wanted.
#[partial]
def unqualify_def_name (s : String) : String :=
    let idx := string_find_qualifier_sep s 0 (String.length s) in
    if I64.beq idx (0 - 1) then s else String.slice s (idx + 2) (String.length s - idx - 2)

#[partial]
def string_find_qualifier_sep (s : String) (i : I64) (n : I64) : I64 :=
    if I64.gt (i + 2) n then (0 - 1)
    else if String.beq (String.slice s i 2) "::" then i
    else string_find_qualifier_sep s (i + 1) n

#[partial]
def bare_modpath (name : String) : ModulePath :=
    ModulePath.mp (List.cons (Identifier.id name) List.empty)