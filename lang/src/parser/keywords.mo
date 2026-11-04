/// Monad's reserved words, and the membership test over them.
///
/// Split out of `parser/core.mo` for the reason `op_table.mo` gives: the list
/// below is a fact about this language, not about parsing. `is_keyword` lives
/// here too, rather than in `char_preds.mo` with the other predicates -- it is
/// the one "predicate" that is really a grammar lookup, and keeping it beside
/// the list is what lets `char_preds.mo` import nothing from here.

/// `pub`/`priv` are missing here even though `vis_parser` treats both
/// as real keywords elsewhere (`tag "pub"`/`tag "priv"` before a
/// `def`/`type`/`class`/.../ declaration) -- the general `identifier`
/// parser (used everywhere a bare identifier can appear, including
/// `expr_climb_rest`'s own "one more application argument" attempt)
/// happily accepts them as ordinary identifiers instead of rejecting
/// them, so a preceding expression with nothing to naturally stop it
/// (no comma, no operator) swallows the NEXT declaration's own leading
/// `pub`/`priv` as a bogus extra argument -- the exact same failure
/// mode `c1ed034`/this session's own `expr_climb_op` fix already cover
/// for other triggers, just never closed for these two specific words.
/// Confirmed live via the full `cli/src/main.mo` self-compile:
/// `lang/parser/core.mo`'s own `op_chars : List String := [...]`
/// (immediately followed by `pub def op_table : List OpEntry := ...`,
/// no comment, nothing unusual) got its list literal miscompiled into
/// applying the whole list to `pub`'s own (garbage) value instead of
/// returning it -- `llc: undefined value '@pub'` once at codegen, but
/// this was ALREADY silently wrong under the tree-walking interpreter
/// too (this bug doesn't need LLVM to manifest, just never surfaced
/// because nothing exercised `op_chars`'s own value end-to-end before).
/// Mirrors the Rust reference's own `RESERVED_KEYWORDS`, which already
/// includes `pub`/`priv` (fixed there in an earlier session) -- this
/// self-hosted `kw_list` is a wholly separate, independent parser
/// implementation that was never given the same fix.
///
/// `as` is NOT included here despite having the identical `tag "as"`
/// shape (`use X as Y` renames) -- unlike `pub`/`priv`, `as` is also
/// used pervasively as an ordinary bound variable name throughout this
/// corpus (`lang/types.mo`'s own `Identifier.id as => ...`, `String.beq
/// as bs`), so reserving it globally breaks far more than it fixes.
/// Confirmed as a real regression from an earlier version of this same
/// fix that included `as`: `lang/types.mo`/`codegen/emit.mo` (both
/// bind fields to a local literally named `as`) went from parsing fine
/// to truncating entirely.
def kw_list : List String :=
	["def", "let", "in", "use", "open", "class", "struct", "instance",
	 "type", "fn", "match", "if", "then", "else", "infix",
	 "do", "return", "for", "quote", "with", "defmacro",
	 "pub", "priv"]


#[partial]
def kw_member (s : String) (kws : List String) : Bool := 
	match kws {
		List.cons kw rest => if String.beq kw s then true else kw_member s rest,
		List.empty => false
		}


/// Is this identifier one of the words above? Moved here from
/// `char_preds.mo`, whose remaining predicates are all character classes.
#[partial]
def is_keyword (s : String) : Bool :=
	kw_member s kw_list
