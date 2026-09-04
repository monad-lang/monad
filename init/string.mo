
/// String functions

use math {}

#[native string_eq]
def String.beq (a b : String) : Bool

#[native string_concat]
def String.concat (a b : String) : String

#[native string_length]
def String.length (s : String) : I64

#[native string_to_lowercase]
def String.to_lowercase (s : String) : String

#[native string_slice]
def String.slice (s : String) (start : I64) (len : I64) : String

#[native string_drop]
def String.drop (n : I64) (s : String) : String

#[native string_starts_with]
def String.starts_with (prefix : String) (s : String) : Bool

#[native string_get]
def String.get (s : String) (i : I64) : Option U8

/// NOT USABLE FOR SCANNING -- see AGENTS.md's `Char` item.
/// `i` is a CHARACTER index, not a byte offset, and the native decodes
/// the whole string into a `Vec<char>` on EVERY call, so any per-character
/// loop built on this is quadratic. `lang/parser/combinators.mo`'s
/// `utf8_char_width` uses `String.get` (an O(1) byte read) for exactly
/// this reason. There is also nothing you can do with the `Char` you get
/// back: `Char` has no operations and no `BEq` instance anywhere.
#[native string_get_char]
def String.get_char (s : String) (i : I64) : Option Char

#[native string_to_list]
def String.to_list (s : String) : List U8

#[native string_from_list]
def String.from_list (bytes : List U8) : String

/// UNWIRED -- declared here but absent from `exec_native`'s dispatch
/// table (`core/src/core_native.rs`), so calling it fails at runtime.
/// This is the hazard `validate_no_unwired_natives` (lang/codegen/emit.mo)
/// exists to catch; it never fires here only because nothing reaches
/// these. See AGENTS.md's `Char` item before relying on either.
#[native string_to_chars]
def String.to_chars (s : String) : List Char

/// UNWIRED (as `to_chars` above), and its parameter type `Chars` is not
/// a type that exists anywhere in the corpus -- presumably a typo for
/// `List Char`.
#[native string_from_chars]
def String.from_chars (bytes : List Chars) : String

// --- Self-hosted reference implementations, kept intentionally ---
//
// The four defs below (`String.hash_bytes_selfhosted`/
// `String.hash_selfhosted`, `bytes_lt_selfhosted`/`bytes_gt_selfhosted`,
// `String.lt_selfhosted`/`String.gt_selfhosted`) are NOT dead code. Every
// `String` comparison/hash used to run through here, converting through
// `String.to_list` (materializing a full `List U8` linked list) before
// comparing/folding — real self-hosted logic, but dominated by that
// allocation-heavy conversion rather than the comparison/hash itself
// (`String.beq` already had a native fast path, `string_eq`; these
// didn't). See self-hosted-compiler-perf.md Step 2: the active
// `String.hash`/`String.lt`/`String.gt` below now delegate to natives
// (`string_hash`/`string_lt`/`string_gt`, bit-identical algorithms,
// re-implemented in `core/src/core_native.rs`) as a temporary,
// pragmatic win — every `Identifier`/`ModulePath` `BOrd`/`Hashable`
// instance (`lang/types.mo`) pays this cost on every scope hashmap op.
// Kept here, renamed rather than deleted, as the intended long-term
// implementation to switch back to once more of the compiler is
// self-hosted and the interpreter itself is faster (see the tail-call
// optimization work in `core/src/core_eval.rs`, which reduces — but
// does not eliminate — the interpreter-overhead argument against pure
// `.mo` implementations of hot paths like this one).

/// djb2 hash: hash = hash * 33 + byte
#[terminating]
def String.hash_bytes_selfhosted (bytes: List U8) (acc: U64) : U64 :=
  match bytes {
    List.empty => acc,
    List.cons b rest =>
      let byte : U64 := U8.to_u64 b in
      String.hash_bytes_selfhosted rest (U64.add (U64.mul acc 33u64) byte)
  }

def String.hash_selfhosted (s : String) : U64 :=
  String.hash_bytes_selfhosted (String.to_list s) 5381u64

#[native string_hash]
def String.hash (s : String) : U64

instance BEq String {
	def beq (a b : String) : Bool := String.beq a b
}

def bytes_lt_selfhosted (a b : List U8) : Bool :=
	match a {
		empty => match b {
			empty => false,
			cons _ _ => true
		},
		cons xa ta => match b {
			empty => false,
			cons xb tb =>
				if U8.lt xa xb then true
				else if U8.gt xa xb then false
				else bytes_lt_selfhosted ta tb
		}
	}

def bytes_gt_selfhosted (a b : List U8) : Bool :=
	match a {
		empty => false,
		cons xa ta => match b {
			empty => true,
			cons xb tb =>
				if U8.gt xa xb then true
				else if U8.lt xa xb then false
				else bytes_gt_selfhosted ta tb
		}
	}

def String.lt_selfhosted (a b : String) : Bool := bytes_lt_selfhosted (String.to_list a) (String.to_list b)

def String.gt_selfhosted (a b : String) : Bool := bytes_gt_selfhosted (String.to_list a) (String.to_list b)

#[native string_lt]
def String.lt (a b : String) : Bool

#[native string_gt]
def String.gt (a b : String) : Bool

instance BOrd String {
	def lt (a b : String) : Bool := String.lt a b
	def gt (a b : String) : Bool := String.gt a b
}

instance ToString String {
	def to_string (s : String) : String := s
}

instance Add String {
	def add (a b : String) : String := String.concat a b
}

instance Append String {
  def append (a b : String) : String := String.concat a b
}

instance Hashable String {
  def hash (s : String) : U64 := String.hash s
}

def String.is_empty (s : String) : Bool :=
	I64.beq (String.length s) 0

// ── List helpers (polymorphic) ──

def List.reverse_append (bytes : List A) (acc : List A) : List A :=
	match bytes {
		empty => acc,
		cons b rest => List.reverse_append rest (List.cons b acc)
	}

def List.reverse (self : List A) : List A :=
	List.reverse_append self List.empty

def List.singleton (a : A) : List A :=
	List.cons a List.empty

// ── List U8 helpers (pattern-only, concrete) ──

def list_starts_with (full : List U8) (prefix : List U8) : Bool :=
	match prefix {
		empty => true,
		cons p_byte p_tail => match full {
			empty => false,
			cons f_byte f_tail =>
				if U8.beq p_byte f_byte
				then list_starts_with f_tail p_tail
				else false
		}
	}

def list_contains (haystack : List U8) (needle : List U8) : Bool :=
	match haystack {
		empty => List.is_empty needle,
		cons _ tail =>
			if list_starts_with haystack needle
			then true
			else list_contains tail needle
	}

// ── Prefix / Suffix ──

def String.ends_with (s : String) (suffix : String) : Bool :=
	String.starts_with (String.reverse suffix) (String.reverse s)

// ── Repetition ──

#[terminating]
def String.repeat (s : String) (n : I64) : String :=
	if I64.beq n 0
	then ""
	else String.concat s (String.repeat s (I64.sub n 1))

// ── Reverse ──

def String.reverse (s : String) : String :=
	String.from_list (List.reverse (String.to_list s))

// ── Search ──

def String.contains (s : String) (sub : String) : Bool :=
	list_contains (String.to_list s) (String.to_list sub)

// ── Trim ──

def is_whitespace_byte (b : U8) : Bool :=
	U8.beq b 32u8 || U8.beq b 9u8 || U8.beq b 10u8 || U8.beq b 13u8

def trim_leading (bytes : List U8) : List U8 :=
	match bytes {
		empty => bytes,
		cons b rest =>
			if is_whitespace_byte b
			then trim_leading rest
			else bytes
	}

def String.trim (s : String) : String :=
	String.from_list (List.reverse (trim_leading (List.reverse (trim_leading (String.to_list s)))))

/// Index of the last occurrence of `needle` in `haystack`, or -1.
///
/// Canonical home for what `lang/codegen/emit.mo` had as a local
/// `string_find_last`/`_loop` pair. A second, DIVERGED copy lived in
/// `lang/parser.mo` with a real bug -- it passed an end index where
/// `String.slice`'s third argument is a LENGTH -- and was deleted
/// (2026-09-01) rather than repaired, since it had no callers.
///
/// `#[terminating]`: `start_idx` counts DOWN to -1, which the structural
/// termination checker can't see is well-founded.
#[terminating]
def String.find_last_loop (haystack : String) (needle : String) (start_idx : I64) : I64 :=
	if I64.lt start_idx 0 then -1
	else if String.beq (String.slice haystack start_idx (String.length needle)) needle then start_idx
	else String.find_last_loop haystack needle (start_idx - 1)

def String.find_last (haystack : String) (needle : String) : I64 :=
	if String.beq needle "" then -1
	else if I64.gt (String.length needle) (String.length haystack) then -1
	else String.find_last_loop haystack needle (String.length haystack - String.length needle)

/// Concatenate every string in a list, no separator.
/// (For a separator, use `List.intercalate` in `std/list.mo`.)
///
/// Moved here from `lang/json.mo`, which declared this `String` method
/// inside a compiler module; `lang/cli.mo`'s `cli_concat_all` and
/// `lang/toml.mo`'s `toml_concat_list_body` were further copies.
def String.concat_all (ss : List String) : String :=
	match ss {
		empty => "",
		cons hd tl => String.concat hd (String.concat_all tl)
	}
