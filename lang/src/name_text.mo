/// Pure name-text conversions between a source name and its unqualified
/// (or bare) spelling.
///
/// This is the ONE boundary both the front end and the compiler backend use.
/// It deliberately depends on nothing but the ambient `String` primitives:
/// `lang` needs these helpers to judge references, and `codegen` needs them
/// to build symbols. Keeping the leaf free of `lang::types` is what lets
/// `codegen` import it without making `lang` depend on `codegen` -- the
/// cycle `codegen-mote-extraction` Phase 1 cuts.
///
/// The byte-wise forms are deliberate, not incidental: `String.slice`'s
/// third argument is a LENGTH, and `symbols.mo` records two real bugs from
/// getting that wrong. `String.get` scans without allocating.

/// The source name inside a qualified symbol -- `init.string::String.beq`
/// back to `String.beq`. Splits at the LAST `::`: a def key has one, and a
/// constructor key (`owner::ctor`) has the bare constructor after its last
/// one. A name that was never qualified (a synthesized or already-flat one)
/// comes back unchanged, so this is safe to apply anywhere a source-level
/// name is wanted.
#[partial]
pub def unqualify_def_name (s : String) : String :=
    let idx := string_find_last_qualifier_sep s 0 (String.length s) (0 - 1) in
    if I64.beq idx (0 - 1) then s else String.slice s (idx + 2) (String.length s - idx - 2)

/// The byte offset of the LAST `::` in `s[0..n)`, or -1.
///
/// Byte-wise, allocating nothing: `:` is 58, and every byte of a multi-byte
/// UTF-8 character is >= 0x80, so a byte scan can neither miss a `::` nor
/// mistake part of a character for one. The LAST one is the module/name
/// boundary (a ctor key's owner/ctor boundary) because `::` cannot occur
/// inside an identifier.
#[partial]
def string_find_last_qualifier_sep (s : String) (i : I64) (n : I64) (last : I64) : I64 :=
    if I64.gt (i + 2) n then last
    else
        match String.get s i {
            Option.some b =>
                if U8.beq b 58u8 then
                    match String.get s (i + 1) {
                        Option.some b2 =>
                            if U8.beq b2 58u8
                            then string_find_last_qualifier_sep s (i + 2) n i
                            else string_find_last_qualifier_sep s (i + 1) n last,
                        Option.none => last,
                    }
                else string_find_last_qualifier_sep s (i + 1) n last,
            Option.none => last,
        }

/// Does `s` equal `bare`, or spell it qualified (`module::bare` -- the
/// part after the LAST `::`, exactly what `unqualify_def_name` keeps)?
/// The no-allocation twin of `String.beq (unqualify_def_name s) bare`:
/// a byte comparison per position instead of a slice per position, for
/// the hot paths (`class_name_eq`, `carrier_id_eq`) that run per
/// instance/class comparison.
#[partial]
pub def string_matches_bare (s : String) (bare : String) : Bool :=
    let n : I64 := String.length s in
    let idx : I64 := string_find_last_qualifier_sep s 0 n (0 - 1) in
    if I64.beq idx (0 - 1)
    then String.beq s bare
    else bytes_equal_from s bare (idx + 2) 0 (String.length bare)

/// Bytes of `s` from `si` onward equal ALL of `bare` from `bi` onward.
#[partial]
def bytes_equal_from (s : String) (bare : String) (si : I64) (bi : I64) (bn : I64) : Bool :=
    if I64.beq bi bn then I64.beq si (String.length s)
    else
        match String.get s si {
            Option.some a =>
                match String.get bare bi {
                    Option.some b => if U8.beq a b then bytes_equal_from s bare (si + 1) (bi + 1) bn else false,
                    Option.none => false,
                },
            Option.none => false,
        }

/// Join a module text and a name text into the canonical whole-program key.
/// `::` cannot occur in an identifier, so the LAST `::` is the module/name
/// boundary (`global_key_module_text`/`global_key_name_text` split it back).
/// A module path's own dots are part of `module_text`; never split on `.`.
pub def global_key_join (module_text : String) (name_text : String) : String :=
    String.concat module_text (String.concat "::" name_text)

pub def global_key_is_qualified (s : String) : Bool :=
    Bool.not (I64.beq (string_find_last_qualifier_sep s 0 (String.length s) (0 - 1)) (0 - 1))

pub def global_key_module_text (s : String) : Option String :=
    let idx : I64 := string_find_last_qualifier_sep s 0 (String.length s) (0 - 1) in
    if I64.beq idx (0 - 1)
    then Option.none
    else Option.some (String.slice s 0 idx)

pub def global_key_name_text (s : String) : Option String :=
    let idx : I64 := string_find_last_qualifier_sep s 0 (String.length s) (0 - 1) in
    if I64.beq idx (0 - 1)
    then Option.none
    else Option.some (String.slice s (idx + 2) (String.length s - idx - 2))

/// A constructor key: the owner's canonical key plus the constructor
/// identifier. Its last `::` names the constructor, so `ctor_key_join`'s
/// output must go to the ctor helpers, never to `global_key_module_text`.
pub def ctor_key_join (owner_key : String) (ctor : String) : String :=
    global_key_join owner_key ctor

/// The constructor tag-map key: owner + ctor + arity. `#` cannot occur in an
/// identifier, so it separates the numeric arity without aliasing an
/// identifier that ends in digits.
pub def ctor_arity_key (owner_key : String) (ctor : String) (arity : I64) : String :=
    String.concat (ctor_key_join owner_key ctor)
        (String.concat "#" (I64.to_string arity))
