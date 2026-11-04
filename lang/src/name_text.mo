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
/// back to `String.beq`. A name that was never qualified (a synthesized
/// or already-flat one) comes back unchanged, so this is safe to apply
/// anywhere a source-level name is wanted.
#[partial]
pub def unqualify_def_name (s : String) : String :=
    let idx := string_find_qualifier_sep s 0 (String.length s) in
    if I64.beq idx (0 - 1) then s else String.slice s (idx + 2) (String.length s - idx - 2)

#[partial]
def string_find_qualifier_sep (s : String) (i : I64) (n : I64) : I64 :=
    // Byte-wise, allocating nothing: the old `String.slice s i 2` per
    // position paid two allocations per byte of a scan that runs once
    // per registered name -- and, since item 5.1's bare-vs-qualified
    // tolerance, once per bare-vs-qualified COMPARISON too. `:` is 58,
    // and every byte of a multi-byte UTF-8 character is >= 0x80, so a
    // byte scan can neither miss a `::` nor mistake part of a character
    // for one (AGENTS.md item 28: `String.get` is a native returning
    // `U8`; `String.slice` is a native that ALLOCATES).
    if I64.gt (i + 2) n then (0 - 1)
    else
        match String.get s i {
            Option.some b =>
                if U8.beq b 58u8 then
                    match String.get s (i + 1) {
                        Option.some b2 =>
                            if U8.beq b2 58u8 then i else string_find_qualifier_sep s (i + 1) n,
                        Option.none => (0 - 1),
                    }
                else string_find_qualifier_sep s (i + 1) n,
            Option.none => (0 - 1),
        }

/// Does `s` equal `bare`, or spell it qualified (`module::bare` -- the
/// part after the FIRST `::`, exactly what `unqualify_def_name` keeps)?
/// The no-allocation twin of `String.beq (unqualify_def_name s) bare`:
/// a byte comparison per position instead of a slice per position, for
/// the hot paths (`class_name_eq`, `carrier_id_eq`) that run per
/// instance/class comparison.
#[partial]
pub def string_matches_bare (s : String) (bare : String) : Bool :=
    let n : I64 := String.length s in
    let idx : I64 := string_find_qualifier_sep s 0 n in
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
