/// Lookups over the generated range tables: property names to range lists
/// and the simple case-fold orbits. (Full case folding of a string is
/// `casefold.mo`, kept apart so a consumer of the ranges never compiles the
/// fold tree.)
///
/// The range tables (`ranges.mo`) are strings of fixed-width hex, 12
/// characters per inclusive range (`LLLLLLHHHHHH`), decoded on demand. A
/// string literal costs the compiler nothing to elaborate, where a list
/// literal of a few thousand pairs nests that deep; and every consumer
/// builds its own structure from the decoded list once (a regex class, for
/// instance), so nothing is decoded on a hot path.
use lib::ranges {
    Unicode.gc_data, Unicode.script_data, Unicode.white_space_data, Unicode.word_data,
    Unicode.digit_data, Unicode.simple_fold_data,
}
use std::list {List.filter}

// ─── Decoding ───

def Unicode.hex_nibble (b : U8) : I64 :=
    let c : I64 := U8.to_i64 b in
    if I64.lt c 58 then c - 48
    else if I64.lt c 71 then c - 55
    else c - 87

/// `n` hex digits off the front of `xs`, and the rest.
#[terminating]
def Unicode.take_hex (xs : List U8) (n : I64) (acc : I64) : Pair I64 (List U8) :=
    if I64.lt 0 n then
        match xs {
            List.empty => Pair.pair acc List.empty,
            List.cons b rest => Unicode.take_hex rest (n - 1) (acc * 16 + Unicode.hex_nibble b),
        }
    else Pair.pair acc xs

/// Decode a table string into ascending inclusive `(lo, hi)` ranges.
pub def Unicode.decode_ranges (s : String) : List (Pair I64 I64) :=
    List.reverse (Unicode.decode_ranges_go (String.to_list s) List.empty)

#[terminating]
def Unicode.decode_ranges_go (xs : List U8) (acc : List (Pair I64 I64)) : List (Pair I64 I64) :=
    match xs {
        List.empty => acc,
        List.cons _ _ =>
            match Unicode.take_hex xs 6 0 {
                Pair.pair lo rest =>
                    match Unicode.take_hex rest 6 0 {
                        Pair.pair hi rest2 => Unicode.decode_ranges_go rest2 (List.cons (Pair.pair lo hi) acc),
                    },
            },
    }

// ─── Range algebra ───

/// The union of two ascending range lists, ascending and coalesced
/// (overlapping or adjacent ranges merge).
pub def Unicode.union_ranges (a : List (Pair I64 I64)) (b : List (Pair I64 I64)) : List (Pair I64 I64) :=
    List.reverse (Unicode.coalesce (Unicode.merge_by_lo a b List.empty) List.empty)

#[terminating]
def Unicode.merge_by_lo (a : List (Pair I64 I64)) (b : List (Pair I64 I64)) (acc : List (Pair I64 I64)) : List (Pair I64 I64) :=
    match a {
        List.empty => List.append (List.reverse acc) b,
        List.cons x xs =>
            match b {
                List.empty => List.append (List.reverse acc) (List.cons x xs),
                List.cons y ys =>
                    if I64.lt y.first x.first then Unicode.merge_by_lo (List.cons x xs) ys (List.cons y acc)
                    else Unicode.merge_by_lo xs (List.cons y ys) (List.cons x acc),
            },
    }

/// Coalesce an ascending-by-`lo` list; `acc` is newest-first.
#[terminating]
def Unicode.coalesce (xs : List (Pair I64 I64)) (acc : List (Pair I64 I64)) : List (Pair I64 I64) :=
    match xs {
        List.empty => acc,
        List.cons r rest =>
            match acc {
                List.empty => Unicode.coalesce rest (List.cons r List.empty),
                List.cons top below =>
                    if I64.lt (top.second + 1) r.first then Unicode.coalesce rest (List.cons r (List.cons top below))
                    else Unicode.coalesce rest
                        (List.cons (Pair.pair top.first (if I64.lt top.second r.second then r.second else top.second)) below),
            },
    }

// ─── Names ───

/// Loose matching, as UAX#44 and Rust's `regex` do it: ASCII case, spaces,
/// underscores and hyphens are ignored (`Uppercase_Letter`, `uppercase
/// letter` and `UPPERCASELETTER` are one name).
pub def Unicode.normalize_name (s : String) : String :=
    String.from_list (List.filter Unicode.is_name_byte (String.to_list (String.to_lowercase s)))

def Unicode.is_name_byte (b : U8) : Bool :=
    Bool.not (U8.beq b 32u8 || U8.beq b 95u8 || U8.beq b 45u8)

/// Every General_Category name and alias (normalized) with the two-letter
/// categories it covers.
def Unicode.gc_aliases : List (Pair String (List String)) :=
    [Pair.pair "lu" ["Lu"], Pair.pair "uppercaseletter" ["Lu"],
        Pair.pair "ll" ["Ll"], Pair.pair "lowercaseletter" ["Ll"],
        Pair.pair "lt" ["Lt"], Pair.pair "titlecaseletter" ["Lt"],
        Pair.pair "lm" ["Lm"], Pair.pair "modifierletter" ["Lm"],
        Pair.pair "lo" ["Lo"], Pair.pair "otherletter" ["Lo"],
        Pair.pair "mn" ["Mn"], Pair.pair "nonspacingmark" ["Mn"],
        Pair.pair "mc" ["Mc"], Pair.pair "spacingmark" ["Mc"],
        Pair.pair "me" ["Me"], Pair.pair "enclosingmark" ["Me"],
        Pair.pair "nd" ["Nd"], Pair.pair "decimalnumber" ["Nd"], Pair.pair "digit" ["Nd"],
        Pair.pair "nl" ["Nl"], Pair.pair "letternumber" ["Nl"],
        Pair.pair "no" ["No"], Pair.pair "othernumber" ["No"],
        Pair.pair "pc" ["Pc"], Pair.pair "connectorpunctuation" ["Pc"],
        Pair.pair "pd" ["Pd"], Pair.pair "dashpunctuation" ["Pd"],
        Pair.pair "ps" ["Ps"], Pair.pair "openpunctuation" ["Ps"],
        Pair.pair "pe" ["Pe"], Pair.pair "closepunctuation" ["Pe"],
        Pair.pair "pi" ["Pi"], Pair.pair "initialpunctuation" ["Pi"],
        Pair.pair "pf" ["Pf"], Pair.pair "finalpunctuation" ["Pf"],
        Pair.pair "po" ["Po"], Pair.pair "otherpunctuation" ["Po"],
        Pair.pair "sm" ["Sm"], Pair.pair "mathsymbol" ["Sm"],
        Pair.pair "sc" ["Sc"], Pair.pair "currencysymbol" ["Sc"],
        Pair.pair "sk" ["Sk"], Pair.pair "modifiersymbol" ["Sk"],
        Pair.pair "so" ["So"], Pair.pair "othersymbol" ["So"],
        Pair.pair "zs" ["Zs"], Pair.pair "spaceseparator" ["Zs"],
        Pair.pair "zl" ["Zl"], Pair.pair "lineseparator" ["Zl"],
        Pair.pair "zp" ["Zp"], Pair.pair "paragraphseparator" ["Zp"],
        Pair.pair "cc" ["Cc"], Pair.pair "control" ["Cc"], Pair.pair "cntrl" ["Cc"],
        Pair.pair "cf" ["Cf"], Pair.pair "format" ["Cf"],
        Pair.pair "cs" ["Cs"], Pair.pair "surrogate" ["Cs"],
        Pair.pair "co" ["Co"], Pair.pair "privateuse" ["Co"],
        Pair.pair "cn" ["Cn"], Pair.pair "unassigned" ["Cn"],
        Pair.pair "l" ["Lu", "Ll", "Lt", "Lm", "Lo"], Pair.pair "letter" ["Lu", "Ll", "Lt", "Lm", "Lo"],
        Pair.pair "lc" ["Lu", "Ll", "Lt"], Pair.pair "casedletter" ["Lu", "Ll", "Lt"],
        Pair.pair "m" ["Mn", "Mc", "Me"], Pair.pair "mark" ["Mn", "Mc", "Me"],
        Pair.pair "combiningmark" ["Mn", "Mc", "Me"],
        Pair.pair "n" ["Nd", "Nl", "No"], Pair.pair "number" ["Nd", "Nl", "No"],
        Pair.pair "p" ["Pc", "Pd", "Ps", "Pe", "Pi", "Pf", "Po"],
        Pair.pair "punctuation" ["Pc", "Pd", "Ps", "Pe", "Pi", "Pf", "Po"],
        Pair.pair "punct" ["Pc", "Pd", "Ps", "Pe", "Pi", "Pf", "Po"],
        Pair.pair "s" ["Sm", "Sc", "Sk", "So"], Pair.pair "symbol" ["Sm", "Sc", "Sk", "So"],
        Pair.pair "z" ["Zs", "Zl", "Zp"], Pair.pair "separator" ["Zs", "Zl", "Zp"],
        Pair.pair "c" ["Cc", "Cf", "Cs", "Co", "Cn"], Pair.pair "other" ["Cc", "Cf", "Cs", "Co", "Cn"]]

#[terminating]
def Unicode.assoc {A : Type} (key : String) (xs : List (Pair String A)) : Option A :=
    match xs {
        List.empty => Option.none,
        List.cons entry rest =>
            match entry {
                Pair.pair k v => if String.beq k key then Option.some v else Unicode.assoc key rest,
            },
    }

/// Like `assoc`, comparing normalized keys.
#[terminating]
def Unicode.assoc_loose (key : String) (xs : List (Pair String String)) : Option String :=
    match xs {
        List.empty => Option.none,
        List.cons entry rest =>
            match entry {
                Pair.pair k v =>
                    if String.beq (Unicode.normalize_name k) key then Option.some v
                    else Unicode.assoc_loose key rest,
            },
    }

#[terminating]
def Unicode.union_codes (codes : List String) (acc : List (Pair I64 I64)) : List (Pair I64 I64) :=
    match codes {
        List.empty => acc,
        List.cons code rest =>
            match Unicode.assoc code Unicode.gc_data {
                Option.some data => Unicode.union_codes rest (Unicode.union_ranges acc (Unicode.decode_ranges data)),
                Option.none => Unicode.union_codes rest acc,
            },
    }

/// A General_Category value or group by any of its names (`Lu`,
/// `Uppercase_Letter`, `L`, `Letter`, `punct`, ...), as ascending ranges.
pub def Unicode.gc_ranges (name : String) : Option (List (Pair I64 I64)) :=
    match Unicode.assoc (Unicode.normalize_name name) Unicode.gc_aliases {
        Option.some codes => Option.some (Unicode.union_codes codes List.empty),
        Option.none => Option.none,
    }

/// A Script by its long name (`Greek`, `Old_Italic`, loosely matched).
pub def Unicode.script_ranges (name : String) : Option (List (Pair I64 I64)) :=
    match Unicode.assoc_loose (Unicode.normalize_name name) Unicode.script_data {
        Option.some data => Option.some (Unicode.decode_ranges data),
        Option.none => Option.none,
    }

/// White_Space (PropList): what Rust's `regex` uses for `\s`.
pub def Unicode.white_space_ranges : List (Pair I64 I64) := Unicode.decode_ranges Unicode.white_space_data

/// The UTS#18 word set Rust's `regex` uses for `\w`: Alphabetic, Mark,
/// Decimal_Number, Connector_Punctuation and Join_Control.
pub def Unicode.word_ranges : List (Pair I64 I64) := Unicode.decode_ranges Unicode.word_data

/// Decimal_Number (`Nd`): `\d`.
pub def Unicode.digit_ranges : List (Pair I64 I64) := Unicode.decode_ranges Unicode.digit_data

// ─── Simple case folding ───

/// Every scalar with a simple case-fold equivalent (CaseFolding statuses C
/// and S), ascending, each with the OTHER members of its orbit: `k` lists
/// `K` and U+212A KELVIN SIGN.
pub def Unicode.simple_fold_entries : List (Pair I64 (List I64)) :=
    List.reverse (Unicode.fold_entries_go (String.to_list Unicode.simple_fold_data) List.empty)

#[terminating]
def Unicode.fold_entries_go (xs : List U8) (acc : List (Pair I64 (List I64))) : List (Pair I64 (List I64)) :=
    match xs {
        List.empty => acc,
        List.cons _ _ =>
            match Unicode.take_hex xs 6 0 {
                Pair.pair cp rest =>
                    match Unicode.take_hex rest 1 0 {
                        Pair.pair n rest2 => Unicode.fold_others cp n rest2 List.empty acc,
                    },
            },
    }

#[terminating]
def Unicode.fold_others (cp : I64) (n : I64) (xs : List U8) (others : List I64) (acc : List (Pair I64 (List I64))) : List (Pair I64 (List I64)) :=
    if I64.lt 0 n then
        match Unicode.take_hex xs 6 0 {
            Pair.pair o rest => Unicode.fold_others cp (n - 1) rest (List.cons o others) acc,
        }
    else Unicode.fold_entries_go xs (List.cons (Pair.pair cp (List.reverse others)) acc)

/// The other members of `cp`'s simple case-fold orbit; empty when it has
/// none. A linear scan: callers folding many scalars should walk
/// `simple_fold_entries` once instead.
pub def Unicode.simple_fold_orbit (cp : I64) : List I64 :=
    Unicode.orbit_in cp Unicode.simple_fold_entries

#[terminating]
def Unicode.orbit_in (cp : I64) (entries : List (Pair I64 (List I64))) : List I64 :=
    match entries {
        List.empty => List.empty,
        List.cons entry rest =>
            match entry {
                Pair.pair c others =>
                    if I64.beq c cp then others
                    else if I64.lt cp c then List.empty
                    else Unicode.orbit_in cp rest,
            },
    }
