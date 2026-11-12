// The unicode mote's library root -- bare `use unicode` resolves here.
//
// Explicit re-exports of the public surface. The generated tables
// (classify.mo, fold.mo, ranges.mo) come from src/tools/gen_tables.mo.
pub use lib::utf8 {Unicode.char_width, Unicode.codepoint_at, Unicode.utf8_of_codepoint}
pub use lib::classify {
    Unicode.is_space_separator,
    Unicode.is_punctuation_or_symbol,
    Unicode.is_white_space,
    Unicode.is_word,
    Unicode.is_digit,
}
pub use lib::fold {Unicode.case_fold_cp}
pub use lib::lookup {
    Unicode.decode_ranges,
    Unicode.union_ranges,
    Unicode.normalize_name,
    Unicode.gc_ranges,
    Unicode.script_ranges,
    Unicode.white_space_ranges,
    Unicode.word_ranges,
    Unicode.digit_ranges,
    Unicode.simple_fold_entries,
    Unicode.simple_fold_orbit,
}
pub use lib::casefold {Unicode.case_fold}
