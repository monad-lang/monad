/// Full case folding (CaseFolding statuses C and F) of a string, walking it
/// with the generated `Unicode.case_fold_cp` tree (`fold.mo`).
use lib::fold {Unicode.case_fold_cp}
use lib::utf8 {Unicode.char_width, Unicode.codepoint_at}
use std::list {}

/// Full case folding (statuses C and F) of a string: for caseless
/// comparison, such as CommonMark's link-label matching.
pub def Unicode.case_fold (s : String) : String :=
    String.concat_list (List.reverse (Unicode.case_fold_go s List.empty))

/// `codepoint_at` is `none` exactly on the empty string, and each step
/// drops at least one byte.
#[terminating]
def Unicode.case_fold_go (s : String) (acc : List String) : List String :=
    match Unicode.codepoint_at s {
        Option.none => acc,
        Option.some cp =>
            let w : I64 := Unicode.char_width s in
            match Unicode.case_fold_cp cp {
                Option.some folded => Unicode.case_fold_go (String.drop w s) (List.cons folded acc),
                Option.none => Unicode.case_fold_go (String.drop w s) (List.cons (String.slice s 0 w) acc),
            },
    }
