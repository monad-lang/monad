/// A small, dependency-free unified diff for `monad fmt --diff`.
///
/// It emits ONE hunk covering the changed region (with up to three lines of
/// context), computed from the common prefix and suffix. That is exact for the
/// edits a whitespace formatter makes -- a rewritten line, an added/removed
/// final newline, or a capped blank run -- and deliberately not a minimal
/// diff. A real Myers/patience implementation is a follow-up if reflow makes
/// hunks far apart common.
///
/// It is independent of formatting: any two texts can be diffed.

use std::list {List.intercalate}
use lib::lexer {Lex.lines}

#[partial]
def common_prefix (a : List String) (b : List String) : I64 :=
    match a {
        List.empty => 0,
        List.cons x xs => match b {
            List.empty => 0,
            List.cons y ys =>
                if String.beq x y then I64.add 1 (common_prefix xs ys) else 0,
        },
    }

#[partial]
def drop_n (n : I64) (xs : List String) : List String :=
    if I64.gt n 0 then match xs {
        List.empty => List.empty,
        List.cons _ rest => drop_n (I64.sub n 1) rest,
    } else xs

#[partial]
def take_n (n : I64) (xs : List String) : List String :=
    if I64.gt n 0 then match xs {
        List.empty => List.empty,
        List.cons x rest => List.cons x (take_n (I64.sub n 1) rest),
    } else List.empty

#[partial]
def prefix_lines (prefix : String) (xs : List String) (acc : List String) : List String :=
    match xs {
        List.empty => List.reverse acc,
        List.cons x rest => prefix_lines prefix rest (List.cons (prefix ++ x) acc),
    }

def prefixed (prefix : String) (xs : List String) : List String :=
    prefix_lines prefix xs List.empty

def min_i64 (a : I64) (b : I64) : I64 :=
    if I64.lt a b then a else b

/// `old` and `new` have the same lines but differ in their text: only a line
/// terminator differs (a missing final newline, or CRLF vs LF). `Lex.lines`
/// drops terminators, so the regular hunk would be empty. Emit the
/// conventional last-line hunk, with `\ No newline at end of file` markers
/// where they apply; a CRLF/LF-only change has no visible line text, so it
/// says so instead.
def terminator_only (label : String) (old : String) (new : String) (lines : List String) (n : I64) : String :=
    let last : String := match List.get (I64.sub n 1) lines {
        Option.some s => s,
        Option.none => "",
    } in
    let old_marker : String :=
        if String.ends_with old "\n" then "" else "\\ No newline at end of file\n" in
    let new_marker : String :=
        if String.ends_with new "\n" then "" else "\\ No newline at end of file\n" in
    if String.beq old_marker new_marker then
        "--- " ++ label ++ "\n+++ " ++ label ++ "\n" ++
        "(identical lines; the line terminator differs)\n"
    else
        let hunk : String :=
            "@@ -" ++ I64.to_string n ++ ",1 +" ++ I64.to_string n ++ ",1 @@\n" ++
            "-" ++ last ++ "\n" ++ old_marker ++ "+" ++ last ++ "\n" ++ new_marker in
        "--- " ++ label ++ "\n+++ " ++ label ++ "\n" ++ hunk

/// The unified diff of `old` -> `new`, or "" when they are equal. `label`
/// appears on both the `---` and `+++` lines.
pub def Diff.unified (label : String) (old : String) (new : String) : String :=
    let old_lines : List String := Lex.lines old in
    let new_lines : List String := Lex.lines new in
    let old_len : I64 := List.length old_lines in
    let new_len : I64 := List.length new_lines in
    let prefix : I64 := common_prefix old_lines new_lines in
    if String.beq old new then ""
    else if I64.beq prefix old_len && I64.beq prefix new_len then
        terminator_only label old new old_lines old_len
    else
        let suffix_raw : I64 :=
            common_prefix (List.reverse old_lines) (List.reverse new_lines) in
        let suffix : I64 :=
            min_i64 (min_i64 suffix_raw (I64.sub old_len prefix)) (I64.sub new_len prefix) in
        let before : I64 := min_i64 3 prefix in
        let after : I64 := min_i64 3 suffix in
        let old_changed : I64 := I64.sub (I64.sub old_len prefix) suffix in
        let new_changed : I64 := I64.sub (I64.sub new_len prefix) suffix in
        let start_ctx : I64 := I64.sub prefix before in
        let old_count : I64 := I64.add (I64.add before old_changed) after in
        let new_count : I64 := I64.add (I64.add before new_changed) after in
        let old_start : I64 := if I64.gt old_count 0 then I64.add start_ctx 1 else start_ctx in
        let new_start : I64 := if I64.gt new_count 0 then I64.add start_ctx 1 else start_ctx in
        let hunk : String :=
            "@@ -" ++ I64.to_string old_start ++ "," ++ I64.to_string old_count ++
            " +" ++ I64.to_string new_start ++ "," ++ I64.to_string new_count ++ " @@" in
        let ctx_before : List String :=
            prefixed " " (take_n before (drop_n start_ctx old_lines)) in
        let removed : List String :=
            prefixed "-" (take_n old_changed (drop_n prefix old_lines)) in
        let added : List String :=
            prefixed "+" (take_n new_changed (drop_n prefix new_lines)) in
        let ctx_after : List String :=
            prefixed " " (take_n after (drop_n (I64.sub old_len suffix) old_lines)) in
        let body_lines : List String :=
            List.append ctx_before (List.append removed (List.append added ctx_after)) in
        let body : String := List.intercalate "\n" body_lines in
        "--- " ++ label ++ "\n" ++ "+++ " ++ label ++ "\n" ++ hunk ++ "\n" ++ body ++ "\n"
