/// Small string helpers monadup needs. Kept here, pure, so they are easy
/// to unit-test.
use std::list {List.sort_by}

#[partial]
pub def Text.trim_leading (s : String) : String :=
    if String.is_empty s then s
    else
        let c : String := String.slice s 0 1 in
        if String.beq c " " || String.beq c "\t" || String.beq c "\n" || String.beq c "\r"
        then Text.trim_leading (String.drop 1 s)
        else s

#[partial]
pub def Text.trim_trailing (s : String) : String :=
    let n : I64 := String.length s in
    if I64.lt n 1 then s
    else
        let i : I64 := I64.sub n 1 in
        let c : String := String.slice s i 1 in
        if String.beq c " " || String.beq c "\t" || String.beq c "\n" || String.beq c "\r"
        then Text.trim_trailing (String.slice s 0 i)
        else s

pub def Text.trim (s : String) : String :=
    Text.trim_leading (Text.trim_trailing s)

#[partial]
def Text.find_byte (needle : String) (s : String) (i : I64) : Option I64 :=
    if I64.lt i (String.length s) then
        if String.starts_with needle (String.drop i s)
        then Option.some i
        else Text.find_byte needle s (I64.add i 1)
    else Option.none

#[partial]
pub def Text.split_on (sep : String) (s : String) : List String :=
    match Text.find_byte sep s 0 {
        Option.none => [s],
        Option.some i =>
            let head : String := String.slice s 0 i in
            let tail : String := String.drop (I64.add i (String.length sep)) s in
            List.cons head (Text.split_on sep tail),
    }

/// Space- or tab-separated words, empty ones dropped. Used for `uname -sm`
/// and `$PATH`.
#[partial]
pub def Text.words (s : String) : List String :=
    Text.words_from (Text.trim s)

#[partial]
def Text.first_separator (s : String) : Option I64 :=
    match Text.find_byte " " s 0 {
        Option.none => Text.find_byte "\t" s 0,
        Option.some i =>
            match Text.find_byte "\t" s 0 {
                Option.none => Option.some i,
                Option.some j => Option.some (if I64.lt i j then i else j),
            },
    }

/// The first space- or tab-separated word (`sha256sum` prints
/// `<hash>  <file>`).
#[partial]
pub def Text.first_word (s : String) : String :=
    match Text.first_separator s {
        Option.none => s,
        Option.some i => String.slice s 0 i,
    }

#[partial]
def Text.words_from (s : String) : List String :=
    if String.is_empty s then List.empty
    else
        match Text.first_separator s {
            Option.none => [s],
            Option.some i =>
                let head : String := String.slice s 0 i in
                let tail : String := Text.trim (String.drop (I64.add i 1) s) in
                if String.is_empty head
                then Text.words_from tail
                else List.cons head (Text.words_from tail),
        }

#[partial]
pub def Text.sort (xs : List String) : List String :=
    List.sort_by String.lt xs

/// The final path component, or `s` itself when there is no separator.
#[partial]
pub def Text.basename (s : String) : String :=
    Text.basename_at s 0 0

#[partial]
def Text.basename_at (s : String) (i : I64) (last : I64) : String :=
    if I64.lt i (String.length s) then
        if String.beq (String.slice s i 1) "/"
        then Text.basename_at s (I64.add i 1) (I64.add i 1)
        else Text.basename_at s (I64.add i 1) last
    else String.slice s last (I64.sub (String.length s) last)
