use std::list {List.length}
use lib::text {*}

#[partial]
def nth (n : I64) (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons x rest => if I64.beq n 0 then x else nth (I64.sub n 1) rest,
    }

#[test]
def test_trim : Bool :=
    String.beq (Text.trim "  hello \n") "hello"

#[test]
def test_split_on : Bool :=
    let parts : List String := Text.split_on "/" "a/b/c" in
    I64.beq (List.length parts) 3
        && String.beq (nth 0 parts) "a"
        && String.beq (nth 1 parts) "b"
        && String.beq (nth 2 parts) "c"

#[test]
def test_words_space : Bool :=
    let ws : List String := Text.words "Linux x86_64" in
    I64.beq (List.length ws) 2
        && String.beq (nth 0 ws) "Linux"
        && String.beq (nth 1 ws) "x86_64"

#[test]
def test_words_tab_and_space : Bool :=
    let ws : List String := Text.words " a\tb c " in
    I64.beq (List.length ws) 3
        && String.beq (nth 0 ws) "a"
        && String.beq (nth 1 ws) "b"
        && String.beq (nth 2 ws) "c"

#[test]
def test_words_tab_only : Bool :=
    let ws : List String := Text.words "a\tb" in
    I64.beq (List.length ws) 2
        && String.beq (nth 0 ws) "a"
        && String.beq (nth 1 ws) "b"

#[test]
def test_sort : Bool :=
    let xs : List String := Text.sort ["b", "c", "a"] in
    String.beq (nth 0 xs) "a" && String.beq (nth 1 xs) "b" && String.beq (nth 2 xs) "c"

#[test]
def test_basename : Bool :=
    String.beq (Text.basename "/a/b/c.mo") "c.mo"
        && String.beq (Text.basename "plain") "plain"
