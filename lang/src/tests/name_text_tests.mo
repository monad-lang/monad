use lib::name_text {
    ctor_arity_key, ctor_key_join, global_key_is_qualified, global_key_join,
    global_key_module_text, global_key_name_text, string_matches_bare, unqualify_def_name,
}

#[test]
def test_unqualify_uses_the_last_separator : Bool :=
    String.beq (unqualify_def_name "a::b::c") "c"

#[test]
def test_global_key_round_trip : Bool :=
    let key : String := global_key_join "a.b" "C.d" in
    match global_key_module_text key {
        Option.some m =>
            match global_key_name_text key {
                Option.some n => String.beq m "a.b" && String.beq n "C.d",
                Option.none => false,
            },
        Option.none => false,
    }

#[test]
def test_global_key_is_qualified : Bool :=
    global_key_is_qualified "a::b" && Bool.not (global_key_is_qualified "b")

#[test]
def test_ctor_key_keeps_owner_and_arity : Bool :=
    let a : String := ctor_arity_key "m::T" "cons" 2 in
    let b : String := ctor_arity_key "m::U" "cons" 2 in
    String.beq a "m::T::cons#2"
        && String.beq b "m::U::cons#2"
        && Bool.not (String.beq a b)

#[test]
def test_ctor_key_join_names_the_constructor : Bool :=
    String.beq (ctor_key_join "m::T" "cons") "m::T::cons"
        && String.beq (unqualify_def_name (ctor_key_join "m::T" "cons")) "cons"

#[test]
def test_string_matches_bare_uses_the_last_separator : Bool :=
    string_matches_bare "m::T::cons" "cons"
        && Bool.not (string_matches_bare "m::T::cons" "T::cons")
