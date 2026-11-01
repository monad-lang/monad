/// `Title`: the reply parser for the agent-generated session name and
/// description, and the trigger that decides when to ask.
use init::string {}
use weaver::title {
    Title.max_name, Title.max_description, Title.needed, Title.parse,
    Title.user_prompt
}

def pair_of (r : Option (Pair String String)) : Pair String String :=
    match r {
        Option.none => Pair.pair "" "",
        Option.some p => p,
    }

def name_of (r : Option (Pair String String)) : String :=
    match pair_of r { Pair.pair n _ => n }

def desc_of (r : Option (Pair String String)) : String :=
    match pair_of r { Pair.pair _ d => d }

#[test]
def test_parse_labelled_pair : Bool :=
    let r : Option (Pair String String) := Title.parse "name: Add a cache\ndescription: Add a small cache to the editor." in
    Bool.and (name_of r == "Add a cache")
        (desc_of r == "Add a small cache to the editor.")

#[test]
def test_parse_name_only_keeps_the_description_empty : Bool :=
    let r : Option (Pair String String) := Title.parse "name: Add a cache" in
    Bool.and (name_of r == "Add a cache") (String.is_empty (desc_of r))

#[test]
def test_parse_strips_quotes_and_backticks : Bool :=
    let r : Option (Pair String String) := Title.parse "name: \"Add a cache\"\ndescription: `Wire it in.`" in
    Bool.and (name_of r == "Add a cache") (desc_of r == "Wire it in.")

#[test]
def test_parse_free_form_two_lines : Bool :=
    let r : Option (Pair String String) := Title.parse "Add a cache\nWire it into the editor." in
    Bool.and (name_of r == "Add a cache") (desc_of r == "Wire it into the editor.")

#[test]
def test_parse_free_form_drops_bullets_and_heading_marks : Bool :=
    let r : Option (Pair String String) := Title.parse "# Add a cache\n- Wire it in" in
    Bool.and (name_of r == "Add a cache") (desc_of r == "Wire it in")

#[test]
def test_parse_rejects_an_empty_reply : Bool :=
    match Title.parse "\n  \n" {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_parse_caps_the_fields : Bool :=
    let long : String := "word word word word word word word word word word word word word word word word" in
    let r : Option (Pair String String) := Title.parse (String.concat "name: " (String.concat long (String.concat "\ndescription: " long))) in
    let n : I64 := String.length (name_of r) in
    let d : I64 := String.length (desc_of r) in
    Bool.and (Bool.not (I64.lt (Title.max_name + 8) n))
        (Bool.not (I64.lt (Title.max_description + 8) d))

#[test]
def test_needed_asks_on_the_first_turn_or_a_plan : Bool :=
    Bool.and (Title.needed true false 1 false)
        (Bool.and (Title.needed true false 7 true)
            (Bool.and (Bool.not (Title.needed true false 2 false))
                (Bool.and (Bool.not (Title.needed false false 1 false))
                    (Bool.not (Title.needed true true 1 false)))))

#[test]
def test_user_prompt_carries_both_halves : Bool :=
    let p : String := Title.user_prompt "add a cache" "edited src/cache.mo" in
    Bool.and (String.contains p "add a cache") (String.contains p "edited src/cache.mo")
