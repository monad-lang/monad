/// `ClassIndex` must answer exactly what a scan of the whole class list
/// answers (`find_class_by_name`): the same class, and the FIRST one in
/// list order when several share a bare spelling.
use lang::types {
    Class, ClassIndex, Identifier, ModulePath, NamePath, Scope, ScopeData, Visibility, class_index_add,
    class_index_empty, class_index_of,
}
use lang::scope {class_index_find, find_class_by_name, scope_data_add_class, scope_data_empty, scope_find_class}
use lang::module {merge_scope_data}
use std::list {List.all}

def cls (name : String) : Class :=
    Class.mk (Identifier.id name) List.empty List.empty List.empty Visibility.package_private Option.none List.empty

def query (name : String) : NamePath := NamePath.mk [Identifier.id name]

/// Two `Show`s under different modules, so order decides the bare lookup.
def classes : List Class :=
    [cls "a::Show", cls "Eq", cls "b::Show", cls "Json.Deserializer", cls "std.cmp::Ord"]

def found_name (r : Option Class) : String := match r {
    Option.some c => match c.name { Identifier.id s => s },
    Option.none => "<none>",
}

def agrees (idx : ClassIndex) (q : String) (expected : String) : Bool :=
    String.beq (found_name (class_index_find idx (query q))) expected
        && String.beq (found_name (find_class_by_name classes (query q))) expected

#[test]
def test_index_matches_scan : Bool :=
    let idx := class_index_of classes in
    agrees idx "Show" "a::Show"
        && agrees idx "b::Show" "b::Show"
        && agrees idx "a::Show" "a::Show"
        && agrees idx "Eq" "Eq"
        && agrees idx "x::Eq" "Eq"
        && agrees idx "Json.Deserializer" "Json.Deserializer"
        && agrees idx "Ord" "std.cmp::Ord"
        && agrees idx "Deserializer" "<none>"
        && agrees idx "c::Show" "<none>"
        && agrees idx "Missing" "<none>"

/// `class_index_add` mirrors `List.cons`: adding back to front yields the
/// same index as building it from the whole list.
#[test]
def test_add_mirrors_cons : Bool :=
    let idx :=
        class_index_add (cls "a::Show")
            (class_index_add (cls "Eq")
                (class_index_add (cls "b::Show")
                    (class_index_add (cls "Json.Deserializer")
                        (class_index_add (cls "std.cmp::Ord") class_index_empty)))) in
    agrees idx "Show" "a::Show" && agrees idx "b::Show" "b::Show" && agrees idx "Ord" "std.cmp::Ord"

/// Same bare name in two modules: each qualified query finds its own
/// class whichever is listed first, and a bare query takes the first in
/// list order, exactly as the scan does.
#[test]
def test_same_bare_name_in_two_modules : Bool :=
    let ab := class_index_of shows_ab in
    let ba := class_index_of shows_ba in
    same_as_scan ab shows_ab "a::Show" "a::Show" && same_as_scan ab shows_ab "b::Show" "b::Show"
        && same_as_scan ba shows_ba "a::Show" "a::Show" && same_as_scan ba shows_ba "b::Show" "b::Show"
        && same_as_scan ab shows_ab "Show" "a::Show" && same_as_scan ba shows_ba "Show" "b::Show"

def shows_ab : List Class := [cls "a::Show", cls "b::Show"]

def shows_ba : List Class := [cls "b::Show", cls "a::Show"]

/// The key strips only a `::` qualifier, so a dotted class never answers
/// for its last segment, nor that segment's class for the dotted name.
#[test]
def test_dotted_name_is_not_its_last_segment : Bool :=
    let idx := class_index_of dotted in
    same_as_scan idx dotted "Deserializer" "Deserializer"
        && same_as_scan idx dotted "Json.Deserializer" "json::Json.Deserializer"
        && same_as_scan idx dotted "other::Deserializer" "Deserializer"

def dotted : List Class := [cls "Deserializer", cls "json::Json.Deserializer"]

/// More names than the map has buckets: names that share a hash bucket
/// stay apart.
#[test]
def test_names_sharing_a_hash_bucket_stay_apart : Bool :=
    let names := List.map (fn (i : I64) => String.concat "C" (I64.to_string i)) (upto 600) in
    let cs := List.map cls names in
    let idx := class_index_of cs in
    List.all (fn (n : String) => String.beq (found_name (class_index_find idx (query n))) n) names
        && String.beq (found_name (class_index_find idx (query "C600"))) "<none>"

/// The index `ScopeData` carries stays in step with `classes` through
/// `scope_data_add_class` and `merge_scope_data`: `scope_find_class`
/// answers what a scan of `classes` answers.
#[test]
def test_scope_data_index_tracks_classes : Bool :=
    let left := scope_data_add_class (scope_data_add_class scope_data_empty (cls "b::Show")) (cls "Eq") in
    let right := scope_data_add_class scope_data_empty (cls "a::Show") in
    let merged := merge_scope_data left right in
    let qs := ["Eq", "Show", "b::Show", "a::Show", "Ord"] in
    scope_agrees (scope_of left) left.classes qs
        && scope_agrees (scope_of merged) merged.classes qs
        && String.beq (found_name (scope_find_class (query "a::Show") (scope_of merged))) "a::Show"

def same_as_scan (idx : ClassIndex) (cs : List Class) (q : String) (expected : String) : Bool :=
    String.beq (found_name (class_index_find idx (query q))) expected
        && String.beq (found_name (find_class_by_name cs (query q))) expected

def scope_of (sd : ScopeData) : Scope := {
    module_id := ModulePath.mk [Identifier.id "class_index_tests"],
    scope := sd,
    parent := Option.none,
    incomplete_match_ok := false,
}

def scope_agrees (s : Scope) (cs : List Class) (qs : List String) : Bool :=
    List.all
        (fn (q : String) => String.beq (found_name (scope_find_class (query q) s)) (found_name (find_class_by_name cs (query q))))
        qs

/// `[0, n)`, ascending.
def upto (n : I64) : List I64 := upto_go n List.empty

#[partial]
def upto_go (n : I64) (acc : List I64) : List I64 :=
    if I64.lt 0 n then upto_go (n - 1) (List.cons (n - 1) acc) else acc
