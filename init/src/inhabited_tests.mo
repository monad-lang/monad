/// Tests for `init/src/prelude.mo`'s `Inhabited` class and `NonEmpty`
/// predicate, and for the opaque primitive types' witness constructors.
#[test]
def test_inhabited_i64 : Bool :=
    I64.beq Inhabited.default 0

#[test]
def test_inhabited_bool : Bool :=
    Bool.not Inhabited.default

#[test]
def test_inhabited_string : Bool :=
    String.beq Inhabited.default ""

#[test]
def test_inhabited_unit : Bool :=
    let u : Unit := Inhabited.default in
    true

def default_i64s : List I64 := Inhabited.default

#[test]
def test_inhabited_list : Bool :=
    List.is_empty default_i64s

#[test]
def test_nonempty_carries_its_witness : Bool :=
    match NonEmpty.nonempty 7 {
        NonEmpty.nonempty w => I64.beq w 7,
    }

/// The opaque primitive types are INHABITED by exactly one nullary witness
/// constructor, so they are not the empty type. The witness is
/// unreferenceable (`#[opaque]`), which is what keeps them abstract — these
/// tests only ever obtain values from ordinary literals/natives.
#[test]
def test_a_primitive_value_comes_from_its_operations : Bool :=
    let x : I64 := I64.add 1 2 in
    I64.beq x 3
