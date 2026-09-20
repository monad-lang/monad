// Module-qualified references (`::` in TERM and TYPE position).
//
// `plans/implementations/qualified-names.md` makes `::` qualification
// valid wherever a name is, not just in a `use` path. Nothing in the
// corpus exercised that: every `::` elsewhere is a `use`/`open` path or
// a string literal, so the whole feature shipped with both compilers
// half-wiring it in OPPOSITE directions -- the Rust host panicked on a
// qualified TYPE (exit 101) while the self-hosted one could not resolve
// a qualified TERM, and neither accepted a dotted NAME half
// (`std::io::IO.println`), which is how most of std actually declares
// its defs.
//
// These run under BOTH runners, which is the point: the two failed at
// different stages, so a test either one skips proves nothing.

use std::base {}
use std::process {}
use init::string {}

// --- A qualified def reference ---------------------------------------

#[test]
def test_qualified_def_reference : Bool :=
    I64.gt std::process::process_id 0

// --- A qualified name with a DOTTED name half ------------------------
//
// `String.concat` is declared `pub def String.concat`, so the qualified
// spelling has a two-segment name half. The host used to leave
// `.concat` unconsumed and re-read it as an infix `.` operator.

#[test]
def test_qualified_dotted_name_half : Bool :=
    let s : String := init::string::String.concat "a" "b" in
    String.beq s "ab"

// --- A qualified inductive in TYPE position, and its constructor -----
//
// The annotation is the shape that used to panic the host outright.

def qualified_type_annotation (o : std::base::Ordering) : Bool := match o {
    Ordering.lt => true,
    _ => false,
}

#[test]
def test_qualified_type_annotation : Bool :=
    qualified_type_annotation std::base::Ordering.lt

// --- Both spellings of one name are ONE type -------------------------
//
// Atoms are keyed by spelling, so without deliberate sharing this
// reports "type mismatch: `Ordering` vs. `std::base::Ordering`" -- a
// name failing to match itself.

def bare_type_annotation (o : Ordering) : Bool := match o {
    Ordering.gt => true,
    _ => false,
}

#[test]
def test_qualified_and_bare_are_one_type : Bool :=
    bare_type_annotation std::base::Ordering.gt
