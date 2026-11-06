/// Shared fixtures and assertions for the backend's test modules.

use lang::types {
    AttrArg, Attribute, Decl, DebugName, Def, Identifier, NamePath, Term,
    TypeConstraint, Visibility, sentinel,
}
use lib::symbols {bare_npath}

#[partial]
def qtest_def (name : String) (body_ref : String) : Decl :=
    Decl.def_d (Def.mk (bare_npath name) Term.hole
        (Term.var sentinel (DebugName.named (Identifier.id body_ref)))
        ([] : List TypeConstraint) ([] : List Attribute) Visibility.package_private List.empty)

#[partial]
def check_contains (text : String) (needle : String) : Bool :=
    if String.beq text "" then false
    else if String.beq (String.slice text 0 (String.length needle)) needle then true
    else check_contains (String.slice text 1 (String.length text - 1)) needle

/// `check_contains`'s counting sibling -- for tests that must pin an
/// occurrence count EXACTLY (e.g. one `alloc_constructor`, where a
/// wrong wrap kind would emit two) rather than detect mere presence.
#[partial]
def check_count (text : String) (needle : String) : I64 :=
    if String.beq text "" then 0
    else if String.beq (String.slice text 0 (String.length needle)) needle
    then 1 + check_count (String.slice text 1 (String.length text - 1)) needle
    else check_count (String.slice text 1 (String.length text - 1)) needle
