/// Model tests: `public_only` keeps `pub` items and drops the rest, per
/// module, without dropping the module itself.
use lib::extract {DocExtract.extract_source}
use lib::model {DocItem, DocModule, DocMote, DocMote.public_only}

def sample : String :=
    "/// A public def.\npub def shown : I64 := 1\n\n/// A private def.\npriv def hidden : I64 := 2\n\n/// Package-private.\ndef pkg : I64 := 3\n"

def module_of (src : String) : DocModule :=
    DocExtract.extract_source "init/src/m.mo" src

def mote_of (src : String) : DocMote :=
    DocMote.mk "init" [module_of src]

/// Names of the items, in order.
def names (items : List DocItem) : List String :=
    List.map (fn (i : DocItem) => i.name) items

#[test]
def test_public_only_keeps_pub : Bool :=
    match DocMote.public_only (mote_of sample) {
        { modules, .. } =>
            match first_module modules {
                { items, .. } => match names items {
                    List.cons a rest => String.beq a "shown" && List.is_empty rest,
                    List.empty => false,
                },
            },
    }

def first_module (ms : List DocModule) : DocModule :=
    match ms {
        List.empty => DocModule.mk "" "" Option.none List.empty,
        List.cons m rest => m,
    }

/// A module whose every item is private keeps its page; it just has no items
/// to list. The module doc is still worth showing.
#[test]
def test_public_only_keeps_the_module : Bool :=
    match DocMote.public_only (mote_of "priv def only : I64 := 1\n") {
        { modules, .. } => I64.beq (List.length modules) 1,
    }
