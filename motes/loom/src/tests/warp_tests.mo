use loom::warp {Warp, ServiceName}

#[test]
def test_extract_is_the_val_component : Bool :=
    Comonad.extract (Warp.warp ["svc"] 42) == 42

#[test]
def test_duplicate_carries_the_registry_into_both : Bool :=
    match Comonad.duplicate (Warp.warp ["svc"] 42) {
        Warp.warp g1 inner =>
            match inner {
                Warp.warp g2 v => v == 42,
            }
    }

#[test]
def test_extend_applies_with_the_registry_in_scope : Bool :=
    match Comonad.extend (fn w => Comonad.extract w + 1) (Warp.warp ["svc"] 41) {
        Warp.warp g v => v == 42
    }

#[test]
def test_provides_true_for_a_listed_service : Bool :=
    let w : Warp (List ServiceName) I64 := Warp.warp [ServiceName.name "grep", ServiceName.name "read"] 0 in
    Warp.provides (ServiceName.name "grep") w

#[test]
def test_provides_false_for_an_unlisted_service : Bool :=
    let w : Warp (List ServiceName) I64 := Warp.warp [ServiceName.name "grep"] 0 in
    Bool.not (Warp.provides (ServiceName.name "write") w)

#[test]
def test_isolate_replaces_the_visible_registry_only : Bool :=
    let w : Warp (List ServiceName) I64 := Warp.warp [ServiceName.name "grep"] 7 in
    let isolated := Warp.isolate [ServiceName.name "read"] w in
    Bool.not (Warp.provides (ServiceName.name "grep") isolated) &&
    Warp.provides (ServiceName.name "read") isolated &&
    Comonad.extract isolated == 7
