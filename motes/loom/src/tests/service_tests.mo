use loom::warp {Warp, ServiceName}
use loom::service {
    ServiceOwnership, Service, Provides,
    ServiceOwnership.check,
    Service.acquire, Service.config, Service.inject, Service.linear, Service.many, Service.name,
    Provides.add, Provides.empty, Provides.has, Provides.of_service,
    Warp.isolate_services, Warp.serves,
}

def grep_service : Service String :=
    Service.linear (ServiceName.name "grep") "grep-cfg"

def read_service : Service I64 :=
    Service.many (ServiceName.name "read") 7

#[test]
def test_injecting_a_provided_service_yields_its_config : Bool :=
    let w : Warp Provides I64 := Warp.warp (Provides.of_service grep_service) 0 in
    match Service.inject grep_service w {
        Result.ok cfg => String.beq cfg "grep-cfg",
        Result.err _ => false,
    }

#[test]
def test_a_missing_provider_is_a_runtime_err : Bool :=
    let w : Warp Provides I64 := Warp.warp (Provides.of_service read_service) 0 in
    match Service.inject grep_service w {
        Result.ok _ => false,
        Result.err e => String.contains e "missing provider: grep",
    }

#[test]
def test_isolation_hides_a_service_and_keeps_the_value : Bool :=
    let both : Provides := Provides.add (Service.name grep_service) (Provides.of_service read_service) in
    let w : Warp Provides I64 := Warp.warp both 7 in
    let iso : Warp Provides I64 := Warp.isolate_services (Provides.of_service read_service) w in
    Bool.not (Warp.serves (Service.name grep_service) iso) &&
    Warp.serves (Service.name read_service) iso &&
    Comonad.extract iso == 7

#[test]
def test_provides_add_and_has : Bool :=
    let p : Provides := Provides.add (ServiceName.name "extra") (Provides.of_service grep_service) in
    Provides.has (ServiceName.name "extra") p &&
    Provides.has (Service.name grep_service) p &&
    Bool.not (Provides.has (ServiceName.name "absent") p)

#[test]
def test_empty_provides_has_nothing : Bool :=
    let p : Provides := Provides.empty in
    Bool.not (Provides.has (ServiceName.name "grep") p)

#[test]
def test_single_owner_admits_the_first_owner : Bool :=
    match ServiceOwnership.check ServiceOwnership.single_owner 0 {
        Result.ok _ => true,
        Result.err _ => false,
    }

#[test]
def test_single_owner_rejects_a_second_owner : Bool :=
    match ServiceOwnership.check ServiceOwnership.single_owner 1 {
        Result.ok _ => false,
        Result.err e => String.contains e "already has an owner",
    }

#[test]
def test_any_owner_admits_shared_owners : Bool :=
    match ServiceOwnership.check ServiceOwnership.any_owner 9 {
        Result.ok _ => true,
        Result.err _ => false,
    }

#[test]
def test_acquire_checks_provision_and_ownership : Bool :=
    let w : Warp Provides I64 := Warp.warp (Provides.of_service grep_service) 0 in
    match Service.acquire grep_service w 0 {
        Result.ok _ => match Service.acquire grep_service w 1 {
            Result.ok _ => false,
            Result.err _ => true,
        },
        Result.err _ => false,
    }

def service_name_text (s : Service String) : String :=
    match Service.name s { ServiceName.name n => n }

#[test]
def test_service_accessors_round_trip : Bool :=
    String.beq (service_name_text grep_service) "grep" &&
    Service.config read_service == 7
