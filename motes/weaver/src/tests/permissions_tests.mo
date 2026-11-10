/// Session grants: lexical path normalization, repo containment, and
/// the grant list the gate consults.
use std::path {Path}
use shuttle::gate {Capability}
use weaver::permissions {
    PermGrant, PermScope, Permissions.normalize, Permissions.within, Permissions.matches,
    Permissions.get, Permissions.add, Permissions.revoke,
    Permissions.revoke_cap, Permissions.clear,
}
use std::ref {Ref}
use std::list {}

#[test]
def test_normalize_collapses_dot_segments : Bool :=
    String.beq (Permissions.normalize "/a/./b/../c") "/a/c"
        && String.beq (Permissions.normalize "a//b/") "a/b"
        && String.beq (Permissions.normalize "/../x") "/x"
        && String.beq (Permissions.normalize "a/../..") ".."
        && String.beq (Permissions.normalize ".") ""

/// The boundary is the `/`: `/repo` must not accept `/repo-evil`.
#[test]
def test_within_uses_a_path_boundary : Bool :=
    Permissions.within (Path.path "/repo") (Path.path "src/a.mo")
        && Permissions.within (Path.path "/repo") (Path.path "/repo/a.mo")
        && Permissions.within (Path.path "/repo") (Path.path "/repo")
        && Bool.not (Permissions.within (Path.path "/repo") (Path.path "../outside.mo"))
        && Bool.not (Permissions.within (Path.path "/repo") (Path.path "/repo-evil/a.mo"))
        && Bool.not (Permissions.within (Path.path "") (Path.path "a.mo"))

/// A repo grant covers a pick inside the workspace only; an anywhere
/// grant covers everything of its capability.
#[test]
def test_matches_respects_scope : Bool :=
    let repo_grant : PermGrant := { cap := Capability.write, scope := PermScope.repo } in
    let any_grant : PermGrant := { cap := Capability.write, scope := PermScope.anywhere } in
    let read_any : PermGrant := { cap := Capability.read, scope := PermScope.anywhere } in
    Permissions.matches [repo_grant] Capability.write true
        && Bool.not (Permissions.matches [repo_grant] Capability.write false)
        && Bool.not (Permissions.matches [repo_grant] Capability.exec true)
        && Permissions.matches [any_grant] Capability.write false
        && Permissions.matches [read_any] Capability.read false

/// The store is a Ref: add, revoke one scope, revoke a capability at both
/// scopes, clear.
#[test]
def test_grant_store_operations : IO Bool := do {
    let empty : List PermGrant := List.empty;
    let r <- Ref.new empty;
    let repo_write : PermGrant := { cap := Capability.write, scope := PermScope.repo };
    let any_write : PermGrant := { cap := Capability.write, scope := PermScope.anywhere };
    let any_read : PermGrant := { cap := Capability.read, scope := PermScope.anywhere };
    let _ <- Permissions.add (Option.some r) repo_write;
    let _ <- Permissions.add (Option.some r) any_write;
    let _ <- Permissions.add (Option.some r) any_read;
    let g1 <- Permissions.get (Option.some r);
    let _ <- Permissions.revoke (Option.some r) Capability.write PermScope.repo;
    let g2 <- Permissions.get (Option.some r);
    let _ <- Permissions.revoke_cap (Option.some r) Capability.write;
    let g3 <- Permissions.get (Option.some r);
    let _ <- Permissions.clear (Option.some r);
    let g4 <- Permissions.get (Option.some r);
    return (List.length g1 == 3 && List.length g2 == 2 && List.length g3 == 1 && List.length g4 == 0)
}

/// A root that NORMALIZES to nothing ("." or "./") must not accept the
/// world: its boundary would become "/", i.e. a repo grant over the
/// whole filesystem.
#[test]
def test_within_refuses_a_root_that_normalizes_empty : Bool :=
    Bool.not (Permissions.within (Path.path ".") (Path.path "/etc/passwd"))
        && Bool.not (Permissions.within (Path.path "./") (Path.path "../../x"))
        && Bool.not (Permissions.within (Path.path ".") (Path.path "a.mo"))

/// `/` is the one root whose boundary is the root itself.
#[test]
def test_within_root_slash_covers_the_filesystem : Bool :=
    Permissions.within (Path.path "/") (Path.path "/etc/passwd")
        && Permissions.within (Path.path "/") (Path.path "/")
