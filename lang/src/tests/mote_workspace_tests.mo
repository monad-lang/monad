/// `Mote.workspace_root_of` against this repository's own virtual root
/// (`mote.toml`, cwd = the checkout). A member whose DIRECTORY is listed is
/// accepted from the member list alone; only an unlisted spelling falls back
/// to reading every member's manifest for its name.
use std::path {Path}
use lib::mote {Mote.workspace_root_of, MoteRootLookup}

def is_found (l : MoteRootLookup) : Bool := match l {
    MoteRootLookup.root_found _ => true,
    _ => false,
}

def is_rejected (l : MoteRootLookup) : Bool := match l {
    MoteRootLookup.root_rejected _ => true,
    _ => false,
}

/// The name is deliberately one no member has: a hit can only come from
/// the directory comparison, which used to compare the ROOT's directory
/// and so never matched.
#[test]
def test_listed_member_dir_is_found_by_directory : IO Bool := do {
    let l <- Mote.workspace_root_of (Path.unsafe_dir "lang") "no-member-has-this-name";
    return (is_found l)
}

#[test]
def test_listed_member_name_is_found : IO Bool := do {
    let l <- Mote.workspace_root_of (Path.unsafe_dir "lang") "lang";
    return (is_found l)
}

#[test]
def test_unlisted_dir_and_name_is_rejected : IO Bool := do {
    let l <- Mote.workspace_root_of (Path.unsafe_dir "fixtures/cfg/on") "no-member-has-this-name";
    return (is_rejected l)
}
