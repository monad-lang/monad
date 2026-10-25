/// Session approval grants, finer-grained than a capability: `repo`
/// covers a pick whose target path is inside the workspace root,
/// `anywhere` covers every pick of that capability.
///
/// The list lives in a `Ref` owned by weaver, not in shuttle's
/// `RunState.always` cache. Two reasons: the cache is keyed only by
/// capability (so an `a` on one write is an `a` on every write), and a
/// slash command cannot inspect or clear it -- `/permissions` can do
/// both here. The gate never returns `Approval.always`; it records a
/// grant and returns `once`, so shuttle's cache stays empty.
///
/// The repo scope is LEXICAL, not a sandbox: `..` is normalized before
/// the prefix test, but symlinks are not resolved and the tools still
/// receive the model's path verbatim. It scopes the approval prompt, not
/// the file system.
use shuttle::gate {Capability, Capability.eq}
use std::ref {Ref}
use std::list {List.filter, List.intercalate}

/// Where a grant applies. `repo` needs a path-bearing pick inside the
/// workspace root; `anywhere` is the old "all <cap>s this session".
pub type PermScope {
    repo,
    anywhere,
}

pub struct PermGrant {
    cap : Capability,
    scope : PermScope,
}

pub def PermScope.show (s : PermScope) : String :=
    match s {
        PermScope.repo => "repo",
        PermScope.anywhere => "anywhere",
    }

/// The capability's display name. Local to this module so `permissions`
/// does not import `gate` (the gate imports this one).
pub def cap_text (c : Capability) : String :=
    match c {
        Capability.read => "read",
        Capability.write => "write",
        Capability.exec => "exec",
        Capability.net => "net",
    }

pub def PermGrant.describe (g : PermGrant) : String :=
    String.concat (cap_text g.cap) (String.concat " (" (String.concat (PermScope.show g.scope) ")"))

// ── The session store ──────────────────────────────────────────────────

pub def Permissions.get (r : Option (Ref (List PermGrant))) : IO (List PermGrant) :=
    match r {
        Option.none => IO.pure List.empty,
        Option.some cell => Ref.get cell,
    }

pub def Permissions.add (r : Option (Ref (List PermGrant))) (g : PermGrant) : IO Unit :=
    match r {
        Option.none => IO.pure unit,
        Option.some cell => do {
            let _ <- Ref.update cell (fn (gs : List PermGrant) => List.cons g gs);
            IO.pure unit
        },
    }

/// Remove every grant of `cap` at `scope`. `scope` is exact: revoking
/// `repo` leaves an `anywhere` grant, which covers it (the safer
/// direction).
pub def Permissions.revoke (r : Option (Ref (List PermGrant))) (cap : Capability) (scope : PermScope) : IO Unit :=
    match r {
        Option.none => IO.pure unit,
        Option.some cell => do {
            let _ <- Ref.update cell (fn (gs : List PermGrant) => List.filter (fn (g : PermGrant) => Bool.not (Bool.and (Capability.eq g.cap cap) (scope_eq g.scope scope))) gs);
            IO.pure unit
        },
    }

/// Remove every grant of `cap`, at BOTH scopes -- what `/permissions
/// revoke read` means when no scope is named.
pub def Permissions.revoke_cap (r : Option (Ref (List PermGrant))) (cap : Capability) : IO Unit :=
    match r {
        Option.none => IO.pure unit,
        Option.some cell => do {
            let _ <- Ref.update cell (fn (gs : List PermGrant) => List.filter (fn (g : PermGrant) => Bool.not (Capability.eq g.cap cap)) gs);
            IO.pure unit
        },
    }

pub def Permissions.clear (r : Option (Ref (List PermGrant))) : IO Unit :=
    match r {
        Option.none => IO.pure unit,
        Option.some cell => do {
            let _ <- Ref.set cell List.empty;
            IO.pure unit
        },
    }

def scope_eq (a : PermScope) (b : PermScope) : Bool :=
    match a {
        PermScope.repo => match b { PermScope.repo => true, _ => false },
        PermScope.anywhere => match b { PermScope.anywhere => true, _ => false },
    }

/// The `/permissions` display: mode, workspace root, then one line per
/// grant. Lives here (not in `commands`) so the TUI dialog can render it
/// without importing the command module's state type.
pub def Permissions.render (root : Option String) (mode_text : String) (gs : List PermGrant) : String :=
    let root_text : String := match root {
        Option.none => "(no workspace root -- repo grants are not offered)",
        Option.some r => r,
    } in
    let head : String := String.concat "permissions: mode " (String.concat mode_text
        (String.concat ", root " root_text)) in
    let body : String := if List.is_empty gs
        then "  grants: none"
        else String.concat "  grants:\n"
            (String.concat_list (List.map (fn (g : PermGrant) => String.concat "  - " (PermGrant.describe g)) gs)) in
    String.concat head (String.concat "\n" (String.concat body
        "\n  /permissions allow <cap> [here|any] | revoke <cap|all> [here|any]"))

// ── Lexical path normalization and containment ─────────────────────────

#[partial]
def path_segments (s : String) (i : I64) (start : I64) (acc : List String) : List String :=
    if I64.lt (String.length s) i
    then
        if I64.lt (String.length s) start
        then List.reverse acc
        else List.reverse (List.cons (String.slice s start (String.length s - start)) acc)
    else if String.slice s i 1 == "/"
    then
        let seg : String := String.slice s start (i - start) in
        path_segments s (i + 1) (i + 1) (List.cons seg acc)
    else path_segments s (i + 1) start acc

def pop_or_keep (absolute : Bool) (stack : List String) : List String :=
    match stack {
        List.empty => if absolute then List.empty else List.cons ".." List.empty,
        List.cons _ tl => tl,
    }

#[partial]
def normalize_segments (absolute : Bool) (segs : List String) (stack : List String) : List String :=
    match segs {
        List.empty => stack,
        List.cons seg rest =>
            if String.is_empty seg
            then normalize_segments absolute rest stack
            else if seg == "."
            then normalize_segments absolute rest stack
            else if seg == ".."
            then normalize_segments absolute rest (pop_or_keep absolute stack)
            else normalize_segments absolute rest (List.cons seg stack),
    }

/// `/a/./b/../c` -> `/a/c`; relative `a/../..` keeps the leading `..`
/// that cannot be popped. Never resolves symlinks.
pub def Permissions.normalize (s : String) : String :=
    let absolute : Bool := String.starts_with "/" s in
    let segs : List String := path_segments s 0 0 List.empty in
    let stack : List String := normalize_segments absolute segs List.empty in
    let body : String := List.intercalate "/" (List.reverse stack) in
    if absolute then String.concat "/" body else body

/// `target` (relative targets resolved against `root`) is `root` or
/// below it, after lexical normalization. The boundary is the `/`, so
/// `root = /src/monad` does not accept `/src/monad-evil`.
pub def Permissions.within (root : String) (target : String) : Bool :=
    if String.is_empty root then false
    else
        let root_n : String := Permissions.normalize root in
        let target_abs : String := if String.starts_with "/" target then target else raw_join root_n target in
        let target_n : String := Permissions.normalize target_abs in
        if target_n == root_n then true
        else String.starts_with (String.concat root_n "/") target_n

def raw_join (a : String) (b : String) : String :=
    if String.ends_with a "/" then String.concat a b else String.concat a (String.concat "/" b)

/// A pick's target qualifies for repo scope only when it names a path
/// inside the root. `exec`/`net` picks and targetless picks never do:
/// a shell command is not confined by its input.
pub def Permissions.pick_in_repo (root : Option String) (target : Option String) : Bool :=
    match root {
        Option.none => false,
        Option.some r => match target {
            Option.none => false,
            Option.some t => Permissions.within r t,
        },
    }

/// Does any grant cover this pick? `anywhere` grants cover every pick
/// of their capability; `repo` grants cover only in-repo targets.
pub def Permissions.matches (root : Option String) (grants : List PermGrant) (cap : Capability) (target : Option String) : Bool :=
    matches_go root grants cap target

#[partial]
def matches_go (root : Option String) (grants : List PermGrant) (cap : Capability) (target : Option String) : Bool :=
    match grants {
        List.empty => false,
        List.cons g rest =>
            let covers : Bool := Capability.eq g.cap cap
                && (match g.scope {
                    PermScope.anywhere => true,
                    PermScope.repo => Permissions.pick_in_repo root target,
                }) in
            if covers then true else matches_go root rest cap target,
    }
