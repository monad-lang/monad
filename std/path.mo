// Filesystem path handling. See AGENTS.md's "init vs std" section for
// why this lives here (OS-specific-adjacent) rather than in `init/`.

/// A validated filesystem path -- a plain `String` wrapper, following
/// this codebase's existing newtype idiom (`Identifier`/`Operator`/
/// `ModulePath`, `lang/types.mo`). Construct via `Path.of` (validating);
/// the bare `Path.path` constructor is only for compile-time literals
/// already known non-empty (see `default_output_dir` in `lang/main.mo`).
type Path {
    path String
}

/// The validating smart constructor -- the ONLY sanctioned way to build
/// a `Path` from an arbitrary/external string (CLI argv, a hardcoded
/// literal, ...). Rejects the empty string: an empty path is never a
/// meaningful file target, and it's the concrete shape a defaulted or
/// missing CLI argument can otherwise silently slip through as. This is
/// deliberately narrow validation, not general path-syntax checking (no
/// NUL-byte/`..`-traversal/Windows-path handling) -- fully addresses
/// the bug this type was introduced to prevent (a naive `++`-joined
/// output path silently doubling up when one half was already
/// absolute), without taking on open-ended "what is a valid path"
/// scope nothing in this corpus actually needs yet.
def Path.of (s : String) : Result String Path :=
    if String.is_empty s
    then err "empty path"
    else ok (Path.path s)

def Path.to_string (p : Path) : String :=
    match p { Path.path s => s }

def Path.is_absolute (p : Path) : Bool :=
    String.starts_with "/" (Path.to_string p)

/// Low-level, unvalidated join -- the same empty-component/trailing-
/// slash-handling logic `lang/module.mo`'s own `path_join` used to
/// duplicate; that function now delegates here instead. Stays total,
/// not routed through `Path.of`: the module resolver relies on an
/// empty `a`/`b` behaving as a no-op, and forcing that through the
/// validating constructor would change that existing, working
/// behavior -- out of scope for this type.
def raw_path_join (a : String) (b : String) : String :=
    if String.beq a "" then b
    else if String.beq b "" then a
    else if String.ends_with a "/" then String.concat a b
    else String.concat (String.concat a "/") b

/// THE fix for the bug this type was introduced to prevent: an
/// absolute `b` replaces `a` entirely instead of naively concatenating
/// (`os.path.join`-style semantics) -- exactly the case that produced
/// a mangled `/tmp//tmp/monad_v2.ll` when `lang/main.mo`'s own
/// `link_ir` joined a hardcoded `/tmp` output directory with an
/// already-absolute user-supplied output name via plain `++`. Operates
/// on already-validated `Path` values, so the non-empty invariant
/// holds without re-validating (concatenating two non-empty strings
/// can't be empty).
def Path.join (a : Path) (b : Path) : Path :=
    if Path.is_absolute b then b
    else Path.path (raw_path_join (Path.to_string a) (Path.to_string b))

/// Append a literal suffix (extension, filename tail) -- no separator
/// inserted. Targets `output_dir ++ "/" ++ name ++ ".ll"`-style code.
def Path.with_suffix (p : Path) (suffix : String) : Path :=
    Path.path (String.concat (Path.to_string p) suffix)

def Path.beq (a b : Path) : Bool :=
    String.beq (Path.to_string a) (Path.to_string b)

instance BEq Path {
    def beq (a b : Path) : Bool := Path.beq a b
}

// No `Show Path` instance: it would need `use std.show {Show}`, and a
// std/*.mo file that's part of the always-loaded bootstrap set (see
// `core/src/term/module.rs`'s `init_package_sources`) depending on a
// NON-bootstrap std module hits a latent bug in the test runner's own
// per-file reachability computation (confirmed: `test std` panics with
// "uses unloaded module: std.show" processing this file, even though
// `check`/`compile` handle the identical dependency fine) -- nothing
// in this codebase's own migration needs `Show Path`, so sidestepping
// it here rather than chasing that separate, pre-existing bug.
