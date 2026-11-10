// Filesystem path handling. See AGENTS.md's "init vs std" section for
// why this lives here (OS-specific-adjacent) rather than in `init/`.

/// A validated filesystem path -- a plain `String` wrapper, following
/// this codebase's existing newtype idiom (`Identifier`/`Operator`/
/// `ModulePath`, `lang/types.mo`). Construct via `Path.of` (validating);
/// the bare `Path.path` constructor is for a string the caller has
/// already established is non-empty (a compile-time literal, or a value
/// it checked -- see `default_output_dir` in `cli/src/main.mo`).
pub type Path {
    path String
}

/// A `Path` is a `String` wrapper, and `String` is `Copy` (an immutable
/// pointer), so sharing one is a pointer copy, not an ownership move.
pub instance Copy Path {
    def copy (p : Path) : Pair Path Path := Pair.pair p p
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
/// Why `Path.of` rejected a string. Structured rather than a message so a
/// caller can branch on it or render it; `to_string` keeps the old text.
pub type PathError {
    empty,
}

pub def PathError.to_string (e : PathError) : String :=
    match e { PathError.empty => "empty path" }

pub def Path.of (s : String) : Result PathError Path :=
    if String.is_empty s
    then err PathError.empty
    else ok (Path.path s)

/// The boundary constructor for a string the caller has ALREADY
/// established is a path: a manifest-provided path, a compile-time
/// literal, or a value that passed `Path.of`. It skips only the non-empty
/// check; it is not a second validating constructor.
pub def Path.unsafe (s : String) : Path := Path.path s

pub def Path.to_string (p : Path) : String :=
    match p { Path.path s => s }

/// Absolute in the only sense this corpus needs: a leading `/`.
/// `Path.is_absolute` delegates here rather than repeating the test, so
/// the `String`-level join below and the `Path`-level one above cannot
/// disagree about what counts as absolute.
def raw_path_is_absolute (s : String) : Bool :=
    String.starts_with "/" s

pub def Path.is_absolute (p : Path) : Bool :=
    raw_path_is_absolute (Path.to_string p)

/// Low-level, unvalidated join -- the same empty-component/trailing-
/// slash-handling logic `lang/module.mo`'s own `path_join` used to
/// duplicate; that function now delegates here instead. Stays total,
/// not routed through `Path.of`: the module resolver relies on an
/// empty `a`/`b` behaving as a no-op, and forcing that through the
/// validating constructor would change that existing, working
/// behavior -- out of scope for this type.
///
/// An absolute `b` replaces `a` entirely (`os.path.join`-style
/// semantics). This is THE fix for the bug the `Path` type was
/// introduced to prevent -- the case that produced a mangled
/// `/tmp//tmp/monad_v2.ll` when `cli/src/main.mo`'s own `link_ir`
/// joined a hardcoded `/tmp` output directory with an already-absolute
/// user-supplied output name via plain `++`. It used to live in
/// `Path.join` alone, which left every DIRECT caller of this function
/// with the bug: `Mote.dep_dir_entries_go` joins a manifest
/// `[dependencies.X] path` onto the mote's own directory, and a bare
/// `monad check` sets that directory to `"."`, so an absolute path dep
/// came out as `".//home/.../init"` and the dependency silently failed
/// to resolve. Fixing it here rather than at that one call site is
/// deliberate -- a rule kept in one place is inherited by callers that
/// do not exist yet, which is what `Path.join`'s old comment was
/// asking for.
pub def raw_path_join (a : String) (b : String) : String :=
    if String.beq a "" then b
    else if String.beq b "" then a
    else if raw_path_is_absolute b then b
    else if String.ends_with a "/" then String.concat a b
    else String.concat (String.concat a "/") b

/// Delegates to `raw_path_join`, which owns the absolute-`b` rule for
/// both spellings. Operates on already-validated `Path` values, so the
/// non-empty invariant holds without re-validating (an absolute `b` is
/// returned as-is and is non-empty by validation; concatenating two
/// non-empty strings can't be empty either).
pub def Path.join (a : Path) (b : Path) : Path :=
    Path.path (raw_path_join (Path.to_string a) (Path.to_string b))

/// Append a literal suffix (extension, filename tail) -- no separator
/// inserted. Targets `output_dir ++ "/" ++ name ++ ".ll"`-style code.
pub def Path.with_suffix (p : Path) (suffix : String) : Path :=
    Path.path (String.concat (Path.to_string p) suffix)

/// The directory part of a path, or `""` when there is none ("hello.mo"
/// has no directory, and `""` means "the current one" to every caller --
/// notably `mkdir -p`, which must not be run on it).
///
/// Total and unvalidated for the same reason `raw_path_join` is: callers
/// rely on the empty result, which the validating constructor rejects.
/// `lang/src/module.mo`'s `extract_directory` delegates here rather than
/// keeping its own copy, exactly as `path_join` delegates to
/// `raw_path_join`.
pub def raw_parent_dir (s : String) : String :=
    let last_slash : I64 := raw_find_last_slash s (String.length s) in
    if I64.lt last_slash 0
    then ""
    else String.slice s 0 last_slash

/// `/` as a byte -- ASCII 47.
def slash_byte : U8 := 47u8

/// Scan backwards for `/`, returning -1 when absent. Walks from the end so
/// the FIRST hit is the last separator.
///
/// Compares BYTES via `String.get`, not one-character `String.slice`es: a
/// slice is a strlen + allocation + copy per character, which turns a scan
/// over a path into a quadratic, allocating one. This runs per module load
/// and per dependency in the loader's walk, so that cost is on the hot
/// path. (The byte comparison is also what the loader's own
/// `string_find_last_slash` did before it delegated here.)
#[partial]
def raw_find_last_slash (s : String) (i : I64) : I64 :=
    if I64.lt i 1
    then -1
    else match (String.get s (i - 1) : Option U8) {
        Option.some byte_val =>
            if U8.beq byte_val slash_byte
            then i - 1
            else raw_find_last_slash s (i - 1),
        Option.none => -1
    }

/// The directory part of `p`, or none when it has none ("hello.mo",
/// "/monad"): an empty `Path` is never constructed.
pub def Path.parent (p : Path) : Option Path :=
    let d : String := raw_parent_dir (Path.to_string p) in
    if String.is_empty d then Option.none else Option.some (Path.path d)

/// The last component of `p` -- the whole of it when it has no `/`.
pub def Path.file_name (p : Path) : String :=
    let s : String := Path.to_string p in
    let last_slash : I64 := raw_find_last_slash s (String.length s) in
    if I64.lt last_slash 0
    then s
    else String.drop (last_slash + 1) s

/// Collapse `.`/`..` segments and repeated separators: `a/../b` -> `b`,
/// `./x` -> `x`, `a//b` -> `a/b`. Moved here from `lang/module.mo` so the
/// loader, the CLI and build share one implementation; pure string work,
/// so it never changes which file resolves, only how the winner is spelled.
/// An empty result becomes `"."` (the current directory).
pub def Path.normalize (p : Path) : Path :=
    let raw : String := Path.to_string p in
    let joined : String :=
        join_path_segments (normalize_segments_go (path_segments_go raw 0 0 List.empty) List.empty) "" in
    let normalized : String :=
        if String.starts_with "/" raw
        then String.concat "/" joined
        else (if String.is_empty joined then "." else joined) in
    Path.path normalized

/// The extension after the last `.` in the file name, without the dot.
/// `none` when there is no dot or it is the file name's first byte (a
/// dotfile such as `.gitignore` has no extension).
pub def Path.extension (p : Path) : Option String :=
    let name : String := Path.file_name p in
    let dot : I64 := find_last_dot name (String.length name) in
    if I64.lt dot 1
    then Option.none
    else Option.some (String.drop (dot + 1) name)

/// The file name without its extension (`/a/b.mo` -> `b`); the whole
/// file name when it has no extension.
pub def Path.file_stem (p : Path) : String :=
    let name : String := Path.file_name p in
    let dot : I64 := find_last_dot name (String.length name) in
    if I64.lt dot 1 then name else String.slice name 0 dot

/// Join a relative segment onto a path, with `Path.join`'s absolute-
/// segment rule but without requiring the segment to be a `Path`
/// (segments are literals, never validated targets).
pub def Path.child (p : Path) (segment : String) : Path :=
    Path.path (raw_path_join (Path.to_string p) segment)

/// Byte scan for `.` (46) from the end; -1 when absent.
#[partial]
def find_last_dot (s : String) (i : I64) : I64 :=
    if I64.lt i 1
    then -1
    else match (String.get s (i - 1) : Option U8) {
        Option.some b => if U8.beq b 46u8 then i - 1 else find_last_dot s (i - 1),
        Option.none => -1,
    }

/// `s` split on `/`, with empty segments dropped so a leading `/` and any
/// `//` contribute nothing. `Path.normalize` restores the leading slash
/// from the original string, which is the only thing it can carry.
#[partial]
pub def path_segments_go (s : String) (i : I64) (start : I64) (acc : List String) : List String :=
    if I64.lt i (String.length s)
    then (if String.beq (String.slice s i 1) "/"
        then path_segments_go s (I64.add i 1) (I64.add i 1)
            (path_push_segment (String.slice s start (I64.sub i start)) acc)
        else path_segments_go s (I64.add i 1) start acc)
    else List.reverse (path_push_segment (String.slice s start (I64.sub (String.length s) start)) acc)

/// Accumulate one segment, skipping an empty one.
pub def path_push_segment (seg : String) (acc : List String) : List String :=
    if String.is_empty seg then acc else List.cons seg acc

/// `path_segments_go`'s output with `.` dropped and each `..` cancelling
/// the segment before it. A `..` with nothing to cancel is KEPT, and two
/// leading `..`s keep both -- otherwise `../init/src` would normalize to
/// `init/src` and stop naming the file it found.
#[partial]
pub def normalize_segments_go (segs : List String) (acc : List String) : List String :=
    match segs {
        List.empty => List.reverse acc,
        List.cons s rest =>
            if String.beq s "." then normalize_segments_go rest acc
            else (if String.beq s ".."
                then (match acc {
                    List.empty => normalize_segments_go rest (List.cons s List.empty),
                    List.cons hd tl =>
                        if String.beq hd ".."
                        then normalize_segments_go rest (List.cons s (List.cons hd tl))
                        else normalize_segments_go rest tl
                })
                else normalize_segments_go rest (List.cons s acc))
    }

/// Re-join segments with a single `/` between them and none at either end.
pub def join_path_segments (segs : List String) (acc : String) : String :=
    match segs {
        List.empty => acc,
        List.cons s rest =>
            if String.is_empty acc
            then join_path_segments rest s
            else join_path_segments rest (String.concat acc (String.concat "/" s))
    }

pub def Path.beq (a b : Path) : Bool :=
    String.beq (Path.to_string a) (Path.to_string b)

pub instance BEq Path {
    def beq (a b : Path) : Bool := Path.beq a b
}

/// Canonical-string hash/order, so a `Path` can key a map (the loader's
/// file table) without every caller rendering it first.
pub instance Hashable Path {
    def hash (p : Path) : U64 := String.hash (Path.to_string p)
}

pub instance BOrd Path {
    def lt (a b : Path) : Bool := BOrd.lt (Path.to_string a) (Path.to_string b)
    def gt (a b : Path) : Bool := BOrd.gt (Path.to_string a) (Path.to_string b)
    def lte (a b : Path) : Bool := Bool.not (BOrd.gt (Path.to_string a) (Path.to_string b))
    def gte (a b : Path) : Bool := Bool.not (BOrd.lt (Path.to_string a) (Path.to_string b))
}

// No `Show Path` instance: it would need `use std.show {Show}`, and a
// std/*.mo file that's part of the always-loaded bootstrap set (see
// `rust/core/src/term/module.rs`'s `init_package_sources`) depending on a
// NON-bootstrap std module hits a latent bug in the test runner's own
// per-file reachability computation (confirmed: `test std` panics with
// "uses unloaded module: std.show" processing this file, even though
// `check`/`compile` handle the identical dependency fine) -- nothing
// in this codebase's own migration needs `Show Path`, so sidestepping
// it here rather than chasing that separate, pre-existing bug.
