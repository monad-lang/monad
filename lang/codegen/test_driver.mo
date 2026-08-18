/// A `monad test` subcommand for the self-hosted compiler's own CLI
/// (`lang/main.mo`), analogous to `cargo test`: discover every
/// `#[test]`-attributed `def` in a target file, synthesize a driver
/// program that calls each of them and reports PASS/FAIL, compile that
/// driver via the existing native codegen pipeline
/// (`lang.codegen.emit`), and hand the result back to `lang/main.mo`
/// to link and run.
///
/// Kept as its own file rather than folded into the already-1857-line
/// `lang/codegen/emit.mo` — isolates the genuinely novel logic
/// (discovery + source synthesis) from existing, working codegen.
///
/// **Architecture decision**: the driver is synthesized as ordinary
/// `.mo` SOURCE TEXT (string-templated), not a hand-built de-Bruijn
/// `Term` AST — then fed through the already-proven
/// `lang.module.try_parse_decls`, the same entry point
/// `lang/main.mo`'s own `compile_file` fallback path already uses.
/// Hand-building a correct de-Bruijn-indexed `Term.lam`/`Term.app`/
/// `Term.var` tree with numerically-correct relative indices for N
/// sequential test calls is real, avoidable risk — string-templating a
/// small ordinary program and letting the real parser produce the
/// `Def` is how every other `Def` in this codebase gets produced.
///
/// **v1 scope**: `#[test]` defs are assumed `Bool`-returning — the
/// only shape observed anywhere in this whole corpus's own test
/// suites. `IO Bool`/`Result`-returning tests (which the Rust
/// reference's own `monad-rs test` does classify, via
/// `detect_test_result_value`, `core/src/lib.rs`) are explicitly out
/// of scope for this file — not silently unsupported, just not yet
/// needed by any real corpus file.
use lang.types {Attribute, Decl, Def, ModulePath, has_attr}
use lang.codegen.emit {module_path_to_str}

// ─── Discovery ──────────────────────────────────────────────────────

/// Whether `d` carries a bare `#[test]` attribute. Mirrors the Rust
/// reference's `Def::has_test_attr` (`core/src/term.rs`), via the
/// already-shared `has_attr` helper (`lang/types.mo`).
#[partial]
def is_test_def (d : Def) : Bool :=
    match d {
        Def.mk _name _typ _term _constraints attrs _vis => has_attr (Identifier.id "test") attrs,
    }

/// Every top-level `Def` in `decl_list` carrying a bare `#[test]`
/// attribute. Mirrors the Rust reference's own discovery precedent
/// (`core/src/lib.rs:886-892`, `module.defs().filter(has_test_attr)`)
/// — scoped to the given decl list only. Callers should pass the
/// TARGET FILE's own unprefixed decls (`get_module_info_decls
/// (get_loaded_main loaded)`), not its transitive `use` dependencies'
/// decls, matching that same precedent — a dependency's own tests
/// aren't this file's tests.
#[partial]
def discover_test_defs (decl_list : List Decl) : List Def :=
    match decl_list {
        List.empty => List.empty,
        List.cons d rest =>
            match d {
                Decl.def_d def_val =>
                    if is_test_def def_val
                    then List.cons def_val (discover_test_defs rest)
                    else discover_test_defs rest,
                _ => discover_test_defs rest,
            },
    }

/// Whether `decl_list` already defines its own top-level `Def` named
/// literally `"main"` — checked before splicing in the synthesized
/// driver, so a `main`-defining file gets a clear error instead of an
/// ambiguous "which `main` does `find_def_by_name` pick" outcome.
#[partial]
def has_top_level_main (decl_list : List Decl) : Bool :=
    match decl_list {
        List.empty => false,
        List.cons d rest =>
            match d {
                Decl.def_d def_val => if String.beq (module_path_to_str (Def.name def_val)) "main" then true else has_top_level_main rest,
                _ => has_top_level_main rest,
            },
    }

/// Bare source-level names of `defs`, in the same order.
#[partial]
def test_def_names (defs : List Def) : List String :=
    match defs {
        List.empty => List.empty,
        List.cons d rest => List.cons (module_path_to_str (Def.name d)) (test_def_names rest),
    }

// ─── Tests ───────────────────────────────────────────────────────────
//
// Hand-built `Decl.def_d` fixtures (some `#[test]`-attributed, some
// not), same construction style as `lang/codegen/link.mo`'s own
// existing `test_link_compile_defs_to_ir` fixture. No pipeline wiring
// exercised here — pure discovery-function unit tests.

def test_attr : List Attribute := List.cons (Attribute.mk (Identifier.id "test") List.empty) List.empty
def no_attrs : List Attribute := List.empty
def dummy_path (name : String) : ModulePath := ModulePath.mp (List.cons (Identifier.id name) List.empty)

def dummy_def (name : String) (attrs : List Attribute) : Def :=
    Def.mk (dummy_path name) Term.hole (Term.lit (Literal.num 1 NumSuffix.i64)) List.empty attrs Visibility.package_private

#[test]
def test_is_test_def_true_for_tagged : Bool :=
    is_test_def (dummy_def "test_a" test_attr)

#[test]
def test_is_test_def_false_for_untagged : Bool :=
    Bool.not (is_test_def (dummy_def "helper" no_attrs))

#[test]
def test_discover_test_defs_filters_correctly : Bool :=
    let decl_list : List Decl :=
        List.cons (Decl.def_d (dummy_def "test_a" test_attr))
            (List.cons (Decl.def_d (dummy_def "helper" no_attrs))
                (List.cons (Decl.def_d (dummy_def "test_b" test_attr)) List.empty)) in
    let found : List Def := discover_test_defs decl_list in
    I64.beq (List.length found) 2

#[test]
def test_discover_test_defs_ignores_non_def_decls : Bool :=
    let use_decl : Decl := Decl.use_d (dummy_path "std") UseFilter.use_bare true in
    let decl_list : List Decl := List.cons use_decl (List.cons (Decl.def_d (dummy_def "test_a" test_attr)) List.empty) in
    I64.beq (List.length (discover_test_defs decl_list)) 1

#[test]
def test_discover_test_defs_empty_when_none_tagged : Bool :=
    let decl_list : List Decl := List.cons (Decl.def_d (dummy_def "helper" no_attrs)) List.empty in
    match discover_test_defs decl_list { List.empty => true, List.cons _ _ => false }

#[test]
def test_test_def_names_preserves_order : Bool :=
    let defs : List Def := List.cons (dummy_def "test_a" test_attr) (List.cons (dummy_def "test_b" test_attr) List.empty) in
    match test_def_names defs {
        List.cons n1 rest =>
            String.beq n1 "test_a" &&
            match rest { List.cons n2 _ => String.beq n2 "test_b", List.empty => false },
        List.empty => false,
    }

#[test]
def test_has_top_level_main_true : Bool :=
    let decl_list : List Decl := List.cons (Decl.def_d (dummy_def "main" no_attrs)) List.empty in
    has_top_level_main decl_list

#[test]
def test_has_top_level_main_false : Bool :=
    let decl_list : List Decl := List.cons (Decl.def_d (dummy_def "helper" no_attrs)) List.empty in
    Bool.not (has_top_level_main decl_list)
