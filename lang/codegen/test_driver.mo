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
use lang.module {try_parse_decls}

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

// ─── Driver source synthesis ────────────────────────────────────────
//
// Synthesizes `.mo` SOURCE TEXT for a driver `def main : IO I64 { ... }`
// that calls each named test in turn (v1 scope: each assumed
// `Bool`-returning), prints "PASS  <name>" / "FAIL  <name>" per test
// (`println`, inherited-stdio streaming — matches
// `lang.codegen.link.compile_and_run`'s own existing convention, the
// only way a compiled/run binary's results reach a human here), a
// final "<passed>/<total> tests passed" summary line, and returns `0`
// if every test passed, `1` otherwise (the sole signal the PARENT
// process — `lang/main.mo`'s own `test_file`, a later step — can
// observe via `exec_cmd`'s exit code).
//
// `def main : IO I64 { ... }` with zero params is deliberate and
// already handled downstream — `lang/codegen/emit.mo`'s own
// `ensure_main_params`/`rename_main` auto-add the runtime's `args :
// List String` param when `main` has none.
//
// Each test's own call result is bound to an index-based local
// (`__t0`, `__t1`, ...) rather than reusing the test's own name, so a
// test literally named e.g. `__t0` (vanishingly unlikely, but not this
// function's job to rule out) can't collide with the driver's own
// internal bookkeeping.

#[partial]
def test_var_name (idx : I64) : String := "__t" ++ I64.to_string idx

#[partial]
def synth_let_lines (names : List String) (idx : I64) : String :=
    match names {
        List.empty => "",
        List.cons name rest =>
            "    let " ++ test_var_name idx ++ " := " ++ name ++ ";\n" ++ synth_let_lines rest (idx + 1),
    }

#[partial]
def synth_report_lines (names : List String) (idx : I64) : String :=
    match names {
        List.empty => "",
        List.cons name rest =>
            "    if " ++ test_var_name idx ++ " then println \"PASS  " ++ name ++ "\" else println \"FAIL  " ++ name ++ "\";\n" ++ synth_report_lines rest (idx + 1),
    }

#[partial]
def synth_sum_expr (names : List String) (idx : I64) : String :=
    match names {
        List.empty => "0",
        List.cons _ rest =>
            "(if " ++ test_var_name idx ++ " then 1 else 0) + " ++ synth_sum_expr rest (idx + 1),
    }

#[partial]
def synthesize_test_driver_source (names : List String) : String :=
    let total : I64 := List.length names in
    "def main : IO I64 {\n" ++
    synth_let_lines names 0 ++
    synth_report_lines names 0 ++
    "    let __passed := " ++ synth_sum_expr names 0 ++ ";\n" ++
    "    let __total := " ++ I64.to_string total ++ ";\n" ++
    "    println (I64.to_string __passed ++ \"/\" ++ I64.to_string __total ++ \" tests passed\");\n" ++
    "    return (if I64.beq __passed __total then 0 else 1)\n" ++
    "}\n"

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
def test_synthesize_test_driver_source_parses_and_names_main : Bool :=
    // The whole point of the string-templating architecture decision
    // (see this file's own top-of-file doc comment): the synthesized
    // source must round-trip through the REAL parser, producing
    // exactly one `Decl.def_d` named "main".
    let source : String := synthesize_test_driver_source (List.cons "test_a" (List.cons "test_b" List.empty)) in
    match try_parse_decls source {
        Option.some decl_list =>
            match decl_list {
                List.cons only_decl rest =>
                    (match rest { List.empty => true, List.cons _ _ => false }) &&
                    match only_decl {
                        Decl.def_d def_val => String.beq (module_path_to_str (Def.name def_val)) "main",
                        _ => false,
                    },
                List.empty => false,
            },
        Option.none => false,
    }

#[test]
def test_synthesize_test_driver_source_no_tests_still_parses : Bool :=
    // Zero discovered tests -- a valid, parseable (if degenerate)
    // driver, matching the letter of the architecture decision even
    // in the empty case (`lang/main.mo`'s own caller is expected to
    // special-case this into a "no tests" report before ever calling
    // this function, but this function itself shouldn't crash on it).
    let source : String := synthesize_test_driver_source List.empty in
    match try_parse_decls source {
        Option.some _ => true,
        Option.none => false,
    }

#[test]
def test_has_top_level_main_true : Bool :=
    let decl_list : List Decl := List.cons (Decl.def_d (dummy_def "main" no_attrs)) List.empty in
    has_top_level_main decl_list

#[test]
def test_has_top_level_main_false : Bool :=
    let decl_list : List Decl := List.cons (Decl.def_d (dummy_def "helper" no_attrs)) List.empty in
    Bool.not (has_top_level_main decl_list)
