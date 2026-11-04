/// Regression tests for a field access whose SUBJECT is a top-level def
/// rather than a local binder (`vzero.x`, not `p.first`).
///
/// `lower_path_ids` (`lang/src/parser/lower_parse.mo`) settles the
/// "module-qualified global, or field access?" ambiguity on exactly one
/// question -- is the path's first segment a local binder? -- because the
/// parser has no scope to ask. A local subject is therefore already a
/// single-entry `field_pattern` match by the time the checker sees it; a
/// top-level one is not, and the whole dotted spelling survives as ONE
/// global name, which no def is registered under. The reported failure was
/// plain: `unknown variable 'vzero.x'` for the entirely ordinary pair
/// `def vzero : Vec3` and `vzero.x`.
///
/// `try_global_field_access` (`lang/typecheck/infer.mo`) is the recovery:
/// it rebuilds the access with the parser's own builder and re-enters the
/// checker, which is what carries the desugaring into the `Def` codegen
/// reads. Its head has to resolve in the CODEGEN scope as well as the
/// checker's own, and those two do not agree on the spelling -- `monad
/// check` sees `vzero`, `monad compile` sees `simple::vzero`, because
/// `qualify_decl_names` renames defs and the alias rewriter matches a
/// reference only by its WHOLE name text (which a dotted spelling never
/// is). That is why `resolve_dotted_head` falls back to the one `def_refs`
/// key ending in `::vzero`.
///
/// These compile through the self-hosted backend and RUN the binary, so
/// the pre-fix symptom was not a wrong IR shape but a hard
/// `call to undefined symbol(s): vzero.x` at the end of codegen. Both rows
/// keep their totals under 256 deliberately -- the harness compares a
/// process EXIT CODE, which the OS truncates to 8 bits -- and use weights
/// that make a field read at the wrong index produce a different number
/// (reading `x` for `y` gives 120 in the first row, not 44).
///
/// The `#[test]` defs here never read a field themselves: a `#[test]` def
/// with a struct field access takes the FIELD's LLVM type as its own return
/// type and miscompiles. Every read lives in the compiled source string,
/// behind an accessor.
open IO {println}
use codegen::test::e2e_harness {compile_source_run_expect}

/// The minimal shape, exactly as filed: one struct, one top-level def, and
/// two accessors reading its two fields.
#[test]
def test_global_field_read_through_a_def : IO Bool :=
    let source := r#"struct Vec3 {
    x : I64,
    y : I64,
}
def vzero : Vec3 := { x := 40, y := 2 }
def vzero_x : I64 := vzero.x
def vzero_y : I64 := vzero.y
def main (args : List String) : IO I64 := do {
    return (I64.add vzero_x (I64.mul vzero_y 2))
}
"# in
    compile_source_run_expect source "test_global_field_read_through_a_def" 44

/// A two-step chain (`origin.pos.x`) through two structs, so the rebuilt
/// access is a nested `field_pattern` and not just one entry deep. The
/// second read is deliberate: reading `x` for `y` gives 80, not 42.
#[test]
def test_global_field_read_chains_through_two_structs : IO Bool :=
    let source := r#"struct Vec3 {
    x : I64,
    y : I64,
}
struct Body {
    pos : Vec3,
    mass : I64,
}
def p0 : Vec3 := { x := 40, y := 2 }
def origin : Body := { pos := p0, mass := 100 }
def origin_x : I64 := origin.pos.x
def origin_y : I64 := origin.pos.y
def main (args : List String) : IO I64 := do {
    return (I64.add origin_x origin_y)
}
"# in
    compile_source_run_expect source "test_global_field_read_chains_through_two_structs" 42
