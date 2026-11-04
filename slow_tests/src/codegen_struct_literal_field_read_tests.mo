/// Regression tests for a field read inside a struct LITERAL, and for the
/// struct-update base.
///
/// `{ a := s.a, log := s.log : S }` compiled both reads to
/// `monad_get_field(s, 0)`, so a rebuilt struct carried its first field
/// twice. Forge found it as list corruption -- `List.append s.log [v]` on
/// an empty `log` came back with two entries, because `s.log` was really
/// `s.buckets` (`plans/implementations/2026-10-03-any-boxed-struct-
/// reconstruction-corrupts-sibling-field.md`, filed against `Any` and the
/// GC, neither of which was involved).
///
/// The cause: codegen's own `desugar_struct_lits_decls` rewrites an
/// annotated literal to a `Term.con` and leaves the per-arg check to the
/// elaborate pass behind it, and `type_check_con` looked the constructor up
/// under `typ_name ++ [cname]` -- `[S, mk]`, which nothing registers. Every
/// def holding an annotated struct literal therefore failed to elaborate
/// and kept the parser's one-binder field-access match, which
/// `bind_match_fields` reads at index 0.
///
/// Weights are chosen so a wrong index is a different number, and every
/// read lives in the compiled source behind an accessor (a `#[test]` def
/// that reads a field takes the FIELD's LLVM type as its return type).
open IO {println}
use codegen::test::e2e_harness {compile_source_run_expect}

/// The minimal shape: rebuild a two-field struct, read both fields back.
/// Pre-fix both came back as field 0, giving 80 rather than 42.
#[test]
def test_struct_literal_reads_each_field_at_its_own_index : IO Bool :=
    let source := r#"struct S {
    a : I64,
    b : I64,
}
def rebuild (s : S) : S := { a := s.a, b := s.b : S }
def sa (s : S) : I64 := s.a
def sb (s : S) : I64 := s.b
def main (args : List String) : IO I64 := do {
    let r : S := rebuild ({ a := 40, b := 2 } : S);
    return (I64.add (sa r) (sb r))
}
"# in
    compile_source_run_expect source "test_struct_literal_reads_each_field_at_its_own_index" 42

/// Forge's own shape, scaled down: a list carried through a rebuild while a
/// sibling list is appended to. Pre-fix the appended list came back with
/// the OTHER field's elements in it, so the count was 3 rather than 1.
#[test]
def test_struct_rebuild_does_not_mix_two_list_fields : IO Bool :=
    let source := r#"struct Store {
    items : List I64,
    log : List I64,
}
def count (xs : List I64) : I64 := match xs {
    empty => 0,
    cons _ rest => I64.add 1 (count rest),
    _ => 0
}
def append_log (s : Store) (v : I64) : Store :=
    { items := s.items, log := List.append s.log [v] : Store }
def slog (s : Store) : List I64 := s.log
def sitems (s : Store) : List I64 := s.items
def main (args : List String) : IO I64 := do {
    let seeded : Store := { items := [7, 8, 9], log := [] : Store };
    let out : Store := append_log seeded 1;
    return (I64.add (I64.mul 10 (count (slog out))) (count (sitems out)))
}
"# in
    compile_source_run_expect source "test_struct_rebuild_does_not_mix_two_list_fields" 13
