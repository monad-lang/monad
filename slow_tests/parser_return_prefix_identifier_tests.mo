/// Regression tests for `tag_keyword` (`lang/parser/combinators.mo`):
/// the parser's own `return`-recognition sites (`do_stmt_return`,
/// `return_shorthand_parser`) used a bare `is_prefix`-based `tag "return"`
/// check with NO word-boundary check, so an ORDINARY identifier that
/// merely starts with the substring "return" (e.g. a def or local named
/// `return_foo`) was silently mis-parsed as the keyword `return` applied
/// to whatever remained after stripping the literal 6 characters --
/// `return_foo 41` parsed as `return (_foo 41)`.
///
/// This compiled and linked cleanly (both `_foo` -- an unrelated,
/// nonexistent local/def reference -- and the spurious `Monad.pure` wrap
/// are syntactically valid AST shapes) and only surfaced as a downstream
/// "unknown variable" or "undefined symbol" failure far from the actual
/// bug -- confirmed via `compile`'s own explicit typecheck gate
/// (`unknown variable '_foo'`) and, independently, via
/// `bootstrap compile lang/main.mo monad`'s self-compile hitting the
/// identical class of bug on `lang/scope.mo`'s own real
/// `return_type_after_n_args` (`llc: use of undefined value
/// '@Monad_pure'`, `lang/scope.mo:2189`'s call to it compiled to a call
/// to undefined `@_type_after_n_args` plus a spurious `@Monad_pure`
/// wrap) -- see `implementations/2026-08-29-return-prefixed-def-name-
/// mangled-with-spurious-monad-pure.md`.
///
/// Fixed by adding `tag_keyword` (checks a genuine word boundary --
/// end of input or a non-identifier character -- after the keyword tag
/// succeeds) and using it at both `return`-recognition call sites instead
/// of the bare `tag`.
use io {IO}
use lang.codegen.test.e2e_harness {compile_source_run_expect}


/// An ordinary, non-monadic def whose name starts with `return_`, called
/// as a plain `let`-bound expression -- the exact shape that used to
/// mis-parse as `return (_foo 41)`.
#[test]
def test_return_prefixed_def_name_ordinary_call : IO Bool :=
    let source := r#"def return_foo (x : I64) : I64 := x

def main (args : List String) : IO I64 := do {
    let y := return_foo 41;
    return y
}
"# in
    compile_source_run_expect source "test_return_prefixed_def_name_ordinary_call" 41

/// Same shape as a bare do-block STATEMENT (not `let`-bound) -- exercises
/// `do_stmt_return`'s own `tag_keyword` call, not just
/// `return_shorthand_parser`'s. `return_marker` must be `IO`-typed to be
/// a valid bare statement (mirrors `lang/main.mo`'s own established
/// `IO.write_file path content;` bare-statement idiom).
#[test]
def test_return_prefixed_def_name_bare_statement : IO Bool :=
    let source := r#"use io {IO}
def return_marker (x : I64) : IO Unit := IO.println (I64.to_string x)

def main (args : List String) : IO I64 := do {
    return_marker 0;
    return 7
}
"# in
    compile_source_run_expect source "test_return_prefixed_def_name_bare_statement" 7
