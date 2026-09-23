/// Constructs that carry `Term.ctx` source-position wrappers in the places
/// placement rule R3 leaves exposed, so the transparency oracle
/// (`tools/debug_transparency_oracle.sh`) has something to check them on.
///
/// Every term carries its position on every path (`parse_all_decls`,
/// `lang/module.mo`). A wrapper must change what the compiler ANNOTATES and
/// never what it DECIDES, and R3 keeps wrappers out of an application's HEAD
/// but puts one on every ARGUMENT -- so argument-reading shape probes are
/// the exposed surface. Not one file in `examples/` used `++` before this
/// one, so that surface had no oracle coverage at all.
///
/// **What this file proves, and what it does not.** It proves the oracle's
/// actual property: for these shapes, a `--debug` build differs from a
/// `--release` one only by `!dbg` annotations. It does NOT catch the
/// carrier-inference gaps that motivated writing it -- verified, not
/// assumed: with the `term_peel` removed from `infer_carrier_type` or from
/// `term_matches_carrier` (`lang/scope.mo`), this file still compiles
/// clean.
///
/// The reason is worth knowing before writing another test like this. The
/// type checker's own class-method resolution (`resolve_class_method`,
/// `lang/typecheck/infer.mo`) is ctx-transparent for these shapes, and it
/// runs first. The syntactic carrier-inference pass in `lang/scope.mo` is
/// only load-bearing for a def whose ELABORATION failed, which
/// `elaborate_module_decls_best_effort` swallows silently and which in
/// practice needs the scale of the self-compile to happen at all. So:
///
///   - the corpus is the gate for `named_call_fields_of` and
///     `con_owner_name` (`slow_tests/codegen_named_call_*_tests.mo` and
///     `typecheck_init_tests.mo` each caught one);
///   - **the self-compile, in BOTH modes, is the only gate for the
///     carrier-inference gaps.** `monad compile cli/src/main.mo` without
///     `--release` is what found `Append.append`, and the `--release` one
///     found `FromListLiteral.empty`.
///
/// Each def below is still a shape a non-peeling probe reads:
///
///   `concat_computed`  a `++` whose LEFT operand is a CALL, not a literal
///                      -- the shape `infer_carrier_type`'s `Term.app` arm
///                      exists for.
///   `concat_local`     `++` on a local whose carrier comes from its
///                      declared type, via `lookup_local_type`.
///   `list_and_lookup`  a list literal desugars to `FromListLiteral.cons`/
///                      `.empty`, which have no argument to infer from, so
///                      the CLASS DEFAULT carrier is the only source -- and
///                      a class param's default is lowered as a value, so
///                      it is itself wrapped.
///   `sum_of_call`      a `match` whose scrutinee is a bare call, which is
///                      what `scrutinee_type_args` reads to enrich an arm's
///                      type environment.
///
/// Keep it compiling in BOTH modes: the oracle SKIPs a file that fails
/// either way, and a skipped case proves nothing.
#![mote { name := "located_terms", deps := [init, std] }]

use io {IO}
open IO {println}
use std::list {sum}

/// `++` with a computed left operand.
def concat_computed (x : I64) (suffix : String) : String :=
    I64.to_string x ++ suffix

/// `++` where the carrier comes from a local's declared type.
def concat_local (a : String) : String :=
    let b : String := "-" ++ a in
    b ++ "!"

/// A list literal (class-default carrier) plus a fold over it.
def list_and_lookup : I64 :=
    let xs : List I64 := [1, 2, 3] in
    List.sum xs

/// A `match` whose scrutinee is a bare call. `List.last` returns an
/// `Option I64`, so the arm env has a concrete type arg to lose.
def sum_of_call (xs : List I64) : I64 :=
    match List.last xs {
        Option.some v => v + List.sum xs,
        Option.none => 0,
    }

#[test]
def test_concat_computed : Bool :=
    String.beq (concat_computed 42 "x") "42x"

#[test]
def test_concat_local : Bool :=
    String.beq (concat_local "a") "-a!"

#[test]
def test_list_and_lookup : Bool :=
    list_and_lookup == 6

#[test]
def test_sum_of_call : Bool :=
    sum_of_call ([4, 5] : List I64) == 14

def main (args : List String) : IO Unit := do {
    println (concat_computed (list_and_lookup) " = sum");
    println (concat_local "located");
    println (I64.to_string (sum_of_call ([4, 5] : List I64)))
}
