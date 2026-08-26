use lang.core_eval {basic_native_table, eval}
use lang.core_ir {CoreIr, IrLit}
use lang.core_value {GlobalTable, Value, global_cache_new, global_table_len}
use lang.lower_core_ir {LowerCtx, lower_ctx_from_decls, lower_root}
use lang.types {AttrArg, Attribute, DebugName, ModulePath, Term}

/// End-to-end tests: real checked `Term` -> `LowerCtx` (built via
/// `lang.lower_core_ir.lower_ctx_from_decls`, which itself calls
/// `lang.scope.build_scope_from_decls` -- the same machinery the actual
/// self-hosted type checker's module loader uses) -> `lang.lower_core_ir`
/// -> `lang.core_eval`. Where `lang/core_eval.mo`'s own tests hand-build
/// `CoreIr` directly (exercising only the evaluator), and
/// `lang/lower_core_ir.mo`'s own tests exercise only pure helpers with no
/// real `Scope`, these tests hand-build checked `Term`/`Decl` values (the
/// same de-Bruijn shape `lang/typecheck/infer.mo` actually produces --
/// see e.g. `lang/tests/scope_tests.mo` for the same
/// hand-built-`Decl`-against-real-`Scope`-machinery style) and drive the
/// *whole* new pipeline through `lang.scope`'s real name/inductive
/// resolution, proving `lang/lower_core_ir.mo` actually integrates with
/// it, not just with its own mocks.
///
/// This is deliberately not "parse real .mo source text" end-to-end --
/// that would additionally exercise the surface parser and the
/// TermV0->Term elaborator, neither of which this evaluator plan is
/// about. Hand-building the checked `Term` is exactly what a real
/// `Def.term` already looks like post-elaboration (de Bruijn locals,
/// `Term.var sentinel (DebugName.named id)` for anything free) -- see
/// `lang/typecheck/infer.mo:329-343`.
///
/// Note: `lang/lower_core_ir.mo`'s `LowerCtx` reads def bodies from its
/// own flat `List Def` (built by `lower_ctx_from_decls` from these same
/// `decl_list`), not from `Scope`/`scope_resolve_name` -- confirmed directly
/// that `lang/scope.mo`'s `build_scope_def` always stores `body :=
/// Term.hole` in scope, never the real `Def.term`. See
/// `lang/lower_core_ir.mo`'s own doc comment.

def sentinel : I64 := -1

def mp1 (s : String) : ModulePath := ModulePath.mp [Identifier.id s]

def named (s : String) : DebugName := DebugName.named (Identifier.id s)

def free_var (s : String) : Term := Term.var sentinel (named s)

def num (n : I64) : Term := Term.lit (Literal.num n NumSuffix.i64)

def def_decl (name : String) (term : Term) : Decl :=
  Decl.def_d (Def.mk (mp1 name) Term.hole term List.empty List.empty Visibility.package_private)

def build_ctx (decl_list : List Decl) : LowerCtx :=
  lower_ctx_from_decls (mp1 "test") decl_list

/// Lower `root`'s body against `ctx` and evaluate it to a `Value`,
/// against the (real, worklist-built) `GlobalTable` `lower_root` returns.
def lower_and_run (ctx : LowerCtx) (root : String) : Option Value :=
  match lower_root ctx (mp1 root) {
    Result.err _ => Option.none,
    Result.ok pr => run_lowered pr,
  }

def run_lowered (pr : Pair CoreIr GlobalTable) : Option Value :=
  match pr {
    Pair.pair ir globals =>
      match eval ir Env.env_nil globals basic_native_table (global_cache_new (global_table_len globals)) {
        Pair.pair r _ =>
          match r {
            Result.ok v => Option.some v,
            Result.err _ => Option.none,
          },
      },
  }

def value_num_is (v : Value) (expected : I64) : Bool :=
  match v {
    Value.v_lit l => irlit_num_is l expected,
    _ => false,
  }

def irlit_num_is (l : IrLit) (expected : I64) : Bool :=
  match l {
    IrLit.ir_num n _ => I64.beq n expected,
    _ => false,
  }

def opt_value_num_is (ov : Option Value) (expected : I64) : Bool :=
  match ov {
    Option.some v => value_num_is v expected,
    Option.none => false,
  }

// ─── Test 1: an escaping closure that captures an outer global's arg ───
// The exact shape the OLD self-hosted evaluator (lang/eval.mo) gets
// wrong: `const_fn` returns an inner lambda that must still see the
// outer lambda's parameter once applied later, from a completely
// different call site (`main`'s own environment, not const_fn's).

def const_fn_term : Term :=
  // fn x => fn y => x
  Term.lam (named "x") Term.hole
    (Term.lam (named "y") Term.hole
      (Term.var 1 (named "x")))

def closure_main_term : Term :=
  // const_fn 111 222 -- must yield 111, proving the inner lambda closed
  // over x=111 rather than reading whatever's live at the *application*
  // site.
  Term.app (Term.app (free_var "const_fn") (num 111)) (num 222)

def closure_test_decls : List Decl :=
  [def_decl "const_fn" const_fn_term, def_decl "main" closure_main_term]

#[test]
def test_escaping_closure_captures_global_arg_end_to_end : Bool :=
  opt_value_num_is (lower_and_run (build_ctx closure_test_decls) "main") 111

// ─── Test 2: self-recursive addition over a hand-built 2-constructor ───
// inductive, dispatched through match_ -- the two other gaps found in
// the old evaluator (erecursor was an unevaluated stub; econst had no
// real global table at all).

def mynat_path : ModulePath := mp1 "MyNat"

def z_ctor : InductConstructor := InductConstructor.mk (mp1 "z") List.empty Term.hole
def s_ctor : InductConstructor := InductConstructor.mk (mp1 "s") List.empty Term.hole

def mynat_decl : Decl :=
  Decl.inductive_d (Inductive.mk mynat_path List.empty Term.hole [z_ctor, s_ctor] List.empty Visibility.package_private)

def mynat_z : Term := Term.con (Con.mk (Identifier.id "z") mynat_path 0 List.empty)

def mynat_s (n : Term) : Term := Term.con (Con.mk (Identifier.id "s") mynat_path 1 [Option.some n])

/// def my_add (a b : MyNat) : MyNat := match a { z => b, s n => s (my_add n b) }
def my_add_term : Term :=
  Term.lam (named "a") Term.hole
    (Term.lam (named "b") Term.hole
      (Term.lit (Literal.match_
        (Term.var 1 (named "a"))
        [
          MatchCase.mc (Identifier.id "z") List.empty (Term.var 0 (named "b")) Option.none,
          MatchCase.mc (Identifier.id "s") [Identifier.id "n"]
            (mynat_s (Term.app (Term.app (free_var "my_add") (Term.var 0 (named "n"))) (Term.var 1 (named "b")))) Option.none,
        ])))

def two_term : Term := mynat_s (mynat_s mynat_z)
def one_term : Term := mynat_s mynat_z

def add_main_term : Term :=
  // my_add 2 1 -- should reduce to 3 = s (s (s z))
  Term.app (Term.app (free_var "my_add") two_term) one_term

def recursion_test_decls : List Decl :=
  [mynat_decl, def_decl "my_add" my_add_term, def_decl "main" add_main_term]

/// Count how deep a `s (s (... z))` chain goes -- `z`'s tag is 0 (first
/// declared), `s`'s tag is 1 (second declared), matching `mynat_decl`'s
/// constructor order.
#[partial]
def count_succ (v : Value) : Option I64 :=
  match v {
    Value.v_con tag args =>
      if I64.beq tag 0
      then Option.some 0
      else count_succ_s args,
    _ => Option.none,
  }

#[partial]
def count_succ_s (args : List Value) : Option I64 :=
  match args {
    List.cons inner _ =>
      match count_succ inner {
        Option.some n => Option.some (n + 1),
        Option.none => Option.none,
      },
    List.empty => Option.none,
  }

#[test]
def test_self_recursive_match_over_custom_inductive_end_to_end : Bool :=
  match lower_and_run (build_ctx recursion_test_decls) "main" {
    Option.some v =>
      match count_succ v {
        Option.some n => I64.beq n 3,
        Option.none => false,
      },
    Option.none => false,
  }

// ─── Test 3: if, end-to-end through lower_root/eval ─────────────────────
// `lower_if` compiles `Literal.if_` straight to `match_` against Bool's
// two well-known tags (true=0, false=1 -- hardcoded, matching
// lang/core_eval.mo's `bool_value`; see both files' doc comments), so it
// doesn't itself need Bool registered in scope -- but the *condition*
// here is a real `true` constructor VALUE (`Term.con`), and lowering a
// `Con` always resolves its inductive via `scope_find_inductive`
// (`lower_con`), so a minimal `Bool` inductive `Decl` is still needed for
// this specific test term to lower at all.

def bool_path : ModulePath := mp1 "Bool"
def true_ctor : InductConstructor := InductConstructor.mk (mp1 "true") List.empty Term.hole
def false_ctor : InductConstructor := InductConstructor.mk (mp1 "false") List.empty Term.hole

def bool_decl : Decl :=
  Decl.inductive_d (Inductive.mk bool_path List.empty Term.hole [true_ctor, false_ctor] List.empty Visibility.package_private)

def bool_true : Term := Term.con (Con.mk (Identifier.id "true") bool_path 0 List.empty)

/// if true then 100 else 200
def if_main_term : Term := Term.lit (Literal.if_ bool_true (num 100) (num 200))

def if_test_decls : List Decl := [bool_decl, def_decl "main" if_main_term]

#[test]
def test_if_end_to_end : Bool :=
  opt_value_num_is (lower_and_run (build_ctx if_test_decls) "main") 100

// ─── Test 4: a point-free (unapplied) constructor reference ────────────
// `lang/lower_core_ir.mo`'s `lower_free_var_fallback` -- a nullary
// constructor referenced as a bare VALUE (never applied at this
// occurrence, e.g. `List.empty` used directly as a function's own
// return value) has no `scope_resolve_name` def-name entry, only a
// `scope_find_inductive` constructor-table one. Mirrors the exact shape
// `reflect_type_info!`'s meta-eval hits constantly (every real
// `List`-processing stdlib function's own empty-case body).

def mylist_path : ModulePath := mp1 "MyList"
def mynil_ctor : InductConstructor := InductConstructor.mk (mp1 "mynil") List.empty Term.hole
def hd_param : Param := Param.mk (Identifier.id "hd") Term.hole Multiplicity.many Option.none List.empty
def tl_param : Param := Param.mk (Identifier.id "tl") Term.hole Multiplicity.many Option.none List.empty

def mycons_ctor : InductConstructor :=
  InductConstructor.mk (mp1 "mycons") [hd_param, tl_param] Term.hole

def mylist_decl : Decl :=
  Decl.inductive_d (Inductive.mk mylist_path List.empty Term.hole [mynil_ctor, mycons_ctor] List.empty Visibility.package_private)

/// `def empty_case (n : I64) : MyList := MyList.mynil` -- ignores its
/// own arg entirely and returns the bare, unapplied nullary
/// constructor -- exactly the shape a `List.map`/`List.filter`-style
/// function's own empty-input case takes.
def empty_case_term : Term :=
  Term.lam (named "n") Term.hole (free_var "MyList.mynil")

def point_free_ctor_test_decls : List Decl :=
  [mylist_decl, def_decl "empty_case" empty_case_term, def_decl "main" (Term.app (free_var "empty_case") (num 0))]

#[test]
def test_point_free_nullary_constructor_reference_end_to_end : Bool :=
  match lower_and_run (build_ctx point_free_ctor_test_decls) "main" {
    Option.some v => is_con_with_tag_and_arity v 0 0,
    Option.none => false,
  }

def is_con_with_tag_and_arity (v : Value) (expected_tag : I64) (expected_arity : I64) : Bool :=
  match v {
    Value.v_con tag args => I64.beq tag expected_tag && I64.beq (List.length args) expected_arity,
    _ => false,
  }

// ─── Test 5: a native-attributed stub def referenced as a free var ────
// `lang/lower_core_ir.mo`'s `lower_one_global` -- `#[native i64_add]
// def add_native (a b : I64) : I64` (no `:=` body at all -- mirrors
// EVERY real native stdlib def, e.g. `init/string.mo`'s own
// `#[native string_concat] def String.concat (a b : String) : String`)
// parses to `.term = lam a (lam b Term.hole)`; calling it must resolve
// via `GlobalDef.gd_native`, not try (and fail) to lower that
// placeholder `Term.hole` as an ordinary body.

def native_attr : List Attribute := [Attribute.mk (Identifier.id "native") [AttrArg.ident (Identifier.id "i64_add")]]

def add_native_term : Term := Term.lam (named "a") Term.hole (Term.lam (named "b") Term.hole Term.hole)
def add_native_decl : Decl := Decl.def_d (Def.mk (mp1 "add_native") Term.hole add_native_term List.empty native_attr Visibility.package_private)

def native_stub_main_term : Term :=
  // add_native 3 4 -- should reduce to 7 via the SAME i64_add native
  // `add_one_term`'s own hand-lowered `Term.ntv` uses directly.
  Term.app (Term.app (free_var "add_native") (num 3)) (num 4)

def native_stub_test_decls : List Decl :=
  [add_native_decl, def_decl "main" native_stub_main_term]

#[test]
def test_native_attributed_stub_def_referenced_as_free_var_end_to_end : Bool :=
  opt_value_num_is (lower_and_run (build_ctx native_stub_test_decls) "main") 7

// ─── Test 6: a BARE (`open`-aliased) constructor reference used as a ───
// global -- `lang/lower_core_ir.mo`'s `lower_one_global` own new
// fallback. Different from Test 4: `open MyList {mynil}` makes bare
// "mynil" (no "MyList." qualifier at all) resolve SUCCESSFULLY via
// `scope_resolve_name` (unlike Test 4's "MyList.mynil", which fails
// outright and goes through `lower_free_var`'s OWN fallback instead) --
// but the resolved path still has no ordinary `Def`, so it's
// `lower_one_global` (reached once `process_pending`'s worklist tries
// to lower the INTERNED global's own body), not `lower_free_var`, that
// has to fall back to constructor-owner lookup. Mirrors the exact
// shape `std/derive.mo`'s `open Decl {d_def, d_instance}` hits.

def open_mynil_decl : Decl := Decl.open_d mylist_path (OpenFilter.open_only [Identifier.id "mynil"])

def bare_ctor_global_test_decls : List Decl :=
  [mylist_decl, open_mynil_decl, def_decl "empty_case" (Term.lam (named "n") Term.hole (free_var "mynil")), def_decl "main" (Term.app (free_var "empty_case") (num 0))]

#[test]
def test_bare_open_aliased_constructor_reference_as_global_end_to_end : Bool :=
  match lower_and_run (build_ctx bare_ctor_global_test_decls) "main" {
    Option.some v => is_con_with_tag_and_arity v 0 0,
    Option.none => false,
  }

// ─── Test 7: a 3-field constructor match, extracting the MIDDLE field ──
// Every existing fixture above only matches 0-2-field constructors --
// `init/meta.mo`'s `field_info (name) (typ) (attrs)` (3 fields) is the
// first real 3+-field constructor match this evaluator has been
// exercised against. Isolates whether multi-field binder-index
// assignment is correct in general (independent of
// `reflect_type_info!`'s own much larger call graph).

def triple_path : ModulePath := mp1 "Triple"
def a_param : Param := Param.mk (Identifier.id "a") Term.hole Multiplicity.many Option.none List.empty
def b_param : Param := Param.mk (Identifier.id "b") Term.hole Multiplicity.many Option.none List.empty
def c_param : Param := Param.mk (Identifier.id "c") Term.hole Multiplicity.many Option.none List.empty
def triple_ctor : InductConstructor := InductConstructor.mk (mp1 "triple_mk") [a_param, b_param, c_param] Term.hole
def triple_decl : Decl := Decl.inductive_d (Inductive.mk triple_path List.empty Term.hole [triple_ctor] List.empty Visibility.package_private)

def triple_con (x y z : Term) : Term :=
  Term.con (Con.mk (Identifier.id "triple_mk") triple_path 3 [Option.some x, Option.some y, Option.some z])

/// `def get_b (t : Triple) : I64 := match t { triple_mk a b c => b }`
def get_b_term : Term :=
  Term.lam (named "t") Term.hole
    (Term.lit (Literal.match_
      (Term.var 0 (named "t"))
      [MatchCase.mc (Identifier.id "triple_mk") [Identifier.id "a", Identifier.id "b", Identifier.id "c"] (Term.var 1 (named "b")) Option.none]))

def get_b_main_term : Term :=
  Term.app (free_var "get_b") (triple_con (num 10) (num 20) (num 30))

def three_field_test_decls : List Decl :=
  [triple_decl, def_decl "get_b" get_b_term, def_decl "main" get_b_main_term]

#[test]
def test_three_field_constructor_match_extracts_middle_field : Bool :=
  opt_value_num_is (lower_and_run (build_ctx three_field_test_decls) "main") 20
