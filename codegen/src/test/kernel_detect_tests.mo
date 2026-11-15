/// `codegen::kernel::detect` -- one NEGATIVE test per subset rule.
///
/// ## Why every test here is a negative
///
/// A positive test ("this kernel is accepted") cannot see a rule that has
/// stopped firing: delete the rule's body and a well-formed kernel still
/// passes. So each test below builds the SMALLEST def that breaks exactly one
/// rule, asserts that `check_kernel` reports that rule by tag, and -- the part
/// that makes it a rule rather than a coincidence -- pairs it with a control
/// def differing only in the offending construct, which must report NOTHING.
///
/// The controls are written per rule rather than shared: one "good kernel"
/// reused by five tests would let a rule regress silently the moment the
/// shared fixture drifted into breaking that rule for an unrelated reason.
///
/// ## What is NOT tested here, and why
///
/// The plan's sixth rule -- "dimensions literal at the call site" -- is
/// deliberately absent. It is a property of the CALL, not of the def, so no
/// `Def`-shaped fixture can express it; `mono.mo`/`shape.mo` own it and will
/// carry its tests. `detect.mo`'s header says the same; this note is here so a
/// reader counting tests against rules finds the reason rather than a gap.

use lang::types {
    Attribute, Con, Decl, DebugName, Def, Identifier, Literal, Location,
    NamePath, NumSuffix, Param, SortLevel, Term, TypeConstraint, Visibility,
    binder_binder, binder_named, param_many, sentinel,
}
use lib::kernel::detect {
    KernelDiagnostic, KernelVerdict, check_kernel, check_kernels, extract_kernels,
}
use std::list {List.any, List.filter}

// ─── fixtures ────────────────────────────────────────────────────────

/// The `#[kernel]` attribute -- all discovery keys on.
def kernel_attr : List Attribute :=
    List.cons (Attribute.mk (Identifier.id "kernel") List.empty) List.empty

def no_attrs : List Attribute := List.empty

def bare_npath (s : String) : NamePath := NamePath.mk (List.cons (Identifier.id s) List.empty)

/// `I64`, as a term. A `con` with no args is how the corpus spells a nullary
/// type reference in a fixture (`compile_tests.mo`'s own `option_typ`).
def i64_ty : Term := Term.con (Con.mk (Identifier.id "I64") (bare_npath "I64") 0 List.empty)

/// A def with `attrs`, declared type `typ` and body `body`.
def mk (name : String) (typ : Term) (body : Term) (attrs : List Attribute) : Def :=
    Def.mk (bare_npath name) typ body ([] : List TypeConstraint) attrs
        Visibility.package_private List.empty

/// A `#[kernel]` def.
def kw (name : String) (typ : Term) (body : Term) : Def := mk name typ body kernel_attr

/// A `#[kernel]` def WITH a parameter list -- the shape every PARSED def has
/// and no `kw` fixture does.
///
/// This matters because `Def.params` is what bounds the peel
/// `def_param_chain_body` applies before the rules run: `kw` carries no
/// params, so its `term` is read as-is, while a parsed def's `term` is the
/// written body wrapped in one `Term.lam` per explicit parameter
/// (`lam_parsed_params`, `lang/parser.mo`). A fixture that wants to say
/// anything about the parsed shape therefore has to supply both halves --
/// the params AND the lambda chain -- which is what this constructor is for.
def kwp (name : String) (typ : Term) (params : List Param) (term : Term) : Def :=
    Def.mk (bare_npath name) typ term ([] : List TypeConstraint) kernel_attr
        Visibility.package_private params

/// One `(x : I64)` parameter, named `x`.
def p_i64 (x : String) : Param := param_many (Identifier.id x) i64_ty

/// `fn (a : I64) => fn (b : I64) => body` -- the parameter chain a parsed
/// TWO-parameter def's term is.
def param_chain2 (body : Term) : Term := lam "a" (lam "b" body)

/// The declared type of a plain kernel: one EXPLICIT argument, so the
/// polymorphism rule's control differs only in the binder's kind.
def i64_to_i64 : Term :=
    Term.pi (binder_named (Identifier.id "x")) i64_ty i64_ty

/// A body naming one global. `Term.var`'s `dbg` is the name carrier, and
/// `DebugName.named` is what `free_names.mo`'s collectors read.
def ref (name : String) : Term :=
    Term.var sentinel (DebugName.named (Identifier.id name))

/// `f a`.
def app (f : Term) (a : Term) : Term := Term.app f a

/// A BOUND variable at de Bruijn index `i` -- what a parameter reference
/// inside a parsed def's lambda chain looks like.
def bound (i : I64) : Term := Term.var i DebugName.unnamed

/// An `I64` literal.
def int_lit (v : I64) : Term := Term.lit (Literal.num v NumSuffix.i64)

/// A one-argument lambda over `x`.
def lam (arg : String) (body : Term) : Term :=
    Term.lam (binder_named (Identifier.id arg)) i64_ty body

/// The rule tags a diagnostic list reports, in order. Asserting the TAG is
/// right and asserting the prose is not: the tag is the stable identifier
/// (`detect.mo`'s own doc comment), while the prose is copy.
def rules_of (ds : List KernelDiagnostic) : List String := List.map (fn d => d.rule) ds

def has_rule (rule : String) (ds : List KernelDiagnostic) : Bool :=
    List.any (fn d => String.beq d.rule rule) ds

/// Exactly one diagnostic, and it carries `rule`. Asserting the COUNT as well
/// as the tag is what catches a rule that fires twice for one construct.
def reports_exactly (rule : String) (ds : List KernelDiagnostic) : Bool :=
    has_rule rule ds && List.length ds == 1

/// One `List String` element by index, `""` when out of range, so an ordering
/// test reads without an `Option` at each site.
def nth_or_empty (xs : List String) (i : I64) : String := match xs {
    List.empty => "",
    List.cons x rest => if i == 0 then x else nth_or_empty rest (i - 1),
}

def hd_or_default (ds : List KernelDiagnostic) : KernelDiagnostic := match ds {
    List.empty => KernelDiagnostic.of "" "" "",
    List.cons d _ => d,
}

/// Just the first name segment of a def -- for the discovery test.
def first_segment (d : Def) : String := match d {
    Def.mk {name, ..} => match name {
        NamePath.mk segments => match List.first segments {
            Option.none => "",
            Option.some id => match id { Identifier.id s => s },
        },
    },
}

// ─── discovery (the one positive direction, with its control) ────────

#[test]
def test_discovery_finds_the_marked_def_and_only_it : Bool :=
    let marked : Decl := Decl.def_d (kw "k" i64_to_i64 (ref "y"))
    in
    let plain : Decl := Decl.def_d (mk "f" i64_to_i64 (ref "y") no_attrs)
    in
    let found : List Def := extract_kernels [marked, plain]
    in
    List.length found == 1 && String.beq (first_segment (hd_def found)) "k"

def hd_def (ds : List Def) : Def := match ds {
    List.empty => mk "" i64_to_i64 (ref "") no_attrs,
    List.cons d _ => d,
}

/// A control for the control: an unmarked def alone yields nothing.
#[test]
def test_discovery_yields_nothing_without_the_attribute : Bool :=
    List.is_empty (extract_kernels [Decl.def_d (mk "f" i64_to_i64 (ref "y") no_attrs)])

// ─── rule 1: no IO ───────────────────────────────────────────────────

#[test]
def test_rule_io_fires_on_an_io_reference : Bool :=
    let body : Term := app (ref "IO.mk") (ref "x")
    in
    reports_exactly "io" (check_kernel (kw "k" i64_to_i64 body))

#[test]
def test_rule_io_is_silent_without_an_io_reference : Bool :=
    let body : Term := app (ref "f") (ref "x")
    in
    List.is_empty (check_kernel (kw "k" i64_to_i64 body))

/// `Cmd` is the second excluded effect, and it is a separate entry in the
/// name set -- an `IO`-only check would leave it open.
#[test]
def test_rule_io_fires_on_a_cmd_reference : Bool :=
    let body : Term := app (ref "Cmd.run") (ref "x")
    in
    reports_exactly "io" (check_kernel (kw "k" i64_to_i64 body))

// ─── rule 2: no closures ─────────────────────────────────────────────

#[test]
def test_rule_closure_fires_on_a_lambda : Bool :=
    reports_exactly "closure" (check_kernel (kw "k" i64_to_i64 (lam "y" (ref "y"))))

/// A PARSED def's term is a parameter lambda chain, and the closure rule must
/// NOT count it -- the bug this test exists for.
///
/// `def k (a : I64) (b : I64) : I64 := a` reaches the checker with `params`
/// holding two entries and `term` equal to `fn a => fn b => a`. Counting
/// lambdas over that term reports two closures on a kernel that contains
/// none, one per parameter. The fix is `def_param_chain_body`'s BOUNDED peel,
/// and the bound is the whole point: `test_rule_closure_fires_on_a_lambda`
/// above is the control that keeps an UNBOUNDED strip from being the answer.
#[test]
def test_rule_closure_is_silent_for_a_parsed_def_parameter_chain : Bool :=
    let typ : Term :=
        Term.pi (binder_named (Identifier.id "a")) i64_ty
            (Term.pi (binder_named (Identifier.id "b")) i64_ty i64_ty)
    in
    let body : Term := param_chain2 (bound 1)
    in
    let d : Def := kwp "k" typ [p_i64 "a", p_i64 "b"] body
    in
    List.is_empty (check_kernel d)

/// The same chain, with a REAL lambda underneath it: the peel removes exactly
/// the two parameter lambdas and leaves the body lambda for the rule to find.
/// A fixture with no params (like `kw`) cannot express this difference, which
/// is why `kwp` exists.
#[test]
def test_rule_closure_still_fires_below_a_parameter_chain : Bool :=
    let typ : Term :=
        Term.pi (binder_named (Identifier.id "a")) i64_ty
            (Term.pi (binder_named (Identifier.id "b")) i64_ty i64_ty)
    in
    let body : Term := param_chain2 (lam "y" (ref "y"))
    in
    let d : Def := kwp "k" typ [p_i64 "a", p_i64 "b"] body
    in
    reports_exactly "closure" (check_kernel d)

/// The other three body-walking rules read the same peeled term, so the
/// parameter chain must not hide a real violation either. `IO.mk` under the
/// chain is still IO.
#[test]
def test_rule_io_sees_through_a_parsed_def_parameter_chain : Bool :=
    let typ : Term := Term.pi (binder_named (Identifier.id "a")) i64_ty i64_ty
    in
    let body : Term := lam "a" (app (ref "IO.mk") (ref "x"))
    in
    let d : Def := kwp "k" typ [p_i64 "a"] body
    in
    reports_exactly "io" (check_kernel d)

/// And a self-reference under the chain is still recursion -- `self_referencing`
/// reads the peeled body too, so a kernel's own name may not hide in it.
#[test]
def test_rule_recursive_sees_through_a_parsed_def_parameter_chain : Bool :=
    let typ : Term := Term.pi (binder_named (Identifier.id "a")) i64_ty i64_ty
    in
    let body : Term := lam "a" (app (ref "k") (ref "a"))
    in
    let d : Def := kwp "k" typ [p_i64 "a"] body
    in
    reports_exactly "recursive" (check_kernel d)

#[test]
def test_rule_closure_is_silent_without_a_lambda : Bool :=
    List.is_empty (check_kernel (kw "k" i64_to_i64 (ref "y")))

/// A lambda NESTED under an application is still caught: the walk is over the
/// whole body, not only its head. This is what a shallow check would miss.
#[test]
def test_rule_closure_sees_a_nested_lambda : Bool :=
    let body : Term := app (ref "List.map") (lam "y" (ref "y"))
    in
    reports_exactly "closure" (check_kernel (kw "k" i64_to_i64 body))

/// A lambda at the HEAD of an application is a `let`, not a closure.
///
/// `let x := v in rest` desugars to the beta-redex `(fn x => rest) v`, which
/// the reducer substitutes away, so no closure value ever exists. Measured
/// against the real front end on 2026-11-15: a kernel whose body is only
/// `let i := 0 in n` was reported as a closure while containing none.
#[test]
def test_rule_closure_is_silent_for_a_let_shaped_head_lambda : Bool :=
    let body : Term := app (lam "i" (ref "n")) (int_lit 0)
    in
    List.is_empty (check_kernel (kw "k" i64_to_i64 body))

/// The control for the test above, and the reason the discriminator is
/// POSITION rather than reducibility: the SAME lambda moved into argument
/// position is a first-class function value, and must be refused. Both shapes
/// reduce to zero lambdas, so only the position separates them.
#[test]
def test_rule_closure_fires_when_the_same_lambda_is_an_argument : Bool :=
    let body : Term := app (ref "map_i64") (lam "i" (ref "n"))
    in
    reports_exactly "closure" (check_kernel (kw "k" i64_to_i64 body))

/// A lambda under a head lambda's BODY is still found: the head itself is not
/// counted, but the continuation is walked.
#[test]
def test_rule_closure_sees_a_lambda_inside_a_let_body : Bool :=
    let body : Term := app (lam "i" (lam "y" (ref "y"))) (int_lit 0)
    in
    reports_exactly "closure" (check_kernel (kw "k" i64_to_i64 body))

/// A lambda wrapped in a location must still be seen: `Term.ctx` is
/// documented as transparent to every shape test (`term_peel`'s own doc
/// comment), and a rule that peeked under a wrapper only at the TOP would
/// miss this one -- the wrapper is BELOW an application here.
#[test]
def test_rule_closure_sees_through_a_location_wrapper : Bool :=
    let loc : Location := Location.mk 0 1 1
    in
    let wrapped : Term := Term.ctx loc (lam "y" (ref "y"))
    in
    reports_exactly "closure" (check_kernel (kw "k" i64_to_i64 (app (ref "f") wrapped)))

// ─── rule 3: monomorphic ─────────────────────────────────────────────

/// An implicit binder -- `{A : Type} -> ...` -- is a quantifier, so refused.
#[test]
def test_rule_polymorphic_fires_on_an_implicit_binder : Bool :=
    let typ : Term := Term.pi (binder_binder (Identifier.id "A")) (Term.sort (SortLevel.concrete 1)) i64_to_i64
    in
    reports_exactly "polymorphic" (check_kernel (kw "k" typ (ref "y")))

/// The control differs ONLY in the binder's kind: an explicit pi is a plain
/// argument, not a quantifier, so nothing is reported.
#[test]
def test_rule_polymorphic_is_silent_for_an_explicit_pi : Bool :=
    List.is_empty (check_kernel (kw "k" i64_to_i64 (ref "y")))

/// A class constraint is the rule's other half, on a separate path: a def
/// whose declared type is monomorphic but which carries `[Copy A]` is refused
/// too, because a dictionary is an argument the extractor cannot supply.
#[test]
def test_rule_polymorphic_fires_on_a_class_constraint : Bool :=
    let c : TypeConstraint := TypeConstraint.mk (bare_npath "Copy") (List.cons (Identifier.id "A") List.empty)
    in
    let d : Def := Def.mk (bare_npath "k") i64_to_i64 (ref "y") (List.cons c List.empty)
        kernel_attr Visibility.package_private List.empty
    in
    reports_exactly "polymorphic" (check_kernel d)

// ─── rule 4: no recursion ────────────────────────────────────────────

/// A body naming the def's OWN symbol is recursion. That `def_name_str` and
/// `collect_referenced_names` share a name space is what this pins.
#[test]
def test_rule_recursive_fires_on_a_self_reference : Bool :=
    let body : Term := app (ref "k") (ref "x")
    in
    reports_exactly "recursive" (check_kernel (kw "k" i64_to_i64 body))

/// The control: the same body naming a DIFFERENT def is not recursion -- a
/// kernel may call a helper (which `mono.mo` inlines).
#[test]
def test_rule_recursive_is_silent_for_a_call_to_another_def : Bool :=
    let body : Term := app (ref "helper") (ref "x")
    in
    List.is_empty (check_kernel (kw "k" i64_to_i64 body))

// ─── rule 5: no allocation ───────────────────────────────────────────

/// The NAME half: `List.cons` mentioned in the body.
#[test]
def test_rule_alloc_fires_on_a_constructor_name : Bool :=
    let body : Term := app (ref "List.cons") (ref "x")
    in
    has_rule "alloc" (check_kernel (kw "k" i64_to_i64 body))

/// The STRUCTURAL half: a `Term.con` is a constructor application whose name
/// is `Con`-carried rather than a `var` reference, so the name test alone
/// cannot see it. This is the case that motivated two halves.
#[test]
def test_rule_alloc_fires_on_a_term_con : Bool :=
    let body : Term := Term.con (Con.mk (Identifier.id "some") (bare_npath "Option") 1 List.empty)
    in
    has_rule "alloc" (check_kernel (kw "k" i64_to_i64 body))

/// The other structural half: a struct literal that survived elaboration.
#[test]
def test_rule_alloc_fires_on_a_struct_literal : Bool :=
    let body : Term := Term.lit (Literal.struct_lit List.empty (Option.some (ref "Point")))
    in
    has_rule "alloc" (check_kernel (kw "k" i64_to_i64 body))

/// A constructor nested inside an `if` BRANCH. The branch lives inside
/// `Literal.if_`, not under a `Term` child, so a walk that stopped at
/// `Term.lit` would miss it entirely -- this is the test that pins the
/// literal-children arm.
#[test]
def test_rule_alloc_sees_a_constructor_inside_an_if_branch : Bool :=
    let some : Term := Term.con (Con.mk (Identifier.id "some") (bare_npath "Option") 1 List.empty)
    in
    let body : Term := Term.lit (Literal.if_ (ref "c") some (ref "e"))
    in
    has_rule "alloc" (check_kernel (kw "k" i64_to_i64 body))

/// The control for rule 5: a kernel that only writes through a buffer
/// allocates nothing, because the HOST allocates every `Buf` (the plan's
/// Decision 3, destination passing).
#[test]
def test_rule_alloc_is_silent_for_a_buffer_store : Bool :=
    let body : Term := app (app (ref "Buf.set_f32") (ref "b")) (ref "i")
    in
    List.is_empty (check_kernel (kw "k" i64_to_i64 body))

// ─── ordering and aggregation ────────────────────────────────────────

/// A def breaking two rules reports both, in the documented order. The order
/// is a stable interface (`check_kernel`'s doc comment says so), so it is
/// pinned rather than assumed.
#[test]
def test_check_kernel_reports_rules_in_the_documented_order : Bool :=
    let body : Term := app (ref "IO.mk") (lam "y" (ref "y"))
    in
    let rules : List String := rules_of (check_kernel (kw "k" i64_to_i64 body))
    in
    List.length rules == 2
        && String.beq (nth_or_empty rules 0) "io"
        && String.beq (nth_or_empty rules 1) "closure"

/// A clean kernel produces nothing at all -- the fully-positive control that
/// every rule above is a difference from.
#[test]
def test_a_clean_kernel_reports_nothing : Bool :=
    let body : Term := app (ref "Buf.set_f32") (ref "x")
    in
    List.is_empty (check_kernel (kw "k" i64_to_i64 body))

/// `check_kernels` covers every marked def and reports exactly the marked
/// ones' problems: the unmarked def in the list contributes nothing even
/// though its body is recursive.
#[test]
def test_check_kernels_covers_only_marked_defs : Bool :=
    let bad : Decl := Decl.def_d (kw "bad" i64_to_i64 (ref "bad"))
    in
    let good : Decl := Decl.def_d (kw "good" i64_to_i64 (ref "y"))
    in
    let unmarked : Decl := Decl.def_d (mk "plain" i64_to_i64 (ref "plain") no_attrs)
    in
    List.length (check_kernels [bad, good, unmarked]) == 1

/// The rendered message carries the kernel's name and the rule's prose -- the
/// shape the plan specifies, and the only thing a user sees.
#[test]
def test_render_names_the_kernel_and_the_rule : Bool :=
    let body : Term := app (ref "IO.mk") (ref "x")
    in
    let rendered : String := KernelDiagnostic.render (hd_or_default (check_kernel (kw "foo" i64_to_i64 body)))
    in
    rendered == "kernel 'foo' performs IO; kernels must be pure at IO.mk"

// ─── the verdict summary ─────────────────────────────────────────────

#[test]
def test_verdict_is_ok_for_a_clean_kernel : Bool :=
    KernelVerdict.ok (KernelVerdict.of (kw "k" i64_to_i64 (ref "y")))

#[test]
def test_verdict_is_not_ok_for_a_dirty_kernel : Bool :=
    Bool.not (KernelVerdict.ok (KernelVerdict.of (kw "k" i64_to_i64 (ref "k"))))
