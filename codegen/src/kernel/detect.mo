/// `#[kernel]` discovery and the kernel-subset checker.
///
/// ## What this module is for
///
/// `#[kernel]` is a *promise about a function's body*: it says the body is
/// inside a small, closed, first-order, allocation-free subset that the MLIR
/// backend (`codegen/src/kernel/`, `plans/bootstrapping/mlir-codegen.md`
/// Phase 2) can lower to `scf`/`arith`/`memref` and run on a CPU or a GPU.
/// This module is what makes that promise checkable, and it is the only thing
/// that makes it a promise at all.
///
/// ## Why the annotation is inert without this file
///
/// Attributes in Monad are an *open* set: `lang/src/` has no attribute
/// vocabulary, no validation, and no `kernel` string anywhere. A
/// `#[kernel] def f ...` therefore parses and compiles as an ordinary def
/// today, and the interpreter runs its body. That is a convenience -- it is
/// exactly what gives this plan its reference-body oracle, for free, from the
/// first minute -- but it also means the annotation currently *guarantees
/// nothing*: a kernel that performs IO, recurses, or is polymorphic is
/// accepted in silence. The rules below are what turn the annotation into a
/// rule, and the negative tests beside them are what keep the rules firing.
///
/// ## The subset, and which half this file owns
///
/// The plan's six rules split cleanly into two kinds, and saying so is worth
/// more than pretending they are uniform:
///
/// | Rule | Decidable from | Where |
/// |---|---|---|
/// | No `IO`/`Cmd` in the body | the def alone | **here** |
/// | No closures; all calls direct | the def alone | **here** |
/// | No `Forall` binders, empty constraints | the def alone | **here** |
/// | No recursion | the def alone | **here** |
/// | No GC allocation (`List`, boxed ADT construction) | the def alone | **here** |
/// | Dimensions literal at the call site | the CALL SITE | `mono.mo` (`dim` tag) -- NOT here |
///
/// The last row is the honest one: a kernel's trip count is a property of how
/// it was *called*, so no walk over its own body can decide it. The extractor
/// folds the literal at the call site (`mono.mo`), and `shape.mo` turns the
/// folded value into a `memref` dimension. Claiming this rule here would be
/// claiming a check that cannot fire.
///
/// ## Shape
///
/// `KernelDiagnostic` rather than a `TypeError`: these are *codegen* rules,
/// they live in `codegen/`, and the messages the plan specifies are phrased
/// about the kernel (`kernel 'foo' performs IO at ...`), not about types. A
/// `CodegenError` would be the wrong channel too -- that type is per-compile
/// and failure-branded, while a kernel produces a *list* of per-rule findings
/// that the `monad kernels` subcommand prints together.
///
/// ## Traversal discipline
///
/// Every walk here is hand-rolled over an explicit `value_children` rather than
/// routed through `term_map_children`, for two reasons: that function REBUILDS
/// (a listing walk wants the children, not a copy of the term with them
/// replaced), and a rule that runs per kernel should not pay for a rebuild.
/// `value_children` is also the one place that has to grow when `Term` gains a
/// variant -- the same maintenance point `free_names.mo` and `emit.mo` have.

use lang::types {
    Decl, Def, Elim, Identifier, Literal, MatchCase, NamePath, StructLitField,
    Term, binder_is_explicit, term_peel,
}
use lib::decls {def_attrs, def_body_term, def_name_str, extract_defs}
use lib::attrs {find_attr_args}
use lib::free_names {collect_referenced_names}
use lib::symbols {def_symbol_name}
use std::list {List.filter}

/// One reason a `#[kernel]` def is outside the subset.
///
/// A record rather than a rendered string, so a caller can group, count or
/// filter findings without re-parsing text -- `monad kernels` prints them, and
/// the Phase 2 extractor will refuse to emit for any kernel that has one.
/// `rule` is the stable identifier (tests and the CLI match on it), `detail`
/// names the offending thing, and `render` is what a user reads.
pub struct KernelDiagnostic {
    /// The kernel's own name, as written.
    kernel : String,
    /// A stable rule tag: `io` | `closure` | `polymorphic` | `recursive` |
    /// `alloc` | `dim` (the last is reported by `mono.mo`, a CALL-SITE
    /// property -- see the module header's rule table).
    rule : String,
    /// The offending construct, or `""` when the rule is about the def as a
    /// whole (polymorphism, recursion).
    detail : String,
}

pub def KernelDiagnostic.of (kernel : String) (rule : String) (detail : String) : KernelDiagnostic :=
    KernelDiagnostic.mk kernel rule detail

/// The one-line message, in the plan's own shapes:
/// `kernel 'foo' performs IO at println`.
pub def KernelDiagnostic.render (d : KernelDiagnostic) : String :=
    String.concat_all ["kernel '", d.kernel, "' ", rule_message d.rule,
        (if String.is_empty d.detail then "" else String.concat " at " d.detail)]

/// The half of the message after `kernel 'foo' `. Split out because a test
/// pins the prose, and the rule tag is not the prose.
def rule_message (rule : String) : String :=
    if String.beq rule "io" then "performs IO; kernels must be pure"
    else if String.beq rule "closure" then "captures a value; kernels must be first-order"
    else if String.beq rule "polymorphic" then "is polymorphic; kernels must be monomorphic"
    else if String.beq rule "recursive" then "is recursive; use a bounded loop"
    else if String.beq rule "alloc" then "allocates; kernels must be allocation-free"
    else if String.beq rule "dim" then "is called with a non-literal dimension; kernels need static shapes"
    else String.concat rule " is not allowed in a kernel"

/// Is this def marked `#[kernel]`?
pub def is_kernel (d : Def) : Bool :=
    match find_attr_args "kernel" (def_attrs d) {
        Option.some _ => true,
        Option.none => false,
    }

/// Every `#[kernel]` def in `decl_list`, in declaration order.
///
/// Keeping discovery here means "what is a kernel" has exactly one answer in
/// the compiler: the extractor, the `monad kernels` subcommand and these
/// rules all read this list.
#[partial]
pub def extract_kernels (decl_list : List Decl) : List Def :=
    List.filter (fn d => is_kernel d) (extract_defs decl_list)

/// Every diagnostic for every kernel in `decl_list`, in declaration order.
#[partial]
pub def check_kernels (decl_list : List Decl) : List KernelDiagnostic :=
    check_kernels_go (extract_kernels decl_list)

#[partial]
def check_kernels_go (kernels : List Def) : List KernelDiagnostic := match kernels {
    List.empty => List.empty,
    List.cons d rest => List.append (check_kernel d) (check_kernels_go rest),
}

/// Every diagnostic for one kernel, in a fixed rule order -- io, closure,
/// polymorphic, recursive, alloc -- so a golden test over a def that breaks
/// three rules is stable, and so a reader sees the most structural problem
/// first.
#[partial]
pub def check_kernel (d : Def) : List KernelDiagnostic :=
    let name : String := def_name_str d in
    let body : Term := def_body_term d in
    List.append (io_diags name body)
        (List.append (closure_diags name body)
            (List.append (polymorphic_diags name d)
                (List.append (recursion_diags name d) (alloc_diags name body))))

// ─── rule 1: no IO ───────────────────────────────────────────────────
//
// A device has no host runtime, so an `IO`/`Cmd` value in a kernel body is
// unreachable by construction. The test is structural: an `IO.mk`, `IO.delay`
// or `Cmd.` reference anywhere in the body. Deliberately a NAME test rather
// than a type test -- an elaborated kernel body has no `IO` phantom to ask
// about, and a kernel is a small, first-order body where a name is precise
// enough to be actionable.

/// Names whose presence in a kernel body means "this performs IO". `IO.mk` and
/// `IO.delay` are the two ways an `IO A` is built; `Cmd` is the second effect
/// type the subset excludes.
def io_names : List String := [
    "IO.mk", "IO.delay", "IO.bind", "Cmd.run", "Cmd.perform",
]

#[partial]
def io_diags (kernel : String) (body : Term) : List KernelDiagnostic :=
    map_names kernel "io" (names_in body io_names)

/// One diagnostic per offending name, tagged with `rule`.
#[partial]
def map_names (kernel : String) (rule : String) (names : List String) : List KernelDiagnostic := match names {
    List.empty => List.empty,
    List.cons n rest =>
        List.cons (KernelDiagnostic.of kernel rule n) (map_names kernel rule rest),
}

// ─── rule 2: no closures ─────────────────────────────────────────────
//
// No function pointers exist in the emitted dialect, and a captured
// environment would need heap for the closure record. A `Term.lam` inside a
// kernel body is therefore rejected: a kernel is first-order. A lambda in a
// sub-expression (`List.map (fn x => ...)`) is caught by the same test, which
// is the intent -- it is exactly the closure the rule is about.

#[partial]
def closure_diags (kernel : String) (body : Term) : List KernelDiagnostic :=
    let n := lambda_count body 0 in
    if I64.beq n 0
    then List.empty
    else single kernel "closure" (String.concat (I64.to_string n) " lambda")

// ─── rule 3: monomorphic ─────────────────────────────────────────────
//
// The checker REJECTS polymorphism rather than specialising it: a general
// monomorphiser is its own plan, and putting one on this plan's critical path
// would double its size. So a kernel whose declared type has a non-explicit
// binder on its outer pi spine (`{A : Type}`, `{u : Universe}`) is refused, as
// is one carrying a class constraint.

#[partial]
def polymorphic_diags (kernel : String) (d : Def) : List KernelDiagnostic :=
    match d {
        Def.mk {name := _n, typ, term := _t, constraints, attrs := _a, vis := _v, ..} =>
            if polymorphic_type typ
            then single kernel "polymorphic" ""
            else if Bool.not (List.is_empty constraints)
            then single kernel "polymorphic"
                (String.concat (I64.to_string (List.length constraints)) " class constraint")
            else List.empty,
    }

def single (kernel : String) (rule : String) (detail : String) : List KernelDiagnostic :=
    List.cons (KernelDiagnostic.of kernel rule detail) List.empty

/// Whether a def type binds a non-explicit binder anywhere on its outer pi
/// spine -- i.e. `{A : Type}` or `{u : Universe}`.
#[partial]
def polymorphic_type (typ : Term) : Bool := match term_peel typ {
    Term.pi b _arg ret => if binder_is_explicit b then polymorphic_type ret else true,
    _ => false,
}

// ─── rule 4: no recursion ────────────────────────────────────────────
//
// A termination proof is not a trip count (the plan's Decision 5): `scf.for`
// needs a closed-form bound, and `#[decreasing]` shows only that a recursion
// halts. Kernels therefore permit NO recursion, and a kernel whose body names
// its own symbol is refused. `mono.mo`'s inlining is what then makes a
// bounded-loop helper callable -- it inlines the callee's body rather than
// calling it, so a helper that recurses is caught HERE on the helper's own def.

#[partial]
def recursion_diags (kernel : String) (d : Def) : List KernelDiagnostic :=
    if self_referencing d then single kernel "recursive" "" else List.empty

/// Whether the def's body names the def's own symbol.
///
/// `def_name_str` (an llvm-symbol spelling) on the def side, and
/// `collect_referenced_names` on the body side, are the same name space --
/// exactly the pairing `codegen/src/decls.mo`'s reachability walk uses, and
/// for the same reason.
#[partial]
def self_referencing (d : Def) : Bool :=
    let own : String := def_name_str d in
    name_present own (collect_referenced_names (def_body_term d) List.empty)

#[partial]
def name_present (name : String) (names : List String) : Bool := match names {
    List.empty => false,
    List.cons n rest => if String.beq n name then true else name_present name rest,
}

// ─── rule 5: no allocation ───────────────────────────────────────────
//
// No collector on a device, so a kernel may not construct a boxed value: no
// `List.cons`, no `Option.some`, no `String.from_list`, no constructor
// application, no struct literal. Two halves, because neither alone is enough:
// a NAME test catches the prelude constructors a kernel would reach for, and a
// STRUCTURAL test catches a `Term.con` / `Literal.struct_lit` the name test
// cannot see (a constructor application's name is `Con`-carried, not a `var`).
//
// `Buf` is the permitted storage and is NOT an allocation: every buffer is
// allocated by the HOST and passed in (the plan's Decision 3, destination
// passing), so a kernel writing through a `Buf` argument constructs nothing.

/// Constructor names that allocate. Not exhaustive over the prelude -- it is
/// the set a kernel would plausibly reach for, and the structural half below
/// catches the rest.
def allocating_names : List String := [
    "List.cons", "Option.some", "String.from_list",
]

#[partial]
def alloc_diags (kernel : String) (body : Term) : List KernelDiagnostic :=
    List.append (map_names kernel "alloc" (names_in body allocating_names))
        (structural_alloc_diags kernel body)

/// The structural half of rule 5: a constructor application or a surviving
/// struct literal anywhere in the body, reported as one finding.
///
/// `Literal.struct_lit` is the annotated form that survives best-effort
/// elaboration; the backends already reject every survivor fail-fast for a
/// different reason, so a kernel is not a special case here, just an earlier
/// report.
#[partial]
def structural_alloc_diags (kernel : String) (body : Term) : List KernelDiagnostic :=
    let n := alloc_count body 0 in
    if I64.beq n 0
    then List.empty
    else single kernel "alloc" (String.concat (I64.to_string n) " construction")

/// How many allocation-shaped nodes a term contains: a `Term.con` (which IS a
/// constructor application in an elaborated term) or an allocating literal.
#[partial]
def alloc_count (t : Term) (acc : I64) : I64 :=
    match term_peel t {
        Term.con _c => alloc_count_all (value_children t) (acc + 1),
        Term.lit l => if lit_allocates l
            then alloc_count_all (value_children t) (acc + 1)
            else alloc_count_all (value_children t) acc,
        _ => alloc_count_all (value_children t) acc,
    }

#[partial]
def alloc_count_all (children : List Term) (acc : I64) : I64 := match children {
    List.empty => acc,
    List.cons c rest => alloc_count_all rest (alloc_count c acc),
}

/// Whether a literal builds a heap value. Only `struct_lit` does: `if_`/`match_`
/// are walkers whose children carry the answer, and a scalar literal is not a
/// construction.
def lit_allocates (l : Literal) : Bool := match l {
    Literal.struct_lit _fields _tn => true,
    _ => false,
}

/// How many `Term.lam` nodes the term contains -- the closure rule's count,
/// kept a count rather than a Bool because the message names it.
#[partial]
def lambda_count (t : Term) (acc : I64) : I64 :=
    match term_peel t {
        Term.lam _b _typ _body => count_all (value_children t) (acc + 1),
        _ => count_all (value_children t) acc,
    }

#[partial]
def count_all (children : List Term) (acc : I64) : I64 := match children {
    List.empty => acc,
    List.cons c rest => count_all rest (lambda_count c acc),
}

// ─── the shared child walk ───────────────────────────────────────────

/// The immediate sub-terms of a term that are VALUES.
///
/// TYPE positions are deliberately excluded, and that exclusion is
/// load-bearing rather than tidy: a lambda's annotation is a `Term.con` (an
/// `I64` written in a signature is a constructor application), so a walk that
/// visited it would report every annotated lambda as an ALLOCATION. That is a
/// real false positive, not a hypothetical -- the closure rule's own test
/// caught it, and the fix is here: `lam` yields its body, and `pi` yields
/// nothing (a `pi` IS a type).
///
/// This is the one place that has to grow when `Term` gains a variant, and it
/// is a LISTING walk rather than `term_map_children` (which rebuilds). A
/// `Term.ctx` node is TRANSPARENT (`term_peel`'s own doc comment), so its arm
/// recurses rather than stopping -- which is also what covers the nested case
/// a caller's own peel cannot reach (`Term.app (Term.ctx ..) x`). Matching on
/// `t` rather than on `term_peel t` is required, not stylistic: the checker
/// cannot see that a peeled term is never a `ctx`, so a peel-then-match is
/// non-exhaustive and fails to compile.
#[partial]
pub def value_children (t : Term) : List Term := match t {
    Term.ctx _loc inner => value_children inner,
    Term.var _i _d => List.empty,
    Term.var_macro _i _d => List.empty,
    Term.lam _b _typ body => List.cons body List.empty,
    Term.pi _b _arg _ret => List.empty,
    Term.app f a => List.cons f (List.cons a List.empty),
    Term.lit l => literal_children l,
    Term.ntv _n => List.empty,
    Term.con _c => List.empty,
    Term.hole => List.empty,
    Term.quote_ inner => List.cons inner List.empty,
    Term.sort _lvl => List.empty,
    Term.cubical c => match c { { prim := _, args := args } => args },
    Term.elim e => elim_value_children e,
}

/// `if_`/`match_` carry their operands as literals, not as term children, so a
/// walk that stops at `Term.lit` would miss a whole branch.
#[partial]
def literal_children (l : Literal) : List Term := match l {
    Literal.if_ one two three => List.cons one (List.cons two (List.cons three List.empty)),
    Literal.match_ value cases => List.cons value (match_case_terms cases),
    Literal.struct_lit fields _tn => struct_field_terms fields,
    Literal.struct_update base fields =>
        List.cons base (struct_field_terms fields),
    _ => List.empty,
}

#[partial]
def match_case_terms (cases : List MatchCase) : List Term := match cases {
    List.empty => List.empty,
    List.cons c rest =>
        match c { { body, .. } => List.cons body (match_case_terms rest) },
}

#[partial]
def struct_field_terms (fields : List StructLitField) : List Term := match fields {
    List.empty => List.empty,
    List.cons f rest =>
        match f { { value, .. } => List.cons value (struct_field_terms rest) },
}

/// An `elim`'s VALUE positions: the scrutinee (what is being eliminated) and
/// the minors (the arm bodies). Its `params`/`indices`/`motive` are types and
/// index values, so they are skipped for the same reason a `pi` is.
def elim_value_children (e : Elim) : List Term :=
    List.cons e.scrutinee e.minors

// ─── shared: name collection over a body ─────────────────────────────

/// Every name in `body` that appears in `wanted`, in body order.
///
/// `collect_referenced_names` is the binder-blind over-approximation
/// `free_names.mo` documents, and that is correct here deliberately: a kernel
/// is rejected for *mentioning* `List.cons`, and a mention shadowed by a local
/// binder is not a false positive worth risking a miss for.
#[partial]
def names_in (body : Term) (wanted : List String) : List String :=
    filter_names (collect_referenced_names body List.empty) wanted

#[partial]
def filter_names (names : List String) (wanted : List String) : List String := match names {
    List.empty => List.empty,
    List.cons n rest =>
        if name_present n wanted
        then List.cons n (filter_names rest wanted)
        else filter_names rest wanted,
}

// ─── the summary `monad kernels` prints ──────────────────────────────

/// One kernel's verdict: its name and its diagnostics.
pub struct KernelVerdict {
    kernel : String,
    diagnostics : List KernelDiagnostic,
}

pub def KernelVerdict.of (d : Def) : KernelVerdict :=
    KernelVerdict.mk (def_name_str d) (check_kernel d)

pub def KernelVerdict.ok (v : KernelVerdict) : Bool := List.is_empty v.diagnostics

/// One line per kernel, newline-terminated: `ok <name>`, or `FAIL <message>`
/// for the FIRST rule that failed.
///
/// The first rule rather than all of them, because this is the summary a
/// script reads; a caller that wants the full list has
/// `KernelVerdict.diagnostics` directly.
#[partial]
pub def render_verdicts (verdicts : List KernelVerdict) : String := match verdicts {
    List.empty => "",
    List.cons v rest => String.concat (render_verdict_head v) (String.concat "\n" (render_verdicts rest)),
}

def render_verdict_head (v : KernelVerdict) : String :=
    if KernelVerdict.ok v
    then String.concat "ok    " v.kernel
    else String.concat "FAIL  " (first_rendered v.diagnostics)

def first_rendered (ds : List KernelDiagnostic) : String := match ds {
    List.empty => "",
    List.cons d _ => KernelDiagnostic.render d,
}
