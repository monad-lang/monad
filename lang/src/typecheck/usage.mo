/// Runtime-position USE COUNTING over the canonical de-Bruijn `Term`.
///
/// Milestone 1 of the affine-by-default viability experiment
/// (section *Design B:
/// Viability Experiment*). This module
/// decides nothing and rejects nothing: it answers "how many times does
/// each binder get used at run time?" so the experiment can size the
/// migration before any semantics change.
///
/// The judgement it implements is the design's R1: `Γ, x :ₘ A ⊢ t`
/// holds iff `Σ(x, t) ≤ m`, where `Σ` counts **runtime-position** uses.
/// Three rules make `Σ` what it is, and each is a way to get this wrong:
///
/// 1. **Branches combine by MAX, not sum.** `if c then x else x` uses
///    `x` once — only one arm runs. So does a `match` whose every arm
///    uses it once. Summing them would report every well-formed
///    two-armed match as a double use and make the whole measurement
///    meaningless.
/// 2. **Type positions count 0.** A `Term.pi`'s argument, a
///    `Term.forall`'s kind and a `Term.lam`'s own annotation are
///    compile-time positions. A variable mentioned there is erased
///    before run time and consumes nothing.
/// 3. **Binder depth must match the tree.** Crossing `lam`/`forall`/`pi`
///    adds one to the body; a `MatchCase` adds `List.length args`. Both
///    conventions are spelled out and tested in
///    [[lang/typecheck/traverse.mo]] — this module mirrors them rather
///    than re-deriving them, and the match-arm case is the one
///    `lang/typecheck/subst.mo`'s `test_match_case_binder_depth_shift`
///    exists to catch.
///
/// Not a use, deliberately:
///
/// - A **top-level def reference** is a free global, not a binder. Only
///   `Term.var` indices that resolve to a local binder are counted, and
///   a free reference carries `idx = sentinel` (-1), which no binder
///   depth ever equals.
/// - A **quoted term** (`Term.quote_`) is syntax as data. Nothing inside
///   it runs, so nothing inside it consumes.
/// - `Term.ctx` is a transparent wrapper (`term_map_children_at_depth`'s
///   own arm passes depth 0 through it) — peel, never count.
///
/// Known conservatism, recorded rather than silently assumed: a use
/// inside a closure body counts ONCE even though the closure may be
/// called many times. That is correct for an affine binder — the closure
/// owns the capture, and calling a closure does not consume its captures
/// — but it is NOT correct for a `linear` one, where a closure capturing
/// a linear value must itself be linear. That rule belongs to Milestone
/// 3 (drop points), and it is noted here because this module is where
/// someone will look for it first.
use lib::types {
  Con, DebugName, FieldPattern, Identifier, Literal, Location, MatchCase,
  Native, StructLitField, Term,
}
use std::list {length}

// ─── Use counting ──────────────────────────────────────────────────

/// Larger of two counts. No `I64.max` exists in `init/src/number.mo`
/// (only `lt`/`gt`/`beq`), and branch combination needs one at every
/// `if_`/`match_` node, so it lives here.
def i64_max (a : I64) (b : I64) : I64 := if I64.lt a b then b else a

/// Runtime-position uses of the de-Bruijn index `target` inside `t`.
///
/// `target` is relative to `t`: pass 0 for the variable a `lam` has just
/// bound when walking its body. Crossing a binder shifts the target up
/// by that binder's width, which is why the recursive calls below add
/// rather than the callers subtracting.
#[partial]
def uses_of (target : I64) (t : Term) : I64 :=
    match t {
        Term.var idx _dbg => if I64.beq idx target then 1 else 0,
        // Macro references are resolved in a separate namespace at
        // expansion time and never via de-Bruijn lookup (see
        // `Term.var_macro`'s own doc comment in lang/types.mo), so one
        // can never BE the binder we are counting.
        Term.var_macro _idx _dbg => 0,
        // The annotation is a type position (rule 2); only the body is
        // run-time, and it sits one binder deeper (rule 3).
        Term.lam _dbg _typ body => uses_of (target + 1) body,
        Term.forall _dbg _kind body => uses_of (target + 1) body,
        // A `pi` is a function TYPE, entirely compile-time. Both halves
        // are type positions, so the whole node contributes nothing.
        Term.pi _arg _ret => 0,
        Term.app callee arg => uses_of target callee + uses_of target arg,
        Term.lit value => uses_of_literal target value,
        Term.ntv n => uses_of_native target n,
        Term.con c => uses_of_con target c,
        Term.type_ _u => 0,
        Term.hole => 0,
        Term.quote_ _inner => 0,
        Term.ctx _loc inner => uses_of target inner,
    }

#[partial]
def uses_of_literal (target : I64) (l : Literal) : I64 :=
    match l {
        Literal.str _v => 0,
        Literal.char _v => 0,
        Literal.num _n _suf => 0,
        Literal.flt _t _suf => 0,
        // The condition always runs; exactly one branch does. Rule 1.
        Literal.if_ cond then_ else_ =>
            uses_of target cond + i64_max (uses_of target then_) (uses_of target else_),
        // The scrutinee always runs; exactly one arm does. Rule 1.
        Literal.match_ scrut cases =>
            uses_of target scrut + uses_of_cases target cases,
        // `type_name` is the literal's ascribed TYPE -- a type position.
        Literal.struct_lit fields _type_name => uses_of_fields target fields,
        Literal.struct_update base fields =>
            uses_of target base + uses_of_fields target fields,
    }

/// Max over arms, not sum (rule 1). An empty arm list contributes 0,
/// which is also the identity this fold needs.
#[partial]
def uses_of_cases (target : I64) (cases : List MatchCase) : I64 :=
    match cases {
        List.empty => 0,
        List.cons c rest => i64_max (uses_of_case target c) (uses_of_cases target rest),
    }

/// An arm's own pattern bindings bind over its body, so the body sits
/// `List.length args` binders deeper than the `Literal.match_` node --
/// the same adjustment `match_case_map_children_at_depth` makes.
#[partial]
def uses_of_case (target : I64) (c : MatchCase) : I64 :=
    match c {
        MatchCase.mc _name args body _fp => uses_of (target + List.length args) body,
    }

/// Struct-literal field values all run, so they SUM.
#[partial]
def uses_of_fields (target : I64) (fields : List StructLitField) : I64 :=
    match fields {
        List.empty => 0,
        List.cons f rest =>
            match f {
                StructLitField.mk _name value => uses_of target value + uses_of_fields target rest,
            },
    }

#[partial]
def uses_of_con (target : I64) (c : Con) : I64 :=
    match c {
        Con.mk _name _typ_name _num_args args => uses_of_opt_args target args,
    }

#[partial]
def uses_of_native (target : I64) (n : Native) : I64 :=
    match n {
        Native.mk _native_name _num_args args => uses_of_opt_args target args,
    }

/// A constructor's/native's argument slots are `Option Term` -- an
/// unsaturated slot (`Option.none`) has no term to use anything.
#[partial]
def uses_of_opt_args (target : I64) (args : List (Option Term)) : I64 :=
    match args {
        List.empty => 0,
        List.cons a rest =>
            match a {
                Option.some t => uses_of target t + uses_of_opt_args target rest,
                Option.none => uses_of_opt_args target rest,
            },
    }

// ─── Per-binder collection ─────────────────────────────────────────

/// Where a binder came from. Enough to read a report by; deliberately
/// NOT enough to reconstruct the binding site, which the report does not
/// need and which `Term` cannot supply anyway (a `let` is already
/// desugared to `app (lam ...) value` by the time it gets here, so a
/// let-bound name is indistinguishable from a lambda parameter).
pub type BinderKind {
    bk_lam,
    bk_match,
}

/// One binder and how many times its body uses it.
///
/// `typ` is `Term.hole` when unknown. That is the honest state for a
/// match-arm binder here: its type comes from the matched constructor's
/// `InductConstructor.params`, which needs the scrutinee's inductive
/// resolved, which needs a `Scope` this module deliberately does not
/// take (it stays a pure function of the term). The report's driver
/// fills those in where it can.
pub struct BinderUse {
    name : Identifier,
    kind : BinderKind,
    typ : Term,
    count : I64,
}

/// Typed accessors, one per field this module's own tests read.
///
/// NOT redundant with the struct's field syntax: a `#[test] def` whose
/// body is a bare struct field access takes the FIELD's LLVM type as its
/// own return type in the self-hosted backend (`i1`/`i64` mismatch at
/// `llc`, or an undefined `@P.mk`), and only the compiled runner shows
/// it. Reading through an ordinary def is the documented workaround, and
/// `Def.name` (`lang/types.mo:1021`) is the existing precedent for the
/// name-shadows-field spelling.
pub def BinderUse.count (u : BinderUse) : I64 := u.count

pub def BinderUse.name (u : BinderUse) : Identifier := u.name

pub def BinderUse.typ (u : BinderUse) : Term := u.typ

pub def BinderUse.kind (u : BinderUse) : BinderKind := u.kind

/// `DebugName` -> a printable identifier. An unnamed binder reports as
/// `_`, matching how the corpus already spells a binder nobody reads.
def binder_name (dbg : DebugName) : Identifier :=
    match dbg {
        DebugName.named id => id,
        DebugName.unnamed => Identifier.id "_",
    }

/// Every binder in `t`, with its use count.
///
/// Accumulator-passing, and every walker below it likewise: this runs
/// over whole modules -- 3,817 defs for the compiler itself -- and the
/// natural `List.cons x (recurse rest)` shape holds one native frame per
/// node, which is the exact pathology `lang/codegen/decls.mo`'s
/// `extract_defs` and `lang/codegen/qualify.mo`'s
/// `ambiguous_declared_names` document (and which Boehm then pays for
/// again on every collection, since it marks conservatively from the
/// whole stack).
///
/// Order is unspecified -- the accumulator reverses, and the report
/// sorts by count anyway.
#[partial]
pub def collect_binder_uses (t : Term) : List BinderUse :=
    collect_uses_term t List.empty

#[partial]
def collect_uses_term (t : Term) (acc : List BinderUse) : List BinderUse :=
    match t {
        Term.var _idx _dbg => acc,
        Term.var_macro _idx _dbg => acc,
        Term.lam dbg typ body =>
            let u : BinderUse :=
                { name := binder_name dbg,
                  kind := BinderKind.bk_lam,
                  typ := typ,
                  count := uses_of 0 body } in
            collect_uses_term body (List.cons u acc),
        // A `forall` binds a TYPE variable. It is erased before run time,
        // so it is not a runtime binder and never owns memory -- walk
        // through it for the binders nested inside, but do not report it.
        Term.forall _dbg _kind body => collect_uses_term body acc,
        // Entirely a type position (rule 2). Any `lam` nested inside a
        // type is likewise compile-time and reports nothing.
        Term.pi _arg _ret => acc,
        Term.app callee arg => collect_uses_term arg (collect_uses_term callee acc),
        Term.lit value => collect_uses_literal value acc,
        Term.ntv n => collect_uses_native n acc,
        Term.con c => collect_uses_con c acc,
        Term.type_ _u => acc,
        Term.hole => acc,
        Term.quote_ _inner => acc,
        Term.ctx _loc inner => collect_uses_term inner acc,
    }

#[partial]
def collect_uses_literal (l : Literal) (acc : List BinderUse) : List BinderUse :=
    match l {
        Literal.str _v => acc,
        Literal.char _v => acc,
        Literal.num _n _suf => acc,
        Literal.flt _t _suf => acc,
        Literal.if_ cond then_ else_ =>
            collect_uses_term else_ (collect_uses_term then_ (collect_uses_term cond acc)),
        Literal.match_ scrut cases => collect_uses_cases cases (collect_uses_term scrut acc),
        Literal.struct_lit fields _type_name => collect_uses_fields fields acc,
        Literal.struct_update base fields => collect_uses_fields fields (collect_uses_term base acc),
    }

#[partial]
def collect_uses_cases (cases : List MatchCase) (acc : List BinderUse) : List BinderUse :=
    match cases {
        List.empty => acc,
        List.cons c rest => collect_uses_cases rest (collect_uses_case c acc),
    }

#[partial]
def collect_uses_case (c : MatchCase) (acc : List BinderUse) : List BinderUse :=
    match c {
        MatchCase.mc _name args body _fp =>
            let n : I64 := List.length args in
            let with_args : List BinderUse := collect_case_args args 0 n body acc in
            collect_uses_term body with_args,
    }

/// Pattern binders are pushed onto the local context left to right
/// (`prepend_typed`, `lang/typecheck/infer.mo:1299`), so the LAST one
/// ends up innermost at index 0 and the first sits at `n - 1`. Codegen
/// agrees from the other side: `bind_match_fields`
/// (`lang/codegen/emit.mo:653`) reads field `i` for the `i`-th name in
/// written order. Getting this backwards silently attributes each
/// binder's count to a different binder, which is why it is spelled out
/// rather than inlined.
#[partial]
def collect_case_args (args : List Identifier) (i : I64) (n : I64) (body : Term) (acc : List BinderUse) : List BinderUse :=
    match args {
        List.empty => acc,
        List.cons nm rest =>
            let idx : I64 := n - 1 - i in
            let u : BinderUse :=
                { name := nm,
                  kind := BinderKind.bk_match,
                  typ := Term.hole,
                  count := uses_of idx body } in
            collect_case_args rest (i + 1) n body (List.cons u acc),
    }

#[partial]
def collect_uses_fields (fields : List StructLitField) (acc : List BinderUse) : List BinderUse :=
    match fields {
        List.empty => acc,
        List.cons f rest =>
            match f {
                StructLitField.mk _name value => collect_uses_fields rest (collect_uses_term value acc),
            },
    }

#[partial]
def collect_uses_con (c : Con) (acc : List BinderUse) : List BinderUse :=
    match c {
        Con.mk _name _typ_name _num_args args => collect_uses_opt_args args acc,
    }

#[partial]
def collect_uses_native (n : Native) (acc : List BinderUse) : List BinderUse :=
    match n {
        Native.mk _native_name _num_args args => collect_uses_opt_args args acc,
    }

#[partial]
def collect_uses_opt_args (args : List (Option Term)) (acc : List BinderUse) : List BinderUse :=
    match args {
        List.empty => acc,
        List.cons a rest =>
            match a {
                Option.some t => collect_uses_opt_args rest (collect_uses_term t acc),
                Option.none => collect_uses_opt_args rest acc,
            },
    }

// ─── Tests ─────────────────────────────────────────────────────────
//
// Every rule in this file's doc comment has a test below, because every
// one of them is a way to produce a plausible-looking wrong number.

def dbg_x : DebugName := DebugName.named (Identifier.id "x")

/// `var 0` -- the binder itself, used once.
def t_var0 : Term := Term.var 0 dbg_x

#[test]
def test_uses_of_counts_the_target : Bool :=
    I64.beq (uses_of 0 t_var0) 1

#[test]
def test_uses_of_ignores_other_indices : Bool :=
    I64.beq (uses_of 1 t_var0) 0

#[test]
def test_uses_of_sums_application_args : Bool :=
    // `x x` -- both halves run, so they sum.
    let t : Term := Term.app t_var0 t_var0 in
    I64.beq (uses_of 0 t) 2

#[test]
def test_uses_of_takes_max_across_if_branches : Bool :=
    // `if <unit> then x else x` -- only one arm runs. Rule 1.
    let t : Term := Term.lit (Literal.if_ Term.hole t_var0 t_var0) in
    I64.beq (uses_of 0 t) 1

#[test]
def test_uses_of_adds_if_condition_to_branch_max : Bool :=
    // `if x then x else x` -- the condition always runs on top of
    // whichever arm does.
    let t : Term := Term.lit (Literal.if_ t_var0 t_var0 t_var0) in
    I64.beq (uses_of 0 t) 2

#[test]
def test_uses_of_takes_max_across_match_arms : Bool :=
    // Two zero-binder arms, each using `x` once. Rule 1: one, not two.
    let no_fp : Option FieldPattern := Option.none in
    let no_args : List Identifier := List.empty in
    let arm1 : MatchCase := MatchCase.mc (Identifier.id "a") no_args t_var0 no_fp in
    let arm2 : MatchCase := MatchCase.mc (Identifier.id "b") no_args t_var0 no_fp in
    let arms : List MatchCase := List.cons arm1 (List.cons arm2 List.empty) in
    let t : Term := Term.lit (Literal.match_ Term.hole arms) in
    I64.beq (uses_of 0 t) 1

#[test]
def test_uses_of_shifts_past_match_arm_binders : Bool :=
    // One arm binding two names, whose body is `var 2`. Inside the body
    // the outer binder has moved from 0 to 2, so this IS a use of it.
    // The exact shift `subst.mo`'s own binder-depth test guards.
    let no_fp : Option FieldPattern := Option.none in
    let args : List Identifier :=
        List.cons (Identifier.id "a") (List.cons (Identifier.id "b") List.empty) in
    let body : Term := Term.var 2 dbg_x in
    let arm : MatchCase := MatchCase.mc (Identifier.id "c") args body no_fp in
    let arms : List MatchCase := List.cons arm List.empty in
    let t : Term := Term.lit (Literal.match_ Term.hole arms) in
    I64.beq (uses_of 0 t) 1

#[test]
def test_uses_of_shifts_past_lambda : Bool :=
    // `fn _ => var 1` -- one binder crossed, so index 1 inside is index
    // 0 outside.
    let t : Term := Term.lam DebugName.unnamed Term.hole (Term.var 1 dbg_x) in
    I64.beq (uses_of 0 t) 1

#[test]
def test_uses_of_ignores_lambda_annotation : Bool :=
    // The annotation mentions the binder, the body does not. A type
    // position consumes nothing. Rule 2.
    let t : Term := Term.lam DebugName.unnamed t_var0 Term.hole in
    I64.beq (uses_of 0 t) 0

#[test]
def test_uses_of_ignores_pi_entirely : Bool :=
    // A function type is compile-time on both sides. Rule 2.
    let t : Term := Term.pi t_var0 t_var0 in
    I64.beq (uses_of 0 t) 0

#[test]
def test_uses_of_ignores_quoted_syntax : Bool :=
    // Quoted syntax is data; nothing inside it runs.
    let t : Term := Term.quote_ t_var0 in
    I64.beq (uses_of 0 t) 0

#[test]
def test_uses_of_sees_through_ctx : Bool :=
    // `Term.ctx` is a transparent wrapper -- depth 0, and the use inside
    // still counts.
    let loc : Location := Location.mk 0 1 1 in
    I64.beq (uses_of 0 (Term.ctx loc t_var0)) 1

#[test]
def test_uses_of_counts_constructor_args : Bool :=
    // Constructor argument slots all run, so they sum.
    let args : List (Option Term) :=
        List.cons (Option.some t_var0) (List.cons (Option.some t_var0) List.empty) in
    let c : Con := Con.mk (Identifier.id "P") (ModulePath.mp (List.cons (Identifier.id "P") List.empty)) 2 args in
    I64.beq (uses_of 0 (Term.con c)) 2

#[test]
def test_uses_of_skips_unsaturated_constructor_slots : Bool :=
    let args : List (Option Term) :=
        List.cons (Option.some t_var0) (List.cons Option.none List.empty) in
    let c : Con := Con.mk (Identifier.id "P") (ModulePath.mp (List.cons (Identifier.id "P") List.empty)) 2 args in
    I64.beq (uses_of 0 (Term.con c)) 1

#[test]
def test_collect_reports_one_binder_per_lambda : Bool :=
    // `fn x => fn y => var 0` -- two binders. The inner one is used
    // once; the outer one is never used, which is exactly the shape
    // affine-by-default must free automatically.
    let inner : Term := Term.lam dbg_x Term.hole (Term.var 0 dbg_x) in
    let t : Term := Term.lam dbg_x Term.hole inner in
    I64.beq (List.length (collect_binder_uses t)) 2

#[test]
def test_collect_records_an_unused_binder_as_zero : Bool :=
    // `fn x => <hole>` -- one binder, zero uses. Affine-legal (weakening
    // is admissible), and a release point under Milestone 3.
    let t : Term := Term.lam dbg_x Term.hole Term.hole in
    match collect_binder_uses t {
        List.cons u _rest => I64.beq (BinderUse.count u) 0,
        List.empty => false,
    }

#[test]
def test_collect_records_an_overused_binder : Bool :=
    // `fn x => x x` -- two uses. This is the shape that needs `Copy`.
    let body : Term := Term.app (Term.var 0 dbg_x) (Term.var 0 dbg_x) in
    let t : Term := Term.lam dbg_x Term.hole body in
    match collect_binder_uses t {
        List.cons u _rest => I64.beq (BinderUse.count u) 2,
        List.empty => false,
    }

#[test]
def test_collect_skips_forall_binders : Bool :=
    // A `forall` binds a type variable: erased, never a runtime owner.
    // The `lam` nested under it is still reported.
    let inner : Term := Term.lam dbg_x Term.hole Term.hole in
    let t : Term := Term.forall dbg_x (Term.type_ 0) inner in
    I64.beq (List.length (collect_binder_uses t)) 1
