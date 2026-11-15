/// `#[kernel]` monomorphisation: inline the reachable defs, reduce, and
/// constant-fold the shape literals -- plus the SIXTH subset rule, which
/// `detect.mo` deliberately does not own.
///
/// ## What this module is for
///
/// `detect.mo` decides whether a kernel's own body is inside the subset. This
/// module answers the two questions a body-only walk cannot:
///
/// 1. **What does the kernel's body look like once every helper it calls has
///    been inlined?** `scalar.mo` lowers ONE first-order term; a call to a
///    top-level `def` is not something it can emit. So the reachable helpers
///    are inlined here, and the result is a term whose only remaining
///    references are natives, constructors and the kernel's own parameters.
/// 2. **Is every dimension literal at the CALL site?** That is a property of
///    the call, not the def, which is why it is here rather than in
///    `detect.mo` (see that module's rule table). The plan states the rule as
///    "dimensions literal at the call site"; the tag is `dim`.
///
/// ## The elaborated shape this has to survive
///
/// Arithmetic does NOT reach codegen as `I64.add`. It reaches it as a
/// dictionary-passing class-method call, because `infix (+) := HAdd.add` and
/// `HAdd`'s bridge instance forwards to `Add`:
///
/// ```monad,ignore
/// def z : I64 := 4 + 4
/// // elaborated:
/// def z : I64 := (HAdd_A_A_A_add __Dict_Add_I64 4i64 4i64)
///
/// def HAdd_A_A_A_add : ... :=
///     (fn (__dict_Add : _) => (fn (a : A) => (fn (b : A) =>
///         (match __dict_Add { mk add => add } a b))))
///
/// def __Dict_Add_I64 : Type := (__Dict_Add_I64.mk Add_I64_add)
/// def Add_I64_add : ... := (fn (a : I64) => (fn (b : I64) => (I64.add a b)))
/// ```
///
/// (Measured 2026-11-15 against this tree, through
/// `compile_input_of_modules` -- the real front end, not a hand-built term.)
///
/// So folding `4 + 4` is not a peephole. It is delta (unfold
/// `HAdd_A_A_A_add`) + iota (select the dictionary's single `mk` arm) + beta
/// (apply the three arguments) + delta again (`Add_I64_add`'s body) + the
/// native `I64.add`. All four steps are ordinary reduction, which is why this
/// module reuses `lang`'s substitution primitives and its own small reducer
/// rather than pattern-matching a call shape.
///
/// ## Why the reducer is here and not `whnf`
///
/// `lang::typecheck::whnf` is a *type-level* reducer: it needs a `Scope` and a
/// `LocalScope`, its `whnf_delta` refuses to unfold a name that is locally
/// bound, and its fuel is 64. This module has no scope (a kernel's closure is
/// already flattened into a `List Def`) and needs a *deeper* reduction than
/// weak-head -- `4 * 2 + 1` must become `9i64`, which means reducing inside
/// argument positions, not just at the head. Reusing `whnf` would mean
/// synthesising a `Scope` per kernel to get a weaker answer.
///
/// The two therefore share the SUBSTITUTION primitives (`term_shift`,
/// `term_subst`, `beta_reduce` -- made `pub` in `lang/src/typecheck/subst.mo`
/// for exactly this) and not the reduction strategy.
///
/// ## What inlining is, and what it deliberately is not
///
/// This is **not a monomorphiser in the type-system sense**. The subset checker
/// REJECTS polymorphism rather than specialising it (the plan says so, and
/// `detect.mo`'s rule 3 is that rejection), so a kernel and everything it
/// reaches is monomorphic already. "Mono" here means: inline the reachable
/// top-level defs, beta-reduce, fold the shape arithmetic. A general
/// monomorphiser is its own plan and putting one on this plan's critical path
/// would double its size.
///
/// Inlining is *bounded* rather than recursive-until-fixpoint. A helper that
/// calls itself is already refused by `detect.mo`'s recursion rule on its own
/// def, so a cycle here can only come from mutually recursive helpers, which
/// the same rule's closure check refuses. `inline_budget` is the belt to that
/// braces: an unbounded inliner over a mutually recursive pair would not
/// terminate, and a wrong answer is worse than a diagnostic.
///
/// ## No `mlir` import
///
/// Deliberately. This module produces a `Term`, and `Term` is `lang`'s. The
/// first `codegen -> mlir` import is `shape.mo`/`scalar.mo`'s (they produce an
/// `MlirModule`), and that is the commit which must add `"mlir"` to
/// `scripts/build-self-hosted.sh`'s scan and `nix/monad.nix`'s `compilerSrc`
/// fileset. Keeping this file free of `mlir` keeps that change as small as the
/// plan says it can be.
use lang::types {
    Binder, Con, Cubical, DebugName, Decl, Def, Elim, Identifier, Literal, MatchCase,
    Native, NumSuffix, StructLitField, Term, binder_is_explicit, binder_name, term_peel,
}
use lang::typecheck::subst {beta_reduce, term_subst, term_shift}
use lib::decls {def_body_term, def_name_str, def_param_chain_body, extract_defs}
use lib::kernel::detect {KernelDiagnostic, value_children}
use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}
use std::map {HashMap}

// ─── the result of extraction ────────────────────────────────────────

/// One kernel, ready for `scalar.mo`: its name, its parameters, and its body
/// with every reachable helper inlined and every literal dimension folded.
pub struct KernelExtract {
    /// The kernel's symbol, spelled the way codegen spells it
    /// (`def_name_str`) -- what `host.mo` needs to name the emitted function.
    name : String,
    /// The kernel's explicit parameters, in declaration order.
    params : List KernelParam,
    /// The inlined, reduced body.
    body : Term,
    /// What stopped a FULL extraction: the `dim` rule's findings here, plus
    /// whatever `detect.mo` reported on the def. Empty means the kernel is
    /// ready for `scalar.mo`.
    diagnostics : List KernelDiagnostic,
}

/// One kernel parameter. A record rather than `Param` because the kernel
/// subset cares about exactly two things -- the name and the declared type --
/// and `Param`'s other three fields are meaningless for a kernel argument (a
/// default value would be an implicit call-site literal; a multiplicity is
/// host-side linearity, and the kernel ABI is a bare pointer).
pub struct KernelParam {
    name : String,
    typ : Term,
}

/// Is the extraction free of diagnostics -- ready for `scalar.mo`?
pub def KernelExtract.ready (k : KernelExtract) : Bool := List.is_empty k.diagnostics

/// The kernel's first parameter, or a placeholder. Only for a caller that has
/// already checked the list is non-empty, and for tests.
pub def KernelExtract.first_param (k : KernelExtract) : KernelParam := match k.params {
    List.empty => KernelParam.mk "" Term.hole,
    List.cons p _ => p,
}

// ─── the SIXTH rule: literal dimensions at the call site ─────────────

/// The `dim` rule's finding for one non-literal dimension argument.
///
/// `callee` is the kernel being called and `position` its argument index, so
/// the message names both -- the plan's rejection-message shape is
/// `kernel 'foo' called with non-literal 'n'; ...`, and naming the position is
/// what makes it actionable when a kernel takes three dimensions.
pub def dim_diagnostic (callee : String) (position : I64) (detail : String) : KernelDiagnostic :=
    KernelDiagnostic.of callee "dim"
        (String.concat_all ["argument ", I64.to_string position, " is ", detail])

/// Every `dim` finding for a call to `callee` with `args`, given the set of
/// parameter positions that ARE dimensions.
///
/// "Which positions are dimensions" has to come from somewhere, and the honest
/// answer is `shape.mo`'s: a dimension is a parameter the kernel uses as a
/// `memref` bound, which is read off the body's `Buf` types and its loops.
/// Until that module exists, the caller passes `dim_positions_of`'s
/// over-approximation (every explicit `I64` parameter). An over-report is a
/// diagnostic on a kernel that would have worked; an under-report is a
/// silently dynamic shape, which the plan forbids.
#[partial]
pub def dim_diagnostics (callee : String) (args : List Term) (positions : List I64) : List KernelDiagnostic :=
    dim_diagnostics_go callee args positions 0

#[partial]
def dim_diagnostics_go (callee : String) (args : List Term) (positions : List I64) (i : I64) : List KernelDiagnostic :=
    match args {
        List.empty => List.empty,
        List.cons a rest =>
            List.append (dim_diagnostic_at callee a positions i)
                (dim_diagnostics_go callee rest positions (i + 1)),
    }

#[partial]
def dim_diagnostic_at (callee : String) (a : Term) (positions : List I64) (i : I64) : List KernelDiagnostic :=
    if contains_i64 positions i
    then match int_literal_of a {
        Option.some _ => List.empty,
        Option.none => List.cons (dim_diagnostic callee i (describe_dim a)) List.empty,
    }
    else List.empty

/// A short description of what the caller wrote, for the diagnostic.
def describe_dim (t : Term) : String := match term_peel t {
    Term.var _idx dbg => match dbg {
        DebugName.named id => id_text id,
        DebugName.unnamed => "a variable",
    },
    Term.lit _ => "a non-integer literal",
    Term.app _ _ => "a computed expression",
    _ => "a non-literal",
}

#[partial]
def contains_i64 (xs : List I64) (x : I64) : Bool := match xs {
    List.empty => false,
    List.cons h rest => if I64.beq h x then true else contains_i64 rest x,
}

// ─── literal inspection ──────────────────────────────────────────────

/// A literal `I64`, if `t` is one. `Literal.num` with any suffix counts -- a
/// dimension written `16u8` is still a literal dimension -- but `flt` does not,
/// because a float is not a dimension.
pub def int_literal_of (t : Term) : Option I64 := match term_peel t {
    Term.lit l => match l {
        Literal.num v _suffix => Option.some v,
        _ => Option.none,
    },
    _ => Option.none,
}

/// `Term.lit (Literal.num v NumSuffix.i64)` -- the one spelling this module
/// builds a folded dimension in.
pub def int_lit (v : I64) : Term := Term.lit (Literal.num v NumSuffix.i64)

pub def id_text (id : Identifier) : String := match id { Identifier.id s => s }

// ─── the native arithmetic this module folds ─────────────────────────
//
// Only the natives a DIMENSION can be computed with. Deliberately not the
// whole native set: folding a kernel's DATA arithmetic is `scalar.mo`'s
// business (it emits `arith.addi` and lets `mlir-opt` fold), and doing it here
// would hide the operation from the emitted IR. What has to be folded HERE is
// the shape arithmetic, because `shape.mo` needs a literal dimension and there
// is no IR yet to fold it in.
//
// The semantics mirror the interpreter's (`rust/core/src/core_native.rs`) and
// the runtime's, including the two conventions that are easy to get wrong: a
// ZERO divisor yields 0 rather than trapping, and the arithmetic WRAPS. Both
// are pinned by tests.

/// The folded result of `op` applied to `a` and `b`, or `Option.none` when
/// `op` is not a foldable integer native.
///
/// `op` is the bare native name (`i64_add`), because that is what
/// `#[native i64_add]` writes.
#[partial]
pub def fold_native_binop (op : String) (a : I64) (b : I64) : Option I64 :=
    if String.beq op "i64_add" then Option.some (I64.add a b)
    else if String.beq op "i64_sub" then Option.some (I64.sub a b)
    else if String.beq op "i64_mul" then Option.some (I64.mul a b)
    else if String.beq op "i64_div" then Option.some (if I64.beq b 0 then 0 else I64.div a b)
    else if String.beq op "i64_rem" then Option.some (if I64.beq b 0 then 0 else I64.rem a b)
    else Option.none

/// A `Term.ntv`'s native name.
#[partial]
def native_name_of (t : Term) : Option String := match term_peel t {
    Term.ntv n => match n {
        Native.mk name _n _args => Option.some (id_text name),
    },
    _ => Option.none,
}

/// A `Term.ntv`'s carried arguments, as terms. `Native.args` is
/// `List (Option Term)`; an unelaborated position stays `none` and is dropped.
#[partial]
def native_args_of (t : Term) : List Term := match term_peel t {
    Term.ntv n => match n {
        Native.mk _name _num args => present_terms args,
    },
    _ => List.empty,
}

#[partial]
def present_terms (args : List (Option Term)) : List Term := match args {
    List.empty => List.empty,
    List.cons h rest => match h {
        Option.some a => List.cons a (present_terms rest),
        Option.none => present_terms rest,
    },
}

// ─── the reducer ─────────────────────────────────────────────────────

/// The fuel one head-reduction gets. A kernel body is small and its helper
/// closure is bounded by `inline_budget`, so this only has to be large enough
/// for a nested dictionary chain; it is a stop, not a tuning knob.
def reduce_fuel : I64 := 400

/// Reduce `t` against the definition table `defs`: reduce every child, then
/// head-reduce, and reduce the children of each head step's result.
///
/// **Children BEFORE the head, and the order is load-bearing.** It was
/// head-first in the first version and that version could not fold the
/// dictionary chain at all -- measured, not theorised. An iota step needs its
/// scrutinee to have REDUCED: `match __Dict_Add_I64 { mk add => add }` is stuck
/// while `__Dict_Add_I64` is still a bare reference, and only becomes firable
/// once delta has turned it into `(__Dict_Add_I64.mk Add_I64_add)`. Head-first
/// reached the `match` before its scrutinee and gave up.
///
/// **And the head step's own result is re-reduced**, which is the other half. A
/// head step builds a NEW term (`reapply` of a beta-reduced body), and that term
/// can carry a redex in an argument position. The loop therefore calls back into
/// `reduce_children_with` on each result rather than looping on the bare head --
/// so every argument is a value again before the next step looks at the head.
///
/// Termination: `reduce_children_with` recurses into strictly smaller subterms,
/// and each head step spends one unit of `fuel`. `reduce_fuel` is therefore a
/// hard bound on the head steps of one term, not a tuning knob.
///
/// `defs` is threaded through rather than read from a global, so a test can
/// reduce against a hand-built table with no decl list at all.
#[partial]
pub def reduce_with (defs : HashMap String Term) (t : Term) : Term :=
    let kids : Term := reduce_children_with defs t in
    reduce_head_with defs kids reduce_fuel

/// One head-reduction step, repeated until it stops firing. Each step's result
/// is re-reduced (see `reduce_with`), which is what makes the NEXT step's head
/// visible.
#[partial]
pub def reduce_head_with (defs : HashMap String Term) (t : Term) (fuel : I64) : Term :=
    if I64.lt fuel 1
    then t
    else match step_head_with defs t {
        Option.some next => reduce_head_with defs (reduce_children_with defs next) (fuel - 1),
        Option.none => t,
    }

/// One reduction step at the head of `t`, or `Option.none` if `t` is rigid.
///
/// **The spine is the unit of reduction, not the outermost `Term.app`.** That
/// is not a stylistic choice; it is the bug this function was rewritten for.
/// `HAdd_A_A_A_add __Dict_Add_I64 4i64 4i64` is `((HAdd_A_A_A_add dict) 4) 4`,
/// so the OUTERMOST node's function is itself an application. A version that
/// asked "is `f` a lambda?" of that node would answer no -- `f` is an
/// application -- and beta would never fire on any call of arity >= 2, which is
/// every dictionary chain there is. Measured: the first version of this
/// function folded nothing and `test_reduce_folds_the_measured_dictionary_chain`
/// is what caught it.
///
/// So: flatten the spine, reduce at its HEAD, and RE-APPLY the remaining
/// arguments to whatever the step produced. Each of the four steps is then a
/// statement about the head:
///
/// * **beta** -- the head is a lambda; substitute its binder for the first
///   argument.
/// * **native fold** -- the head is a native with at least two arguments, both
///   literal.
/// * **iota** -- the head is a `match`; fire the selected arm.
/// * **delta** -- the head is a reference to a known def; replace it with its
///   body.
///
/// A step that fires re-enters `reduce_head_with`, which is what lets the chain
/// reduce all the way to `8i64` -- each step exposes the next.
#[partial]
pub def step_head_with (defs : HashMap String Term) (t : Term) : Option Term :=
    match spine_of t {
        Spine.mk hd args => step_spine defs hd args,
    }

/// A call spine: its head and its arguments, in written order.
pub struct Spine {
    hd : Term,
    args : List Term,
}

/// `spine_of` under the name the reducer uses.
#[partial]
pub def spine_of (t : Term) : Spine := Spine.mk (spine_head_of t) (spine_args_of t)

/// One head step on an already-flattened spine.
///
/// Every step RE-APPLIES the spine's remaining arguments to whatever it
/// produced, and delta is the one where forgetting to is silent. A def's body
/// is a lambda chain (`HAdd_A_A_A_add`'s is three lambdas), so unfolding the
/// reference and DROPPING the arguments gives a bare lambda with nothing
/// applied to it -- which the next step sees as a spine of arity 0 and refuses,
/// so reduction simply stops one step in. Measured: that was the second bug in
/// this function, and `test_reduce_folds_the_measured_dictionary_chain` caught
/// it too.
#[partial]
def step_spine (defs : HashMap String Term) (hd : Term) (args : List Term) : Option Term :=
    match term_peel hd {
        Term.lam _b _typ body =>
            match args {
                List.empty => Option.none,
                List.cons a rest => Option.some (reapply (beta_reduce body a) rest),
            },
        Term.ntv _n => fold_native_spine (term_peel hd) args,
        Term.lit l => match match_redex_literal l {
            Option.some fired => Option.some (reapply fired args),
            Option.none => reapply_spine (unfold_def defs (term_peel hd)) args,
        },
        _ => reapply_spine (unfold_def defs (term_peel hd)) args,
    }

/// Re-apply `args` to an `Option`-wrapped step result, propagating `none`.
#[partial]
def reapply_spine (r : Option Term) (args : List Term) : Option Term := match r {
    Option.some body => Option.some (reapply body args),
    Option.none => Option.none,
}

/// `f a b` from `f` and `[a, b]`.
#[partial]
def reapply (f : Term) (args : List Term) : Term := match args {
    List.empty => f,
    List.cons a rest => reapply (Term.app f a) rest,
}

/// The native fold over a spine: `i64_add a b` needs exactly the two operands
/// `fold_native_binop` folds, and they are the native's own first `args` entry
/// plus the spine's first argument.
#[partial]
def fold_native_spine (hd : Term) (args : List Term) : Option Term :=
    match args {
        List.empty => Option.none,
        List.cons first_spine_arg rest =>
            match native_name_of hd {
                Option.none => Option.none,
                Option.some op => fold_native_two op hd first_spine_arg,
            },
    }

#[partial]
def match_redex_literal (l : Literal) : Option Term := match l {
    Literal.match_ scrut cases => iota_match scrut cases,
    _ => Option.none,
}

#[partial]
def fold_native_two (op : String) (f : Term) (a : Term) : Option Term :=
    match first_arg_of (native_args_of f) {
        Option.none => Option.none,
        Option.some first =>
            match int_literal_of first {
                Option.none => Option.none,
                Option.some x =>
                    match int_literal_of a {
                        Option.none => Option.none,
                        Option.some y => match fold_native_binop op x y {
                            Option.some v => Option.some (int_lit v),
                            Option.none => Option.none,
                        },
                    },
            },
    }

#[partial]
def first_arg_of (args : List Term) : Option Term := match args {
    List.empty => Option.none,
    List.cons a _ => Option.some a,
}

/// Delta: replace a reference to a known def with its body.
///
/// `Option.none` for anything but a bare `Term.var` naming a def in `defs`.
/// A bound de Bruijn variable (`idx >= 0`) is never a top-level def, so it is
/// refused explicitly rather than left to the lookup to miss.
#[partial]
def unfold_def (defs : HashMap String Term) (t : Term) : Option Term := match t {
    Term.var idx dbg =>
        if I64.lt idx 0
        then match dbg {
            DebugName.named id => str_map_lookup (id_text id) defs,
            DebugName.unnamed => Option.none,
        }
        else Option.none,
    _ => Option.none,
}

// ─── iota ────────────────────────────────────────────────────────────

/// Fire a `match` whose scrutinee has reduced to a constructor application.
///
/// This is the step that turns `match __dict_Add { mk add => add }` into
/// `add`. A dictionary is a single-constructor inductive, so its `match` has
/// one arm and the arm is selected by the constructor's NAME -- the same
/// `MatchCase.name` comparison `whnf.mo`'s `whnf_iota_case` makes, and for the
/// same reason: a `match` reaching here has already been type-checked, so the
/// arm names are resolved.
///
/// Deliberately NOT reusing `whnf_iota_case`: that needs a `Scope` to decide
/// whether the scrutinee's head names a real constructor
/// (`whnf_is_constructor`), and this module has none. The alternative -- a
/// scope per kernel -- is the cost the header's "why not `whnf`" section
/// declines. The price of that choice is stated plainly: this fires on any
/// head whose LAST dotted segment matches an arm name, so it is correct only
/// for a term that has already been type-checked, which a kernel body has.
///
/// `Option.none` when the scrutinee's head is not a name, or no arm matches. A
/// miss is not an error: it means the match is stuck, which is what a
/// non-dictionary scrutinee is.
#[partial]
pub def iota_match (scrut : Term) (cases : List MatchCase) : Option Term :=
    match constructor_head_of scrut {
        Option.none => Option.none,
        Option.some p =>
            match p {
                Pair.pair con_name field_args =>
                    match find_case_by_name con_name cases {
                        Option.some c => fire_case c field_args,
                        Option.none => Option.none,
                    },
            },
    }

/// The simple name of a constructor application and its field arguments, in
/// declaration order.
///
/// Two spellings, exactly as `whnf_con_head` documents: a `Term.con` (what a
/// hand-built fixture uses) and a free `Term.var` head whose name is a
/// constructor (what the parser and the elaborator actually build -- a
/// dictionary value is `__Dict_Add_I64.mk Add_I64_add`, a `Term.var` head
/// carrying the constructor's dotted name).
///
/// The name is reduced to its LAST dotted segment, because a `MatchCase.name`
/// is the bare constructor name (`mk`) while the reference is
/// `__Dict_Add_I64.mk`.
#[partial]
pub def constructor_head_of (t : Term) : Option (Pair String (List Term)) :=
    constructor_head_of_spine (spine_head_of t) (spine_args_of t)

/// The head and the spine's arguments, paired.
///
/// The SPINE is what matters and it is easy to get wrong: a dictionary value is
/// `__Dict_Add_I64.mk Add_I64_add`, an APPLICATION whose head is a bare
/// `Term.var`, not a `Term.con` -- so a version that matched only `Term.con`
/// (or only a bare `Term.var`) would never fire on the one shape this module
/// exists to fold. `spine_args_of` gives the arguments in written order, which
/// is also the order a `MatchCase`'s binders expect.
#[partial]
def constructor_head_of_spine (hd : Term) (args : List Term) : Option (Pair String (List Term)) := match term_peel hd {
    // A `Term.con` carries its own field arguments; the spine's are extra
    // applications on top of them (`(Foo.mk a) b`), which no kernel writes but
    // a partially applied constructor could produce.
    Term.con c =>
        match c {
            Con.mk name _typ _n cargs => match all_args_present cargs {
                Option.some field_args =>
                    Option.some (Pair.pair (ctor_last_segment (id_text name)) (List.append field_args args)),
                Option.none => Option.none,
            },
        },
    Term.var idx dbg =>
        if I64.lt idx 0
        then match dbg {
            DebugName.named id => Option.some (Pair.pair (ctor_last_segment (id_text id)) args),
            DebugName.unnamed => Option.none,
        }
        else Option.none,
    _ => Option.none,
}

/// The head of an application spine: `spine_args_of`'s dual, and the reason
/// `constructor_head_of` can be handed a whole application.
#[partial]
pub def spine_head_of (t : Term) : Term := match term_peel t {
    Term.app f _a => spine_head_of f,
    _ => term_peel t,
}

/// Every `Option Term` present, or `Option.none` -- `whnf_con_args`'s contract:
/// iota must not fire on a partially-elaborated constructor.
#[partial]
def all_args_present (args : List (Option Term)) : Option (List Term) := match args {
    List.empty => Option.some List.empty,
    List.cons h rest =>
        match h {
            Option.some a => match all_args_present rest {
                Option.some tl => Option.some (List.cons a tl),
                Option.none => Option.none,
            },
            Option.none => Option.none,
        },
}

/// The segment after the LAST `.` -- `__Dict_Add_I64.mk` -> `mk`. A name with
/// no dot is returned unchanged, so a bare `mk` works too.
#[partial]
pub def ctor_last_segment (s : String) : String :=
    let i : I64 := last_dot_pos s 0 (0 - 1) in
    if I64.lt i 0 then s else String.slice s (i + 1) (String.length s - i - 1)

#[partial]
def last_dot_pos (s : String) (i : I64) (last : I64) : I64 :=
    if I64.gt (i + 1) (String.length s) then last
    else match String.get s i {
        Option.some b => if U8.beq b 46u8 then last_dot_pos s (i + 1) i else last_dot_pos s (i + 1) last,
        Option.none => last,
    }

#[partial]
def find_case_by_name (want : String) (cases : List MatchCase) : Option MatchCase := match cases {
    List.empty => Option.none,
    List.cons c rest =>
        match c {
            MatchCase.mk name _args _body _fp _tn =>
                if String.beq (ctor_last_segment (id_text name)) want
                then Option.some c
                else find_case_by_name want rest,
        },
}

/// Fire one arm: substitute the constructor's field arguments for the arm's
/// pattern binders.
///
/// The binder convention is `whnf.mo`'s `whnf_subst_case_fields`, and it is
/// worth restating because getting it backwards is silent: the binders are the
/// arm's `n` levels-at-once, FIRST-declared field OUTERMOST, so the outermost
/// binder sits at index `n-1` and the fold substitutes OUTERMOST-FIRST -- step
/// `k` replaces index `k-1` with its argument shifted up by the `k-1` binders
/// still in scope. Substituting innermost-first would insert each argument
/// under-scoped and the next step would overwrite it.
#[partial]
pub def fire_case (c : MatchCase) (field_args : List Term) : Option Term :=
    match c {
        MatchCase.mk _name binders body _fp _tn =>
            let n : I64 := List.length binders in
            if I64.beq n (List.length field_args)
            then Option.some (subst_case_fields body field_args n)
            else Option.none,
    }

#[partial]
def subst_case_fields (body : Term) (args : List Term) (k : I64) : Term := match args {
    List.empty => body,
    List.cons a rest => subst_case_fields (term_subst (k - 1) (term_shift (k - 1) a) body) rest (k - 1),
}

// ─── the recursive rebuild ───────────────────────────────────────────

#[partial]
def reduce_children_with (defs : HashMap String Term) (t : Term) : Term := match t {
    Term.var _i _d => t,
    Term.var_macro _i _d => t,
    Term.sort _l => t,
    Term.hole => t,
    Term.ntv _n => t,
    Term.con _c => t,
    Term.lam b typ body => Term.lam b (reduce_with defs typ) (reduce_with defs body),
    Term.pi b arg ret => Term.pi b (reduce_with defs arg) (reduce_with defs ret),
    Term.app f a => Term.app (reduce_with defs f) (reduce_with defs a),
    Term.lit l => Term.lit (reduce_literal_with defs l),
    Term.quote_ inner => Term.quote_ (reduce_with defs inner),
    Term.ctx loc inner => Term.ctx loc (reduce_with defs inner),
    Term.cubical c => Term.cubical (reduce_cubical_with defs c),
    Term.elim e => Term.elim (reduce_elim_with defs e),
}

#[partial]
def reduce_literal_with (defs : HashMap String Term) (l : Literal) : Literal := match l {
    Literal.if_ a b c => Literal.if_ (reduce_with defs a) (reduce_with defs b) (reduce_with defs c),
    Literal.match_ scrut cases => Literal.match_ (reduce_with defs scrut) (reduce_cases_with defs cases),
    Literal.struct_lit fields tn => Literal.struct_lit (reduce_fields_with defs fields) (reduce_opt_with defs tn),
    Literal.struct_update base fields => Literal.struct_update (reduce_with defs base) (reduce_fields_with defs fields),
    _ => l,
}

#[partial]
def reduce_cases_with (defs : HashMap String Term) (cases : List MatchCase) : List MatchCase := match cases {
    List.empty => List.empty,
    List.cons c rest => List.cons (reduce_case_with defs c) (reduce_cases_with defs rest),
}

#[partial]
def reduce_case_with (defs : HashMap String Term) (c : MatchCase) : MatchCase :=
    match c {
        MatchCase.mk name args body fp tn => MatchCase.mk name args (reduce_with defs body) fp tn,
    }

#[partial]
def reduce_fields_with (defs : HashMap String Term) (fields : List StructLitField) : List StructLitField := match fields {
    List.empty => List.empty,
    List.cons f rest =>
        match f {
            StructLitField.mk name value =>
                List.cons (StructLitField.mk name (reduce_with defs value)) (reduce_fields_with defs rest),
        },
}

#[partial]
def reduce_opt_with (defs : HashMap String Term) (t : Option Term) : Option Term := match t {
    Option.some x => Option.some (reduce_with defs x),
    Option.none => Option.none,
}

#[partial]
def reduce_cubical_with (defs : HashMap String Term) (c : Cubical) : Cubical :=
    match c { Cubical.mk prim args => Cubical.mk prim (List.map (fn a => reduce_with defs a) args) }

#[partial]
def reduce_elim_with (defs : HashMap String Term) (e : Elim) : Elim :=
    { e with
        params := List.map (fn p => reduce_with defs p) e.params,
        indices := List.map (fn i => reduce_with defs i) e.indices,
        motive := reduce_with defs e.motive,
        minors := List.map (fn m => reduce_with defs m) e.minors,
        scrutinee := reduce_with defs e.scrutinee }

// ─── inlining ────────────────────────────────────────────────────────

/// How many unfoldings one kernel's closure may spend. A bound rather than a
/// tuning knob: a mutually recursive pair would otherwise not terminate, and
/// `detect.mo`'s recursion rule catches only a SELF-recursive def.
///
/// Reaching the budget is not silently ignored: `inline_term` stops unfolding
/// and leaves the reference in place, which `unresolved_refs_of` reports.
pub def inline_budget : I64 := 200

/// The definition table a kernel reduces against: every def's symbol mapped to
/// its body.
///
/// Built from the WHOLE decl list rather than a pre-filtered closure, because
/// a kernel's body names its helpers by symbol and the lookup key is
/// `def_name_str` -- so the honest way to build it is a scan.
/// `codegen/src/decls.mo`'s `build_def_name_map` does the same thing for
/// reachability; this is its term-valued sibling.
pub def build_def_table (decl_list : List Decl) : HashMap String Term :=
    build_def_table_go (extract_defs decl_list) str_map_empty

#[partial]
def build_def_table_go (defs : List Def) (acc : HashMap String Term) : HashMap String Term := match defs {
    List.empty => acc,
    List.cons d rest => build_def_table_go rest (str_map_insert (def_name_str d) (def_body_term d) acc),
}

/// Unfold every reachable top-level reference in `t`, up to `budget`
/// unfoldings.
///
/// Each step is `unfold_def`, which is the same delta step the reducer uses --
/// inlining is delta applied exhaustively rather than once. A reference to a
/// def NOT in the table is left alone: a native (which has no body) and a
/// kernel's own parameter (a bound de Bruijn variable) both fall in that
/// class, and neither is an error.
#[partial]
pub def inline_term (defs : HashMap String Term) (budget : I64) (t : Term) : Term :=
    if I64.lt budget 1
    then t
    else match term_peel t {
        Term.app f a => Term.app (inline_term defs (budget - 1) f) (inline_term defs (budget - 1) a),
        Term.lam b typ body => Term.lam b (inline_term defs budget typ) (inline_term defs budget body),
        Term.pi b arg ret => Term.pi b (inline_term defs budget arg) (inline_term defs budget ret),
        Term.lit l => Term.lit (inline_literal defs budget l),
        Term.elim e => Term.elim (inline_elim defs budget e),
        Term.ctx loc inner => Term.ctx loc (inline_term defs budget inner),
        Term.cubical c => Term.cubical (inline_cubical defs budget c),
        Term.quote_ inner => Term.quote_ (inline_term defs budget inner),
        Term.var _idx _dbg =>
            match unfold_def defs (term_peel t) {
                Option.some body => inline_term defs (budget - 1) body,
                Option.none => t,
            },
        _ => t,
    }

#[partial]
def inline_literal (defs : HashMap String Term) (budget : I64) (l : Literal) : Literal := match l {
    Literal.if_ a b c =>
        Literal.if_ (inline_term defs budget a) (inline_term defs budget b) (inline_term defs budget c),
    Literal.match_ scrut cases =>
        Literal.match_ (inline_term defs budget scrut) (inline_cases defs budget cases),
    Literal.struct_lit fields tn =>
        Literal.struct_lit (inline_fields defs budget fields) (inline_opt defs budget tn),
    Literal.struct_update base fields =>
        Literal.struct_update (inline_term defs budget base) (inline_fields defs budget fields),
    _ => l,
}

#[partial]
def inline_cases (defs : HashMap String Term) (budget : I64) (cases : List MatchCase) : List MatchCase := match cases {
    List.empty => List.empty,
    List.cons c rest => List.cons (inline_case defs budget c) (inline_cases defs budget rest),
}

#[partial]
def inline_case (defs : HashMap String Term) (budget : I64) (c : MatchCase) : MatchCase :=
    match c {
        MatchCase.mk name args body fp tn => MatchCase.mk name args (inline_term defs budget body) fp tn,
    }

#[partial]
def inline_fields (defs : HashMap String Term) (budget : I64) (fields : List StructLitField) : List StructLitField := match fields {
    List.empty => List.empty,
    List.cons f rest =>
        match f {
            StructLitField.mk name value =>
                List.cons (StructLitField.mk name (inline_term defs budget value)) (inline_fields defs budget rest),
        },
}

#[partial]
def inline_opt (defs : HashMap String Term) (budget : I64) (t : Option Term) : Option Term := match t {
    Option.some x => Option.some (inline_term defs budget x),
    Option.none => Option.none,
}

#[partial]
def inline_cubical (defs : HashMap String Term) (budget : I64) (c : Cubical) : Cubical :=
    match c { Cubical.mk prim args => Cubical.mk prim (List.map (fn a => inline_term defs budget a) args) }

#[partial]
def inline_elim (defs : HashMap String Term) (budget : I64) (e : Elim) : Elim :=
    { e with
        params := List.map (fn p => inline_term defs budget p) e.params,
        indices := List.map (fn i => inline_term defs budget i) e.indices,
        motive := inline_term defs budget e.motive,
        minors := List.map (fn m => inline_term defs budget m) e.minors,
        scrutinee := inline_term defs budget e.scrutinee }

// ─── unresolved references (the inliner's own diagnostic) ────────────

/// Every symbol `t` still references that is a known def -- i.e. a helper the
/// inliner did not manage to unfold.
///
/// This is what makes the `inline_budget` stop HONEST rather than silent. A
/// body with an unresolved reference is one `scalar.mo` cannot lower (a call
/// to a top-level def is not an emittable operation), and reporting it here is
/// the difference between a diagnostic and a wrong answer.
///
/// A native is not a def, so it is not reported; a kernel's own parameter is a
/// bound de Bruijn variable, so it is not reported either.
pub def unresolved_refs_of (t : Term) (defs : HashMap String Term) : List String :=
    unresolved_refs_go t defs List.empty

#[partial]
def unresolved_refs_go (t : Term) (defs : HashMap String Term) (acc : List String) : List String :=
    match term_peel t {
        Term.var idx dbg =>
            if I64.lt idx 0
            then match dbg {
                DebugName.named id =>
                    let s : String := id_text id in
                    match str_map_lookup s defs {
                        Option.some _ => List.cons s acc,
                        Option.none => acc,
                    },
                DebugName.unnamed => acc,
            }
            else acc,
        _ => unresolved_refs_children (term_children_of t) defs acc,
    }

#[partial]
def unresolved_refs_children (children : List Term) (defs : HashMap String Term) (acc : List String) : List String := match children {
    List.empty => acc,
    List.cons c rest => unresolved_refs_children rest defs (unresolved_refs_go c defs acc),
}

/// The immediate sub-terms of a term, in VALUE positions.
///
/// `lib::kernel::detect`'s `value_children` is the same walk, and it is
/// `pub` for exactly this: a second copy would be a second place to forget a
/// `Term` variant. It visits value positions only, which is what this needs --
/// a reference in a TYPE position is not a call `scalar.mo` has to emit.
#[partial]
def term_children_of (t : Term) : List Term := value_children t

// ─── extracting one kernel ───────────────────────────────────────────

/// Extract `kernel` for the emitter: inline every reachable helper, reduce,
/// and collect every diagnostic that stops a full extraction.
///
/// `call_sites` is where the SIXTH rule is actually decided, and its being a
/// PARAMETER is the whole point: "dimensions literal at the call site" is a
/// property of a CALL, so it cannot be read off `kernel`'s own def. The caller
/// passes `(callee, args)` for each call it found -- `call_sites_of` is the
/// walk that finds them -- and `dim_positions` says which argument positions
/// are dimensions.
///
/// A kernel with a diagnostic still gets a body, so a caller that wants to
/// report and continue can. `KernelExtract.ready` is what a caller checks
/// before emitting.
#[partial]
pub def extract_kernel (kernel : Def) (decl_list : List Decl) (call_sites : List KernelCallSite) (dim_positions : List I64) : KernelExtract :=
    let defs : HashMap String Term := build_def_table decl_list in
    // `def_param_chain_body`, not `def_body_term`: a parsed def's term is a
    // parameter lambda chain, so the unstripped read hands `scalar.mo` a body
    // wrapped in one `Term.lam` per kernel parameter -- which it would lower as
    // a nested function rather than the function's own entry block, and which
    // `detect.mo`'s closure rule would (correctly) refuse one layer up. The
    // extractor is the last place the chain can be dropped, so it is dropped
    // here.
    let body : Term := def_param_chain_body kernel in
    let inlined : Term := inline_term defs inline_budget body in
    let reduced : Term := reduce_with defs inlined in
    let name : String := def_name_str kernel in
    let call_diags : List KernelDiagnostic := dim_diagnostics_for_sites call_sites dim_positions in
    KernelExtract.mk name (kernel_params kernel) reduced
        (List.append call_diags (unresolved_ref_diagnostics name reduced defs))

/// One call to a kernel: the callee's symbol and the arguments as written.
pub struct KernelCallSite {
    callee : String,
    args : List Term,
}

/// Every call in `decl_list` whose head names one of `kernels` -- the
/// call sites the sixth rule is judged at.
///
/// A kernel may be called from ordinary host code (that is the normal case:
/// `motes/kernel_example/`'s `main` calls `saxpy`), so the walk is over the
/// WHOLE decl list rather than the kernel's own body. That is the reason this
/// rule could not live in `detect.mo`: its input is not a `Def`.
#[partial]
pub def call_sites_of (decl_list : List Decl) (kernels : List String) : List KernelCallSite :=
    call_sites_of_defs (extract_defs decl_list) kernels List.empty

#[partial]
def call_sites_of_defs (defs : List Def) (kernels : List String) (acc : List KernelCallSite) : List KernelCallSite := match defs {
    List.empty => acc,
    List.cons d rest =>
        call_sites_of_defs rest kernels (call_sites_in_term (def_body_term d) kernels acc),
}

/// Every call spine in `t` whose head names a kernel, consed onto `acc`.
///
/// The head is read with `head_name_of`, which peels applications -- so
/// `saxpy dst 16` and a partially applied `saxpy dst` both report the same
/// callee, and the ARGUMENTS are the spine's, in written order.
#[partial]
pub def call_sites_in_term (t : Term) (kernels : List String) (acc : List KernelCallSite) : List KernelCallSite :=
    call_sites_in_term_go t kernels acc

#[partial]
def call_sites_in_term_go (t : Term) (kernels : List String) (acc : List KernelCallSite) : List KernelCallSite :=
    match term_peel t {
        Term.app _f _a =>
            let here : List KernelCallSite :=
                let callee : String := head_name_of t in
                if contains_str kernels callee
                then List.cons (KernelCallSite.mk callee (spine_args_of t)) List.empty
                else List.empty in
            let deeper : List KernelCallSite :=
                call_sites_in_children (value_children t) kernels acc in
            List.append here deeper,
        Term.lam _b _typ body => call_sites_in_term_go body kernels acc,
        Term.pi _b _arg ret => call_sites_in_term_go ret kernels acc,
        _ => call_sites_in_children (value_children t) kernels acc,
    }

#[partial]
def call_sites_in_children (children : List Term) (kernels : List String) (acc : List KernelCallSite) : List KernelCallSite := match children {
    List.empty => acc,
    List.cons c rest => call_sites_in_children rest kernels (call_sites_in_term_go c kernels acc),
}

/// A call spine's arguments, left to right. `Term.app f a` peels its
/// OUTERMOST (last-applied) argument first, so the accumulator is built
/// tail-first and this reverses -- `flatten_call_spine`'s own convention, and
/// the reason its comment is worth reading before rewriting this.
#[partial]
pub def spine_args_of (t : Term) : List Term :=
    spine_args_go t List.empty

#[partial]
def spine_args_go (t : Term) (acc : List Term) : List Term := match term_peel t {
    Term.app f a => spine_args_go f (List.cons a acc),
    _ => acc,
}

#[partial]
def contains_str (xs : List String) (x : String) : Bool := match xs {
    List.empty => false,
    List.cons h rest => if String.beq h x then true else contains_str rest x,
}

/// The sixth rule over a list of call sites -- `dim_diagnostics` lifted to the
/// shape `call_sites_of` returns.
#[partial]
pub def dim_diagnostics_for_sites (sites : List KernelCallSite) (positions : List I64) : List KernelDiagnostic := match sites {
    List.empty => List.empty,
    List.cons s rest =>
        List.append (dim_diagnostics s.callee s.args positions)
            (dim_diagnostics_for_sites rest positions),
}

/// One diagnostic per unresolved reference, so the reason the inliner stopped
/// is reported rather than swallowed.
#[partial]
def unresolved_ref_diagnostics (kernel : String) (t : Term) (defs : HashMap String Term) : List KernelDiagnostic :=
    List.map (fn s => KernelDiagnostic.of kernel "inline" (String.concat "unresolved " s))
        (unresolved_refs_of t defs)

/// The kernel's explicit parameters, from its declared type's pi spine.
///
/// A non-explicit binder never appears: `detect.mo`'s polymorphism rule
/// refuses a kernel whose type has one, so reaching this with an implicit
/// binder would mean the checker did not run. They are SKIPPED rather than
/// reported, because the only caller that can get here already rejected them.
#[partial]
pub def kernel_params (kernel : Def) : List KernelParam :=
    match kernel {
        Def.mk { typ, .. } => kernel_params_of typ,
    }

#[partial]
def kernel_params_of (typ : Term) : List KernelParam := match term_peel typ {
    Term.pi b dom ret =>
        if binder_is_explicit b
        then List.cons (KernelParam.mk (binder_text b) dom) (kernel_params_of ret)
        else kernel_params_of ret,
    _ => List.empty,
}

pub def binder_text (b : Binder) : String := match binder_name b {
    DebugName.named id => id_text id,
    DebugName.unnamed => "x",
}

/// The name at the head of an application spine, or `""`.
#[partial]
pub def head_name_of (t : Term) : String := match term_peel t {
    Term.app f _a => head_name_of f,
    Term.var _idx dbg => match dbg {
        DebugName.named id => id_text id,
        DebugName.unnamed => "",
    },
    _ => "",
}

/// Every explicit `I64` parameter position -- `dim_positions`'s honest
/// placeholder until `shape.mo` can say which ones are really shapes.
///
/// "Is this type `I64`?" is read off the pi spine's domain by BARE NAME, which
/// is deliberately loose: a parameter whose type is an alias for `I64` is a
/// dimension too, and a false positive costs one diagnostic on a kernel whose
/// dimension is genuinely non-literal. Erring the other way -- calling a
/// dimension a data parameter -- would let a dynamic shape through, which the
/// plan forbids.
#[partial]
pub def dim_positions_of (kernel : Def) : List I64 :=
    match kernel {
        Def.mk { typ, .. } => dim_positions_of_typ typ 0,
    }

#[partial]
def dim_positions_of_typ (typ : Term) (i : I64) : List I64 := match term_peel typ {
    Term.pi b dom ret =>
        if binder_is_explicit b
        then
            if is_i64_type dom
            then List.cons i (dim_positions_of_typ ret (i + 1))
            else dim_positions_of_typ ret (i + 1)
        else dim_positions_of_typ ret i,
    _ => List.empty,
}

/// Is `t` the bare type name `I64`? A `Term.var`/`Term.con` head whose last
/// dotted segment is `I64`, and nothing else -- deliberately not a type
/// comparison, which this module has no scope to make.
#[partial]
pub def is_i64_type (t : Term) : Bool := match term_peel t {
    Term.var _idx dbg => match dbg {
        DebugName.named id => String.beq (ctor_last_segment (id_text id)) "I64",
        DebugName.unnamed => false,
    },
    Term.con c => match c {
        Con.mk name _typ _n _args => String.beq (ctor_last_segment (id_text name)) "I64",
    },
    _ => false,
}
