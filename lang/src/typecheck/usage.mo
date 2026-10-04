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
/// 2. **Type positions count 0.** A `Term.pi`'s argument and a
///    `Term.lam`'s own annotation are compile-time positions. A variable
///    mentioned there is erased before run time and consumes nothing.
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
  Binder, Con, DebugName, FieldPattern, Identifier, InductConstructor, Inductive, Literal,
  Location, MatchCase, ModulePath, Multiplicity, NamePath, Native, Param, Scope, ScopeData,
  SortLevel, StructLitField, Term, Visibility, binder_anon, binder_binder, binder_explicit,
  binder_is_explicit, binder_name, show_identifier, show_name_path,
}
use lib::scope {
  find_constructor_in_inductive, scope_data_empty, scope_find_all_inductives_by_constructor,
  scope_globals,
}
use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}
use std::map {HashMap}
use std::list {List.length}

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
        Term.lam _b _typ body => uses_of (target + 1) body,
        // An implicit-binder `pi` (the former `forall`) still binds a
        // variable its body may mention at run time (macro/level
        // machinery aside, the body of a `binder`-info pi is walked like
        // the old forall's body was). An explicit-binder `pi` is a
        // function TYPE, entirely compile-time: both halves are type
        // positions, so the whole node contributes nothing.
        Term.pi b _arg ret =>
            if Bool.not (binder_is_explicit b) then uses_of (target + 1) ret else 0,
        Term.app callee arg => uses_of target callee + uses_of target arg,
        Term.lit value => uses_of_literal target value,
        Term.ntv n => uses_of_native target n,
        Term.con c => uses_of_con target c,
        Term.sort _level => 0,
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

// ─── Owning vs borrowing uses ──────────────────────────────────────
//
// M1 said 11.3% of binders are used more than once, and that those
// concentrate in `String`, `List`, `Term` and `ModulePath` -- heap types
// Design B's Copy policy says can never be Copy. That decided the gate
// in favour of borrows. This section measures what borrows would
// actually buy, which is the question the gate raised and did not
// answer.
//
// The distinction: a use that only READS a value can be a borrow (the
// owner is not moved, so it does not count against Σ). A use that takes
// OWNERSHIP -- storing the value into a constructor, or being the value
// a scope produces -- genuinely moves it. Under affine-plus-borrows a
// binder can afford **one** owning use and any number of reads. Two
// owning uses need real duplication: `Copy`, `Clone`, or a rewrite.
//
// So `owning_uses ≤ 1` is the borrowable set, and `owning_uses ≥ 2` is
// the irreducible migration cost.
//
// **This bound is optimistic, and in the opposite direction from the
// report's Copy approximation** -- stated plainly because the two
// bracket the truth rather than agreeing. An argument passed to a
// function is counted as a read, but it is only really a borrow if the
// callee does not retain it; a callee that stores its argument makes
// that an owning use in disguise. Telling those apart is
// interprocedural, which this is not. So: Copy-only is the pessimistic
// bound, borrows-work-for-all-reads is the optimistic one, and the real
// cost sits between them.

/// Where a use of a binder sits, which is what says whether it could be
/// a borrow.
pub type UsePos {
    /// Callee of an application -- calling a closure reads it.
    up_app_head,
    /// Argument of an ordinary (non-constructor) application. A read
    /// **if** the callee does not retain it; see the caveat above.
    up_app_arg,
    /// Scrutinee of a `match`, or an `if`'s condition. Always a read:
    /// matching inspects a value, it does not consume it.
    up_scrutinee,
    /// Stored into a constructor, a struct literal, or a struct update.
    /// An OWNING use -- the value outlives the expression.
    up_con_field,
    /// The value a scope produces: a bare body, a branch result, a
    /// match arm's result. An OWNING use -- it is moved out.
    up_value,
}

/// Owning uses of `target` in `t` — the `up_con_field` and `up_value`
/// ones. `0` or `1` means the binder is borrowable as written.
#[partial]
pub def owning_uses (ctors : HashMap String Bool) (borrows : HashMap String Bool) (target : I64) (t : Term) : I64 :=
    owning_at ctors borrows UsePos.up_value target t

/// The head of an application spine, peeled of `ctx` wrappers.
///
/// Needed because a multi-argument constructor is CURRIED: `List.cons x
/// xs` is `app (app List.cons x) xs`, so its arguments arrive at
/// `Term.app`, not at `Term.con`'s own `args`. Classifying those as
/// ordinary call arguments would count an owning store into a cons cell
/// as a read, which is exactly the direction that would flatter the
/// design.
#[partial]
def app_spine_head (t : Term) : Term :=
    match t {
        Term.app callee _arg => app_spine_head callee,
        Term.ctx _loc inner => app_spine_head inner,
        _ => t,
    }

/// The set of names that refer to a constructor, for
/// `head_is_ctor`. Built once per report run and threaded down.
///
/// **This exists because testing for `Term.con` does not work.** A probe
/// over the compiler's own elaborated closure found 44,609 application
/// nodes, of which **zero** had a `Term.con` spine head, against 19,738
/// with a dotted name — elaboration leaves a constructor reference as an
/// ordinary named `Term.var` (there are only 212 `Term.con` nodes in the
/// whole tree). A `Term.con` test therefore never fires, and every
/// constructor store silently reads as a call argument. That produced a
/// "99.9% of over-uses are borrowable" figure which was an artifact of
/// the blind classifier, not a property of the corpus.
///
/// A dotted-name test alone would be just as wrong in the other
/// direction: most of those 19,738 heads are ordinary qualified calls
/// (`String.concat`, `List.map`), not constructors. So the names are
/// resolved against the real inductives in scope.
///
/// Each constructor goes in twice: under its bare name (`cons`) and
/// under its rendered path (`List.cons`), so a head resolves whichever
/// spelling its `DebugName` carries.
pub def ctor_name_set (s : Scope) : HashMap String Bool :=
    let sd : ScopeData := scope_globals s in
    ctor_names_from_inds (HashMap.to_list sd.inductives) str_map_empty

#[partial]
def ctor_names_from_inds (pairs : List (Pair String Inductive)) (acc : HashMap String Bool) : HashMap String Bool :=
    match pairs {
        List.empty => acc,
        List.cons p rest =>
            match p {
                Pair.pair _key ind =>
                    match ind {
                        Inductive.mk name _params _typ ctors _attrs _vis =>
                            ctor_names_from_inds rest (ctor_names_from_ctors (show_name_path name) ctors acc),
                    },
            },
    }

/// Registers every spelling a real reference can render with: the ctor's
/// own full path, its bare segment, and `<Inductive>.<ctor>` — the
/// type-qualified form a dotted reference actually carries in an
/// elaborated term (`Borrow.of`, `Pair.pair`). Registering the dotted
/// spellings here is what lets `name_is_ctor` match EXACTLY (no
/// last-segment fallback): `Path.of` — a def on std/path.mo's `Path`, not
/// any inductive's ctor — then misses, instead of inheriting whatever
/// unrelated type happens to declare a bare `of`.
#[partial]
def ctor_names_from_ctors (ind_name : String) (ctors : List InductConstructor) (acc : HashMap String Bool) : HashMap String Bool :=
    match ctors {
        List.empty => acc,
        List.cons c rest =>
            match c {
                InductConstructor.mk name _params _typ =>
                    let full : String := show_name_path name in
                    let bare : String := last_dotted_segment full in
                    let with_full : HashMap String Bool :=
                        str_map_insert (String.concat (String.concat ind_name ".") bare) true
                            (str_map_insert full true acc) in
                    ctor_names_from_ctors ind_name rest (str_map_insert bare true with_full),
            },
    }

/// `"List.cons"` -> `"cons"`; a name with no dot is returned unchanged.
/// Mirrors `lang/typecheck/infer.mo`'s own `last_dotted_segment_go`,
/// which is not exported.
def last_dotted_segment (s : String) : String :=
    last_dotted_segment_go s (String.length s - 1)

#[terminating]
def last_dotted_segment_go (s : String) (idx : I64) : String :=
    if I64.lt idx 0 then s
    else
        match (String.get s idx : Option U8) {
            Option.none => s,
            Option.some byte_val =>
                if U8.beq byte_val 46u8 then // '.' is ASCII 46
                    // `String.drop`, not `String.slice`: slice's second
                    // argument is a LENGTH, not an end index, and the
                    // existing call sites that pass an end index only
                    // survive because over-reads get clamped.
                    String.drop (idx + 1) s
                else last_dotted_segment_go s (idx - 1),
        }

/// Is this spine head a constructor, so its arguments are owning stores
/// rather than call arguments? Checks the rendered `DebugName` against
/// `ctors` exactly — the set holds the bare, full, and type-qualified
/// spellings (`name_is_ctor`'s own doc comment says why exact).
def head_is_ctor (ctors : HashMap String Bool) (t : Term) : Bool :=
    match t {
        Term.con _c => true,
        Term.var _idx dbg =>
            match dbg {
                DebugName.named id => name_is_ctor ctors (show_identifier id),
                DebugName.unnamed => false,
            },
        _ => false,
    }

/// Exact match against the ctor set, with NO last-dotted-segment
/// fallback — the same discipline as `name_is_borrow` below. The set
/// itself carries the dotted spellings a real qualified reference can
/// render with (`Ind.ctor`, registered by `ctor_names_from_ctors` from
/// the inductive's own name), so no fallback is needed to match those.
/// Fail-open here classifies a non-constructor head as a store:
/// `Path.of` (a def on `std/path.mo`'s `Path`) would strip to `of`,
/// inherit `Borrow`'s bare `of`, and report a binder read once and
/// handed to `Path.of` once as `value_used_after_move` — the one
/// diagnostic that says a borrow cannot fix it, when a borrow is
/// exactly the fix.
def name_is_ctor (ctors : HashMap String Bool) (nm : String) : Bool :=
    match str_map_lookup nm ctors {
        Option.some _ => true,
        Option.none => false,
    }

/// Exact match against the borrow set, with NO last-dotted-segment
/// fallback. A dotted spelling the set does not hold verbatim is not a
/// borrow: `Path.of` (a def on `std/path.mo`'s `Path`, not a constructor
/// at all, so `borrow_of_name_set`'s sole-`of`-inductive guard never
/// sees it) would strip to `of` and excuse a real over-use as a borrow
/// read. Missing a real borrow costs one advisory `copy_required`, which
/// is the cheap direction.
def name_is_borrow (borrows : HashMap String Bool) (nm : String) : Bool :=
    match str_map_lookup nm borrows {
        Option.some _ => true,
        Option.none => false,
    }

/// Real identity for `Borrow.of` (`init/src/borrow.mo`, B1 of the borrow
/// design), not a bare string
/// match: `borrow_of_name_set` below resolves the ONE real `Borrow`
/// inductive in scope, so a future type that also declares a bare `of`
/// constructor is no longer misclassified as a borrow. Matched exactly
/// (see `name_is_borrow` above), against a set built once by the caller.
def head_is_borrow_of (borrows : HashMap String Bool) (t : Term) : Bool :=
    match t {
        Term.var _idx dbg =>
            match dbg {
                DebugName.named id => name_is_borrow borrows (show_identifier id),
                DebugName.unnamed => false,
            },
        _ => false,
    }

/// The set `head_is_borrow_of` checks a spine head's rendered name
/// against — like `ctor_name_set`, but scoped to exactly the inductive
/// named `Borrow`, not every registered constructor. Built once per
/// caller, same as `ctors`.
///
/// The dotted spelling (`"Borrow.of"`) is registered unconditionally: a
/// two-segment name only collides with another type also literally named
/// `Borrow`, already a whole-program name collision this checker doesn't
/// otherwise tolerate anywhere else. The bare spelling (`"of"`) is
/// registered ONLY when `Borrow` is the SOLE inductive in scope declaring
/// a constructor by that name — failing closed on exactly the ambiguity
/// `ctor_field_type` above already fails closed on, so a same-named `of`
/// on some other type is no longer counted as a borrow.
pub def borrow_of_name_set (s : Scope) : HashMap String Bool :=
    let of_id : NamePath := NamePath.npath (List.cons (Identifier.id "of") List.empty) in
    let dotted : HashMap String Bool := str_map_insert "Borrow.of" true str_map_empty in
    match scope_find_all_inductives_by_constructor of_id s {
        List.empty => dotted,
        List.cons ind rest =>
            match rest {
                List.empty =>
                    if inductive_named_borrow ind then str_map_insert "of" true dotted
                    else dotted,
                List.cons _ _ => dotted,
            },
    }

def inductive_named_borrow (ind : Inductive) : Bool :=
    match ind {
        Inductive.mk name _params _typ _ctors _attrs _vis => String.beq (show_name_path name) "Borrow",
    }

// ─── Borrow-aware use counting ──────────────────────────────────────
//
// The B1 gap this closes: `f (Borrow.of x); g (Borrow.of x)` uses `x`
// twice but consumes it ZERO times, so the raw `count` over-uses the
// binder even though every use is genuinely free. The affine gate
// (`affine.mo`'s `check_binder`) must compare against the uses that
// count against Σ, not the uses that merely mention the name.

/// Uses of `target` in `t` that count against the affine budget:
/// `uses_of` minus the occurrences that are the DIRECT argument of a
/// real `Borrow.of` call (per `head_is_borrow_of`).
///
/// `borrowed_here` says this subterm IS that direct argument, and only
/// a `Term.var` under it is excused. Anything nested deeper resets:
/// `Borrow.of (f x)` runs `f x` to produce the borrowed value, which is
/// a real use of `x`, so excusing it would hide a genuine double-use.
/// The asymmetry is deliberate in the same direction as everything else
/// here — a missed borrow costs one advisory `copy_required` (fail
/// closed); a wrongly excused use would be a false negative.
///
/// Combination rules are `uses_of`'s EXACTLY — same sums, same
/// per-branch maxes — so `uses_of - borrow_aware_uses` is a
/// branch-consistent borrowed count. That is why `BinderUse.borrowed`
/// is computed as the difference rather than by a separate borrowed
/// walk: two walks that each take their own max across match arms
/// would subtract a borrow in one arm from a use in another, and the
/// gate would let a binder through that one arm genuinely over-uses.
#[partial]
pub def borrow_aware_uses (borrows : HashMap String Bool) (target : I64) (t : Term) : I64 :=
    borrow_aware_at borrows false target t

#[partial]
def borrow_aware_at (borrows : HashMap String Bool) (borrowed_here : Bool) (target : I64) (t : Term) : I64 :=
    match t {
        Term.var idx _dbg =>
            if I64.beq idx target then (if borrowed_here then 0 else 1) else 0,
        Term.var_macro _idx _dbg => 0,
        // A lambda body is a closure the borrow may wrap but does not
        // enter: occurrences inside are captured, which is a real use.
        Term.lam _b _typ body => borrow_aware_at borrows false (target + 1) body,
        // Non-explicit `pi` (the former `forall`) still binds; explicit
        // `pi` is a compile-time function type and contributes nothing.
        Term.pi b _arg ret =>
            if Bool.not (binder_is_explicit b)
            then borrow_aware_at borrows false (target + 1) ret
            else 0,
        Term.app callee arg =>
            let head : Term := app_spine_head callee in
            borrow_aware_at borrows false target callee
                + borrow_aware_at borrows (head_is_borrow_of borrows head) target arg,
        Term.lit value => borrow_aware_literal borrows borrowed_here target value,
        Term.ntv n =>
            match n {
                Native.mk _name _num_args args => borrow_aware_opt_args borrows target args,
            },
        Term.con c =>
            match c {
                Con.mk _name _typ_name _num_args args => borrow_aware_opt_args borrows target args,
            },
        Term.sort _level => 0,
        Term.hole => 0,
        Term.quote_ _inner => 0,
        Term.ctx _loc inner => borrow_aware_at borrows borrowed_here target inner,
    }

#[partial]
def borrow_aware_literal (borrows : HashMap String Bool) (borrowed_here : Bool) (target : I64) (l : Literal) : I64 :=
    match l {
        Literal.str _v => 0,
        Literal.char _v => 0,
        Literal.num _n _suf => 0,
        Literal.flt _t _suf => 0,
        // The condition runs to DECIDE, so it is a real use; the branch
        // that runs IS the value being borrowed, so it inherits the
        // flag — `Borrow.of (if c then x else y)` really does borrow
        // `x`.
        Literal.if_ cond then_ else_ =>
            borrow_aware_at borrows false target cond
                + i64_max (borrow_aware_at borrows borrowed_here target then_)
                    (borrow_aware_at borrows borrowed_here target else_),
        // Same split as `if_`: scrutinee to decide, arm body is the
        // borrowed value.
        Literal.match_ scrut cases =>
            borrow_aware_at borrows false target scrut
                + borrow_aware_cases borrows borrowed_here target cases,
        // Field values are stored into a new value first; the borrow
        // wraps the result, not the fields.
        Literal.struct_lit fields _type_name => borrow_aware_fields borrows target fields,
        Literal.struct_update base fields =>
            borrow_aware_at borrows false target base + borrow_aware_fields borrows target fields,
    }

#[partial]
def borrow_aware_cases (borrows : HashMap String Bool) (borrowed_here : Bool) (target : I64) (cases : List MatchCase) : I64 :=
    match cases {
        List.empty => 0,
        List.cons c rest =>
            i64_max (borrow_aware_case borrows borrowed_here target c)
                (borrow_aware_cases borrows borrowed_here target rest),
    }

#[partial]
def borrow_aware_case (borrows : HashMap String Bool) (borrowed_here : Bool) (target : I64) (c : MatchCase) : I64 :=
    match c {
        MatchCase.mc _name args body _fp =>
            borrow_aware_at borrows borrowed_here (target + List.length args) body,
    }

#[partial]
def borrow_aware_fields (borrows : HashMap String Bool) (target : I64) (fields : List StructLitField) : I64 :=
    match fields {
        List.empty => 0,
        List.cons f rest =>
            match f {
                StructLitField.mk _name value =>
                    borrow_aware_at borrows false target value + borrow_aware_fields borrows target rest,
            },
    }

#[partial]
def borrow_aware_opt_args (borrows : HashMap String Bool) (target : I64) (args : List (Option Term)) : I64 :=
    match args {
        List.empty => 0,
        List.cons a rest =>
            match a {
                Option.some t => borrow_aware_at borrows false target t + borrow_aware_opt_args borrows target rest,
                Option.none => borrow_aware_opt_args borrows target rest,
            },
    }

/// `ctx` is the position the CURRENT subterm occupies. A `Term.var`
/// matching `target` contributes 1 when that position is an owning one.
#[partial]
def owning_at (ctors : HashMap String Bool) (borrows : HashMap String Bool) (ctx : UsePos) (target : I64) (t : Term) : I64 :=
    match t {
        Term.var idx _dbg =>
            if I64.beq idx target then (if pos_is_owning ctx then 1 else 0) else 0,
        Term.var_macro _idx _dbg => 0,
        // A binder resets the position: its body is the value the
        // closure produces, not whatever slot the closure itself fills.
        Term.lam _b _typ body => owning_at ctors borrows UsePos.up_value (target + 1) body,
        // Non-explicit `pi` (the former `forall`) still binds; explicit
        // `pi` is a compile-time function type and contributes nothing.
        Term.pi b _arg ret =>
            if Bool.not (binder_is_explicit b)
            then owning_at ctors borrows UsePos.up_value (target + 1) ret
            else 0,
        Term.app callee arg =>
            let head : Term := app_spine_head callee in
            let arg_pos : UsePos :=
                // Borrowing wins over "is a constructor at all": `of`
                // IS registered in `ctors` (it is a real constructor),
                // so this check must come first or `head_is_ctor` would
                // shadow it and every borrow would count as an owning
                // store -- the exact miscount B1 exists to prevent.
                if head_is_borrow_of borrows head then UsePos.up_app_arg
                else if head_is_ctor ctors head then UsePos.up_con_field
                else UsePos.up_app_arg in
            owning_at ctors borrows UsePos.up_app_head target callee + owning_at ctors borrows arg_pos target arg,
        Term.lit value => owning_at_literal ctors borrows ctx target value,
        // A native's arguments are call arguments, not stores.
        Term.ntv n =>
            match n {
                Native.mk _name _num_args args => owning_at_opt_args ctors borrows UsePos.up_app_arg target args,
            },
        Term.con c =>
            match c {
                Con.mk _name _typ_name _num_args args => owning_at_opt_args ctors borrows UsePos.up_con_field target args,
            },
        Term.sort _level => 0,
        Term.hole => 0,
        Term.quote_ _inner => 0,
        Term.ctx _loc inner => owning_at ctors borrows ctx target inner,
    }

def pos_is_owning (p : UsePos) : Bool :=
    match p {
        UsePos.up_con_field => true,
        UsePos.up_value => true,
        UsePos.up_app_head => false,
        UsePos.up_app_arg => false,
        UsePos.up_scrutinee => false,
    }

#[partial]
def owning_at_literal (ctors : HashMap String Bool) (borrows : HashMap String Bool) (ctx : UsePos) (target : I64) (l : Literal) : I64 :=
    match l {
        Literal.str _v => 0,
        Literal.char _v => 0,
        Literal.num _n _suf => 0,
        Literal.flt _t _suf => 0,
        // Branches inherit the position the whole `if` occupies, and
        // combine by MAX for the same reason `uses_of` does -- only one
        // of them runs, so only one of them owns.
        Literal.if_ cond then_ else_ =>
            owning_at ctors borrows UsePos.up_scrutinee target cond
                + i64_max (owning_at ctors borrows ctx target then_) (owning_at ctors borrows ctx target else_),
        Literal.match_ scrut cases =>
            owning_at ctors borrows UsePos.up_scrutinee target scrut + owning_at_cases ctors borrows ctx target cases,
        Literal.struct_lit fields _type_name => owning_at_fields ctors borrows target fields,
        // The base of a struct update is consumed to build the new one.
        Literal.struct_update base fields =>
            owning_at ctors borrows UsePos.up_con_field target base + owning_at_fields ctors borrows target fields,
    }

#[partial]
def owning_at_cases (ctors : HashMap String Bool) (borrows : HashMap String Bool) (ctx : UsePos) (target : I64) (cases : List MatchCase) : I64 :=
    match cases {
        List.empty => 0,
        List.cons c rest =>
            i64_max (owning_at_case ctors borrows ctx target c) (owning_at_cases ctors borrows ctx target rest),
    }

#[partial]
def owning_at_case (ctors : HashMap String Bool) (borrows : HashMap String Bool) (ctx : UsePos) (target : I64) (c : MatchCase) : I64 :=
    match c {
        MatchCase.mc _name args body _fp => owning_at ctors borrows ctx (target + List.length args) body,
    }

#[partial]
def owning_at_fields (ctors : HashMap String Bool) (borrows : HashMap String Bool) (target : I64) (fields : List StructLitField) : I64 :=
    match fields {
        List.empty => 0,
        List.cons f rest =>
            match f {
                StructLitField.mk _name value =>
                    owning_at ctors borrows UsePos.up_con_field target value + owning_at_fields ctors borrows target rest,
            },
    }

#[partial]
def owning_at_opt_args (ctors : HashMap String Bool) (borrows : HashMap String Bool) (ctx : UsePos) (target : I64) (args : List (Option Term)) : I64 :=
    match args {
        List.empty => 0,
        List.cons a rest =>
            match a {
                Option.some t => owning_at ctors borrows ctx target t + owning_at_opt_args ctors borrows ctx target rest,
                Option.none => owning_at_opt_args ctors borrows ctx target rest,
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
    /// For a `bk_match` binder, the constructor whose pattern bound it;
    /// `Identifier.id ""` for a `bk_lam` one. Paired with `pos`, this is
    /// everything `attribute_binder_types` needs to look the real type
    /// up later, without this walk taking a `Scope`.
    ctor : Identifier := Identifier.id "",
    /// Owning uses of this binder — `owning_uses` on its body. `0` or
    /// `1` means it is borrowable as written (one move, the rest
    /// reads); `2` or more means it genuinely needs duplication.
    owning : I64 := 0,
    /// Borrowed uses — `count` minus `borrow_aware_uses` on this
    /// binder's body: the occurrences that are the direct argument of a
    /// real `Borrow.of` call. Computed as a difference because the two
    /// walks share branch-combination rules, which keeps it exact where
    /// one match arm borrows what another arm consumes; a separately
    /// borrowed-per-branch-maxed count would under-count there. The
    /// affine gate in `affine.mo` compares `count - borrowed`, not
    /// `count`.
    borrowed : I64 := 0,
    /// Position of this binder within that constructor's arguments, in
    /// written order, 0-based. `-1` for a `bk_lam` binder.
    ///
    /// NOT the de-Bruijn index -- pattern binders are pushed left to
    /// right, so the binder at written position `i` of `n` sits at index
    /// `n - 1 - i` inside the body. `collect_case_args` computes both.
    pos : I64 := 0 - 1,
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

pub def BinderUse.ctor (u : BinderUse) : Identifier := u.ctor

pub def BinderUse.pos (u : BinderUse) : I64 := u.pos

pub def BinderUse.owning (u : BinderUse) : I64 := u.owning

pub def BinderUse.borrowed (u : BinderUse) : I64 := u.borrowed

/// `Binder` -> a printable identifier. An unnamed binder reports as
/// `_`, matching how the corpus already spells a binder nobody reads.
def binder_ident (b : Binder) : Identifier :=
    match binder_name b {
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
pub def collect_binder_uses (ctors : HashMap String Bool) (borrows : HashMap String Bool) (t : Term) : List BinderUse :=
    collect_uses_term ctors borrows t List.empty

#[partial]
def collect_uses_term (ctors : HashMap String Bool) (borrows : HashMap String Bool) (t : Term) (acc : List BinderUse) : List BinderUse :=
    match t {
        Term.var _idx _dbg => acc,
        Term.var_macro _idx _dbg => acc,
        Term.lam b typ body =>
            let raw : I64 := uses_of 0 body in
            let u : BinderUse :=
                { name := binder_ident b,
                  kind := BinderKind.bk_lam,
                  typ := typ,
                  count := raw,
                  borrowed := raw - borrow_aware_uses borrows 0 body,
                  owning := owning_uses ctors borrows 0 body,
                  ctor := Identifier.id "",
                  pos := 0 - 1 } in
            collect_uses_term ctors borrows body (List.cons u acc),
        // A non-explicit `pi` (the former `forall`) binds a TYPE variable.
        // It is erased before run time, so it is not a runtime binder and
        // never owns memory -- walk through it for the binders nested
        // inside, but do not report it. An explicit `pi` is entirely a
        // type position (rule 2): any `lam` nested inside a type is
        // likewise compile-time and reports nothing.
        Term.pi b _arg ret =>
            if Bool.not (binder_is_explicit b)
            then collect_uses_term ctors borrows ret acc
            else acc,
        Term.app callee arg => collect_uses_term ctors borrows arg (collect_uses_term ctors borrows callee acc),
        Term.lit value => collect_uses_literal ctors borrows value acc,
        Term.ntv n => collect_uses_native ctors borrows n acc,
        Term.con c => collect_uses_con ctors borrows c acc,
        Term.sort _level => acc,
        Term.hole => acc,
        Term.quote_ _inner => acc,
        Term.ctx _loc inner => collect_uses_term ctors borrows inner acc,
    }

#[partial]
def collect_uses_literal (ctors : HashMap String Bool) (borrows : HashMap String Bool) (l : Literal) (acc : List BinderUse) : List BinderUse :=
    match l {
        Literal.str _v => acc,
        Literal.char _v => acc,
        Literal.num _n _suf => acc,
        Literal.flt _t _suf => acc,
        Literal.if_ cond then_ else_ =>
            collect_uses_term ctors borrows else_ (collect_uses_term ctors borrows then_ (collect_uses_term ctors borrows cond acc)),
        Literal.match_ scrut cases => collect_uses_cases ctors borrows cases (collect_uses_term ctors borrows scrut acc),
        Literal.struct_lit fields _type_name => collect_uses_fields ctors borrows fields acc,
        Literal.struct_update base fields => collect_uses_fields ctors borrows fields (collect_uses_term ctors borrows base acc),
    }

#[partial]
def collect_uses_cases (ctors : HashMap String Bool) (borrows : HashMap String Bool) (cases : List MatchCase) (acc : List BinderUse) : List BinderUse :=
    match cases {
        List.empty => acc,
        List.cons c rest => collect_uses_cases ctors borrows rest (collect_uses_case ctors borrows c acc),
    }

#[partial]
def collect_uses_case (ctors : HashMap String Bool) (borrows : HashMap String Bool) (c : MatchCase) (acc : List BinderUse) : List BinderUse :=
    match c {
        MatchCase.mc name args body _fp =>
            let n : I64 := List.length args in
            let with_args : List BinderUse := collect_case_args ctors borrows name args 0 n body acc in
            collect_uses_term ctors borrows body with_args,
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
def collect_case_args (ctors : HashMap String Bool) (borrows : HashMap String Bool) (ctor : Identifier) (args : List Identifier) (i : I64) (n : I64) (body : Term) (acc : List BinderUse) : List BinderUse :=
    match args {
        List.empty => acc,
        List.cons nm rest =>
            let idx : I64 := n - 1 - i in
            let raw : I64 := uses_of idx body in
            let u : BinderUse :=
                { name := nm,
                  kind := BinderKind.bk_match,
                  typ := Term.hole,
                  count := raw,
                  borrowed := raw - borrow_aware_uses borrows idx body,
                  owning := owning_uses ctors borrows idx body,
                  ctor := ctor,
                  pos := i } in
            collect_case_args ctors borrows ctor rest (i + 1) n body (List.cons u acc),
    }

#[partial]
def collect_uses_fields (ctors : HashMap String Bool) (borrows : HashMap String Bool) (fields : List StructLitField) (acc : List BinderUse) : List BinderUse :=
    match fields {
        List.empty => acc,
        List.cons f rest =>
            match f {
                StructLitField.mk _name value => collect_uses_fields ctors borrows rest (collect_uses_term ctors borrows value acc),
            },
    }

#[partial]
def collect_uses_con (ctors : HashMap String Bool) (borrows : HashMap String Bool) (c : Con) (acc : List BinderUse) : List BinderUse :=
    match c {
        Con.mk _name _typ_name _num_args args => collect_uses_opt_args ctors borrows args acc,
    }

#[partial]
def collect_uses_native (ctors : HashMap String Bool) (borrows : HashMap String Bool) (n : Native) (acc : List BinderUse) : List BinderUse :=
    match n {
        Native.mk _native_name _num_args args => collect_uses_opt_args ctors borrows args acc,
    }

#[partial]
def collect_uses_opt_args (ctors : HashMap String Bool) (borrows : HashMap String Bool) (args : List (Option Term)) (acc : List BinderUse) : List BinderUse :=
    match args {
        List.empty => acc,
        List.cons a rest =>
            match a {
                Option.some t => collect_uses_opt_args ctors borrows rest (collect_uses_term ctors borrows t acc),
                Option.none => collect_uses_opt_args ctors borrows rest acc,
            },
    }

// ─── Type attribution for match-arm binders ────────────────────────
//
// `collect_binder_uses` is a pure function of the term, so a match-arm
// binder comes back with `typ = Term.hole`: its type lives on the
// matched constructor, and reaching that needs a `Scope`. This layer is
// the scope-taking refinement, kept separate so the counter itself stays
// pure and testable without one.
//
// It matters more than it looks. On the compiler's own closure, 723 of
// the 2,419 over-used binders reported as unknown -- 30% of the number
// the whole experiment turns on, unattributed.

/// Fill in `typ` for every `bk_match` binder whose constructor resolves
/// unambiguously. Leaves the rest at `Term.hole`.
#[partial]
pub def attribute_binder_types (s : Scope) (us : List BinderUse) : List BinderUse :=
    List.reverse (attribute_binder_types_go s us List.empty)

#[partial]
def attribute_binder_types_go (s : Scope) (us : List BinderUse) (acc : List BinderUse) : List BinderUse :=
    match us {
        List.empty => acc,
        List.cons u rest => attribute_binder_types_go s rest (List.cons (attribute_one s u) acc),
    }

/// One binder. A `bk_lam` binder already carries its annotation, and a
/// `bk_match` binder is resolved through its constructor -- or left
/// unknown, which is the honest answer whenever it cannot be.
def attribute_one (s : Scope) (u : BinderUse) : BinderUse :=
    match BinderUse.kind u {
        BinderKind.bk_lam => u,
        BinderKind.bk_match =>
            match ctor_field_type s (BinderUse.ctor u) (BinderUse.pos u) {
                Option.some t => { u with typ := t },
                Option.none => u,
            },
    }

/// The declared type of a constructor's `pos`-th field, when exactly one
/// inductive in scope declares that constructor.
///
/// **Exactly one, deliberately.** There is no by-constructor index, only
/// a scan, and a `struct`'s auto-generated constructor is always named
/// `mk` (`build_scope_struct`, `lang/scope.mo`) -- so `mk` matches every
/// struct in the whole loaded corpus. `scope_find_inductive_by_
/// constructor` would hand back whichever hash-bucket order found first,
/// which for `mk` is arbitrary, and scope.mo's own doc comment records
/// that exact ambiguity silently returning the WRONG field elsewhere.
/// Reporting `?` for an ambiguous constructor is a smaller lie than
/// reporting a confident wrong type name, and it keeps the measurement's
/// error in the one direction that cannot flatter the design.
///
/// The resolved type is the constructor's DECLARED field type, so a
/// generic constructor's field comes back as its uninstantiated type
/// parameter (`A`, not `ParseError`) -- instantiating it needs the
/// scrutinee's type, which is inference, not lookup. For a report that
/// groups by type head name that is the right trade: `A` is an honest
/// answer, and the compiler's own constructors are overwhelmingly
/// monomorphic.
def ctor_field_type (s : Scope) (ctor : Identifier) (pos : I64) : Option Term :=
    if I64.lt pos 0 then Option.none
    else
        let con_mp : NamePath := NamePath.npath (List.cons ctor List.empty) in
        match scope_find_all_inductives_by_constructor con_mp s {
            List.empty => Option.none,
            List.cons ind rest =>
                match rest {
                    // Two or more inductives declare it -- see above.
                    List.cons _ _ => Option.none,
                    List.empty =>
                        match find_constructor_in_inductive ind con_mp {
                            Option.none => Option.none,
                            Option.some c =>
                                match c {
                                    InductConstructor.mk _name params _typ => nth_param_type params pos,
                                },
                        },
                },
        }

/// The `n`-th parameter's declared type. `Option.none` when the pattern
/// binds more names than the constructor declares fields -- which the
/// checker rejects, but this walk runs over elaborated terms and should
/// not assume it never sees one.
#[partial]
def nth_param_type (params : List Param) (n : I64) : Option Term :=
    match params {
        List.empty => Option.none,
        List.cons p rest =>
            if I64.beq n 0 then
                match p {
                    Param.mk _name type_ _mult _default _attrs => Option.some type_,
                }
            else nth_param_type rest (n - 1),
    }

// ─── Tests ─────────────────────────────────────────────────────────
//
// Every rule in this file's doc comment has a test below, because every
// one of them is a way to produce a plausible-looking wrong number.

def dbg_x : DebugName := DebugName.named (Identifier.id "x")

/// The `Binder` the tests build `Term.lam`s out of. Pre-R2b `Term.lam`
/// took the `DebugName` directly; now it takes a `Binder`.
def b_x : Binder := binder_explicit dbg_x

/// The constructor set the tests below resolve against: just `P`, the
/// one constructor they build terms out of. Real runs get this from
/// `ctor_name_set`.
def probe_ctors : HashMap String Bool := str_map_insert "P" true str_map_empty

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
    let t : Term := Term.lam binder_anon Term.hole (Term.var 1 dbg_x) in
    I64.beq (uses_of 0 t) 1

#[test]
def test_uses_of_ignores_lambda_annotation : Bool :=
    // The annotation mentions the binder, the body does not. A type
    // position consumes nothing. Rule 2.
    let t : Term := Term.lam binder_anon t_var0 Term.hole in
    I64.beq (uses_of 0 t) 0

#[test]
def test_uses_of_ignores_pi_entirely : Bool :=
    // A function type is compile-time on both sides. Rule 2.
    let t : Term := Term.pi binder_anon t_var0 t_var0 in
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
    let c : Con := Con.mk (Identifier.id "P") (NamePath.npath (List.cons (Identifier.id "P") List.empty)) 2 args in
    I64.beq (uses_of 0 (Term.con c)) 2

#[test]
def test_uses_of_skips_unsaturated_constructor_slots : Bool :=
    let args : List (Option Term) :=
        List.cons (Option.some t_var0) (List.cons Option.none List.empty) in
    let c : Con := Con.mk (Identifier.id "P") (NamePath.npath (List.cons (Identifier.id "P") List.empty)) 2 args in
    I64.beq (uses_of 0 (Term.con c)) 1

#[test]
def test_collect_reports_one_binder_per_lambda : Bool :=
    // `fn x => fn y => var 0` -- two binders. The inner one is used
    // once; the outer one is never used, which is exactly the shape
    // affine-by-default must free automatically.
    let inner : Term := Term.lam b_x Term.hole (Term.var 0 dbg_x) in
    let t : Term := Term.lam b_x Term.hole inner in
    I64.beq (List.length (collect_binder_uses probe_ctors str_map_empty t)) 2

#[test]
def test_collect_records_an_unused_binder_as_zero : Bool :=
    // `fn x => <hole>` -- one binder, zero uses. Affine-legal (weakening
    // is admissible), and a release point under Milestone 3.
    let t : Term := Term.lam b_x Term.hole Term.hole in
    match collect_binder_uses probe_ctors str_map_empty t {
        List.cons u _rest => I64.beq (BinderUse.count u) 0,
        List.empty => false,
    }

#[test]
def test_collect_records_an_overused_binder : Bool :=
    // `fn x => x x` -- two uses. This is the shape that needs `Copy`.
    let body : Term := Term.app (Term.var 0 dbg_x) (Term.var 0 dbg_x) in
    let t : Term := Term.lam b_x Term.hole body in
    match collect_binder_uses probe_ctors str_map_empty t {
        List.cons u _rest => I64.beq (BinderUse.count u) 2,
        List.empty => false,
    }

#[test]
def test_collect_skips_implicit_pi_binders : Bool :=
    // An implicit-binder `pi` (the former `forall`) binds a type
    // variable: erased, never a runtime owner. The `lam` nested under it
    // is still reported.
    let inner : Term := Term.lam b_x Term.hole Term.hole in
    let t : Term := Term.pi (binder_binder (Identifier.id "x")) (Term.sort (SortLevel.concrete 0)) inner in
    I64.beq (List.length (collect_binder_uses probe_ctors str_map_empty t)) 1

// ─── Tests: type attribution ───────────────────────────────────────

def empty_scope : Scope :=
    { module_id := ModulePath.mp (List.cons (Identifier.id "probe") List.empty),
      scope := scope_data_empty,
      parent := Option.none,
      incomplete_match_ok := false }

def probe_param (name : String) (ty : String) : Param :=
    let ty_term : Term := Term.var (0 - 1) (DebugName.named (Identifier.id ty)) in
    Param.mk (Identifier.id name) ty_term Multiplicity.many Option.none List.empty

#[test]
def test_nth_param_type_picks_the_right_slot : Bool :=
    let ps : List Param :=
        List.cons (probe_param "a" "I64") (List.cons (probe_param "b" "String") List.empty) in
    match nth_param_type ps 1 {
        Option.some t =>
            match t {
                Term.var _idx dbg =>
                    match dbg {
                        DebugName.named id => Similar.similar id (Identifier.id "String"),
                        DebugName.unnamed => false,
                    },
                _ => false,
            },
        Option.none => false,
    }

#[test]
def test_nth_param_type_runs_off_the_end : Bool :=
    // A pattern binding more names than the constructor declares. The
    // checker rejects it, but this walk must not assume that.
    match nth_param_type (List.cons (probe_param "a" "I64") List.empty) 3 {
        Option.some _t => false,
        Option.none => true,
    }

#[test]
def test_attribute_leaves_lambda_binders_alone : Bool :=
    // A `bk_lam` binder already carries its annotation; attribution must
    // not overwrite it with a constructor lookup that was never asked
    // for.
    let annotated : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "I64")) in
    let u : BinderUse :=
        { name := Identifier.id "x", kind := BinderKind.bk_lam, typ := annotated,
          count := 1, owning := 1, ctor := Identifier.id "", pos := 0 - 1 } in
    match attribute_binder_types empty_scope (List.cons u List.empty) {
        List.cons out _rest =>
            match BinderUse.typ out {
                Term.var _idx dbg =>
                    match dbg {
                        DebugName.named id => Similar.similar id (Identifier.id "I64"),
                        DebugName.unnamed => false,
                    },
                _ => false,
            },
        List.empty => false,
    }

#[test]
def test_attribute_fails_closed_on_an_unknown_constructor : Bool :=
    // Nothing in scope declares `nope`, so the binder stays unknown
    // rather than acquiring a confident wrong type.
    let u : BinderUse :=
        { name := Identifier.id "f", kind := BinderKind.bk_match, typ := Term.hole,
          count := 2, owning := 2, ctor := Identifier.id "nope", pos := 0 } in
    match attribute_binder_types empty_scope (List.cons u List.empty) {
        List.cons out _rest =>
            match BinderUse.typ out {
                Term.hole => true,
                _ => false,
            },
        List.empty => false,
    }

#[test]
def test_collect_records_the_constructor_and_position : Bool :=
    // The two fields attribution runs on. Position is written order,
    // NOT the de-Bruijn index -- `b` is written second and sits at
    // index 0.
    let no_fp : Option FieldPattern := Option.none in
    let args : List Identifier :=
        List.cons (Identifier.id "a") (List.cons (Identifier.id "b") List.empty) in
    let arm : MatchCase := MatchCase.mc (Identifier.id "pair") args (Term.var 0 dbg_x) no_fp in
    let arms : List MatchCase := List.cons arm List.empty in
    let t : Term := Term.lit (Literal.match_ Term.hole arms) in
    match collect_binder_uses probe_ctors str_map_empty t {
        List.cons u _rest =>
            // The accumulator reverses, so `b` (written position 1)
            // comes back first, and it is the one the body uses.
            Similar.similar (BinderUse.ctor u) (Identifier.id "pair")
                && I64.beq (BinderUse.pos u) 1
                && I64.beq (BinderUse.count u) 1,
        List.empty => false,
    }

// ─── Tests: owning vs borrowing uses ───────────────────────────────

/// A constructor term with `n` slots filled by `t_var0`, for testing
/// that an owning store is recognised as one.
def con_of (args : List (Option Term)) : Term :=
    let nm : NamePath := NamePath.npath (List.cons (Identifier.id "P") List.empty) in
    Term.con (Con.mk (Identifier.id "P") nm 2 args)

#[test]
def test_owning_a_bare_body_is_a_move : Bool :=
    // The value a scope produces is moved out. One owning use.
    I64.beq (owning_uses probe_ctors str_map_empty 0 t_var0) 1

#[test]
def test_owning_ignores_a_call_argument : Bool :=
    // `f x` with `f` free -- passing to a function is a read, which a
    // borrow could serve. The head is a free var (idx sentinel), not
    // the target.
    let f : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "f")) in
    I64.beq (owning_uses probe_ctors str_map_empty 0 (Term.app f t_var0)) 0

#[test]
def test_owning_ignores_a_match_scrutinee : Bool :=
    // Matching inspects a value; it does not consume it.
    let no_fp : Option FieldPattern := Option.none in
    let arm : MatchCase := MatchCase.mc (Identifier.id "a") List.empty Term.hole no_fp in
    let t : Term := Term.lit (Literal.match_ t_var0 (List.cons arm List.empty)) in
    I64.beq (owning_uses probe_ctors str_map_empty 0 t) 0

#[test]
def test_owning_counts_a_constructor_field : Bool :=
    // Stored into a constructor: the value outlives the expression.
    let args : List (Option Term) := List.cons (Option.some t_var0) List.empty in
    I64.beq (owning_uses probe_ctors str_map_empty 0 (con_of args)) 1

#[test]
def test_owning_counts_both_constructor_fields : Bool :=
    // The same value stored twice. THIS is what genuinely needs
    // duplication -- no borrow discipline rescues it.
    let args : List (Option Term) :=
        List.cons (Option.some t_var0) (List.cons (Option.some t_var0) List.empty) in
    I64.beq (owning_uses probe_ctors str_map_empty 0 (con_of args)) 2

#[test]
def test_owning_counts_a_curried_constructor_argument : Bool :=
    // `P x` written as an application, not as saturated `Con.args`.
    // Multi-arg constructors are CURRIED, so this is the shape most
    // constructor stores actually arrive in -- misreading it as a call
    // argument would count an owning store as a free read.
    let empty_args : List (Option Term) := List.empty in
    let head : Term := con_of empty_args in
    I64.beq (owning_uses probe_ctors str_map_empty 0 (Term.app head t_var0)) 1

/// `probe_ctors` plus `"of"`, registered as a REAL constructor -- the
/// shape the borrow tests need to prove the override actually wins
/// over `head_is_ctor`, not just that `of` was never classified as a
/// constructor to begin with.
def probe_ctors_with_of : HashMap String Bool :=
    str_map_insert "of" true probe_ctors

/// What `borrow_of_name_set` would compute for a scope where `Borrow`
/// really is the only inductive declaring `of` -- built by hand here so
/// the owning-count tests below don't need a real `Scope` walk just to
/// exercise `head_is_borrow_of`'s consumer side.
def probe_borrows_of : HashMap String Bool :=
    str_map_insert "of" true (str_map_insert "Borrow.of" true str_map_empty)

/// A `Scope` with a real `Borrow` inductive (one constructor, `of`)
/// registered, for testing `borrow_of_name_set` itself end-to-end.
def scope_with_borrow : Scope :=
    let con : InductConstructor :=
        InductConstructor.mk (NamePath.npath (List.cons (Identifier.id "of") List.empty))
            List.empty Term.hole in
    let ind : Inductive :=
        Inductive.mk (NamePath.npath (List.cons (Identifier.id "Borrow") List.empty))
            List.empty Term.hole (List.cons con List.empty) List.empty Visibility.package_private in
    let sd0 : ScopeData := scope_globals empty_scope in
    { empty_scope with scope := { sd0 with inductives := str_map_insert "Borrow" ind sd0.inductives } }

/// `Borrow.of <arg>`, spelled bare `of` -- the same spelling
/// `head_is_borrow_of` checks first.
def of_of (arg : Term) : Term :=
    let head : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "of")) in
    Term.app head arg

#[test]
def test_borrow_of_name_set_resolves_the_real_borrow_type : Bool :=
    // `borrow_of_name_set` walks a real `Scope` and finds the ONE
    // inductive actually named `Borrow` -- both spellings its own
    // constructor could be written with come back registered.
    let s : HashMap String Bool := borrow_of_name_set scope_with_borrow in
    name_is_ctor s "of" && name_is_ctor s "Borrow.of"

#[test]
def test_borrow_of_name_set_is_empty_with_no_borrow_type_in_scope : Bool :=
    // Nothing named `Borrow` is in scope, so nothing is a borrow --
    // fail closed, the same direction every other ambiguity in this
    // module fails.
    let s : HashMap String Bool := borrow_of_name_set empty_scope in
    not (name_is_ctor s "of")

#[test]
def test_owning_a_borrow_construction_is_a_read_not_a_store : Bool :=
    // `Borrow.of x` must NOT count as an owning use, even though `of`
    // is registered as a real constructor -- the whole point is that
    // the borrow override wins over "any constructor head is a store".
    I64.beq (owning_uses probe_ctors_with_of probe_borrows_of 0 (of_of t_var0)) 0

#[test]
def test_owning_a_value_borrowed_twice_is_still_free : Bool :=
    // `f (Borrow.of x); g (Borrow.of x)` -- x used twice, ZERO owning
    // uses either time. This is the property B1 exists to buy: a
    // borrowed value may be read any number of times without becoming
    // a duplication cost. Reuses `con_of` purely as a wrapper that
    // visits two independent subterms in owning field positions --
    // each subterm's OWN `Term.app` case still computes its `arg_pos`
    // fresh, ignoring the outer context, so this exercises exactly the
    // same code path `test_owning_counts_both_constructor_fields`
    // does, with `of_of t_var0` in place of a bare `t_var0`.
    let args : List (Option Term) :=
        List.cons (Option.some (of_of t_var0)) (List.cons (Option.some (of_of t_var0)) List.empty) in
    I64.beq (owning_uses probe_ctors_with_of probe_borrows_of 0 (con_of args)) 0

#[test]
def test_owning_an_unrelated_types_of_is_not_misclassified_as_borrow : Bool :=
    // The false positive `head_is_borrow_of` used to have: some OTHER
    // type also declares a bare `of` constructor (registered in `ctors`
    // exactly like `Borrow.of` would be), but `Borrow` itself is not in
    // scope here (`borrows` is empty). This must count as an ordinary
    // owning constructor store, not a free borrow read.
    I64.beq (owning_uses probe_ctors_with_of str_map_empty 0 (of_of t_var0)) 1

/// `Path.of x` — a dotted `of` that is NOT Borrow's, as a DEF on
/// another type (`std/path.mo`), so `borrow_of_name_set`'s sole-`of`
/// guard cannot see it. Found for real in `cli/src/main.mo` (4 sites)
/// by the Phase 3 corpus sweep: the last-dotted-segment fallback
/// stripped `Path.of` to `of` and excused 4 real uses as borrow reads.
def path_of_of (arg : Term) : Term :=
    let head : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "Path.of")) in
    Term.app head arg

#[test]
def test_a_dotted_of_from_another_type_is_not_a_borrow : Bool :=
    // The fail-open hole `name_is_borrow` closes: a dotted spelling the
    // borrow set does not hold VERBATIM is not a borrow, even though
    // its last dotted segment is `of`. `Path.of x` must count x.
    name_is_borrow probe_borrows_of "of"
        && name_is_borrow probe_borrows_of "Borrow.of"
        && not (name_is_borrow probe_borrows_of "Path.of")
        && I64.beq (borrow_aware_uses probe_borrows_of 0 (path_of_of t_var0)) 1
        // Positive control in the same breath: the REAL bare spelling
        // still excuses the use, so this test fails if the exact match
        // ever over-corrects into missing genuine borrows.
        && I64.beq (borrow_aware_uses probe_borrows_of 0 (of_of t_var0)) 0

/// `Borrow.of <arg>` spelled type-qualified, the form a real dotted
/// reference carries in an elaborated term — the spelling the ctor set
/// must hold for `name_is_ctor`'s exact match to keep finding it.
def borrow_of_dotted (arg : Term) : Term :=
    let head : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "Borrow.of")) in
    Term.app head arg

#[test]
def test_a_dotted_of_from_another_type_is_not_a_ctor : Bool :=
    // `name_is_ctor`'s own fail-open hole, closed the same way as the
    // borrow one above: `Path.of` is a def on another type, so it must
    // not inherit `Borrow`'s bare `of` — or a binder read once and
    // handed to `Path.of` once reports `value_used_after_move`, the one
    // diagnostic that says no borrow can fix it, when a borrow is
    // exactly the fix.
    //
    // The set is built by the REAL `ctor_name_set` over a scope with a
    // `Borrow` inductive, so the two positive assertions also pin the
    // registration this fix relies on: bare `of` and type-qualified
    // `Borrow.of` both present, `Path.of` absent.
    let s : HashMap String Bool := ctor_name_set scope_with_borrow in
    name_is_ctor s "of"
        && name_is_ctor s "Borrow.of"
        && not (name_is_ctor s "Path.of")
        // End to end through the owning walk: `Path.of`'s argument is an
        // ordinary call argument, not a constructor store.
        && I64.beq (owning_uses s probe_borrows_of 0 (path_of_of t_var0)) 0
        // Positive control: a REGISTERED dotted spelling still counts as
        // a store, so exact matching has not over-corrected into missing
        // the type-qualified references the registration exists for.
        && I64.beq (owning_uses s str_map_empty 0 (borrow_of_dotted t_var0)) 1

#[test]
def test_owning_takes_max_across_branches : Bool :=
    // Moved out on both arms, but only one arm runs. One owning use,
    // so this is still affine-legal.
    let t : Term := Term.lit (Literal.if_ Term.hole t_var0 t_var0) in
    I64.beq (owning_uses probe_ctors str_map_empty 0 t) 1

#[test]
def test_owning_separates_the_read_from_the_move : Bool :=
    // `if x then x else <hole>` -- read as the condition, moved out on
    // one arm. One owning use: borrowable, one move. The distinction
    // the whole section exists to draw.
    let t : Term := Term.lit (Literal.if_ t_var0 t_var0 Term.hole) in
    I64.beq (uses_of 0 t) 2 && I64.beq (owning_uses probe_ctors str_map_empty 0 t) 1

#[test]
def test_collect_records_owning_uses : Bool :=
    // `fn x => P x x` -- used twice, and both are owning stores.
    let empty_args : List (Option Term) := List.empty in
    let head : Term := con_of empty_args in
    let body : Term := Term.app (Term.app head (Term.var 0 dbg_x)) (Term.var 0 dbg_x) in
    let t : Term := Term.lam b_x Term.hole body in
    match collect_binder_uses probe_ctors str_map_empty t {
        List.cons u _rest => I64.beq (BinderUse.count u) 2 && I64.beq (BinderUse.owning u) 2,
        List.empty => false,
    }

// ─── Tests: borrow-aware use counting ──────────────────────────────

#[test]
def test_borrow_aware_uses_excuses_a_direct_borrow : Bool :=
    // `Borrow.of x` -- uses_of says 1, but the use is free.
    I64.beq (borrow_aware_uses probe_borrows_of 0 (of_of t_var0)) 0
        && I64.beq (uses_of 0 (of_of t_var0)) 1

#[test]
def test_borrow_aware_uses_counts_a_use_nested_in_a_borrow : Bool :=
    // `Borrow.of (f x)` -- x is consumed to BUILD the borrowed value,
    // so it still counts. Excusing it would hide a real double-use.
    let f : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "f")) in
    I64.beq (borrow_aware_uses probe_borrows_of 0 (of_of (Term.app f t_var0))) 1

#[test]
def test_borrow_aware_uses_counts_without_a_borrow_type : Bool :=
    // No `Borrow` in scope, so a bare `of` head is an ordinary
    // constructor call and the argument is a real use. Fail closed.
    I64.beq (borrow_aware_uses str_map_empty 0 (of_of t_var0)) 1

#[test]
def test_the_branch_result_of_a_borrow_is_borrowed : Bool :=
    // `Borrow.of (if c then x else x)` -- whichever arm runs IS the
    // value being borrowed.
    let inner : Term := Term.lit (Literal.if_ Term.hole t_var0 t_var0) in
    I64.beq (borrow_aware_uses probe_borrows_of 0 (of_of inner)) 0

#[test]
def test_collect_records_borrowed_uses : Bool :=
    // `f (Borrow.of x); g (Borrow.of x)` -- two uses, both borrows:
    // count 2, borrowed 2, budget zero. The number the affine gate
    // actually compares against.
    let args : List (Option Term) :=
        List.cons (Option.some (of_of t_var0)) (List.cons (Option.some (of_of t_var0)) List.empty) in
    let t : Term := Term.lam b_x Term.hole (con_of args) in
    match collect_binder_uses probe_ctors_with_of probe_borrows_of t {
        List.cons u _rest =>
            I64.beq (BinderUse.count u) 2
                && I64.beq (BinderUse.borrowed u) 2
                && I64.beq (BinderUse.owning u) 0,
        List.empty => false,
    }

#[test]
def test_collect_separates_a_borrow_from_a_real_use : Bool :=
    // `f (Borrow.of x); P x` -- one borrow, one owning store. Borrowed
    // 1 of 2 uses; budget 1, which is affine-legal.
    let args : List (Option Term) :=
        List.cons (Option.some (of_of t_var0)) (List.cons (Option.some t_var0) List.empty) in
    let t : Term := Term.lam b_x Term.hole (con_of args) in
    match collect_binder_uses probe_ctors_with_of probe_borrows_of t {
        List.cons u _rest =>
            I64.beq (BinderUse.count u) 2
                && I64.beq (BinderUse.borrowed u) 1
                && I64.beq (BinderUse.owning u) 1,
        List.empty => false,
    }

#[test]
def test_borrowed_is_branch_consistent : Bool :=
    // One arm over-uses `x` for real (`x x`), the other only borrows
    // it. The borrowed count must NOT offset the over-using arm:
    // budget is max(2, 1-1) = 2, not max(2,1) - max(0,1) = 1. This is
    // the difference-between-walks design earning its keep -- a
    // separately per-branch-maxed borrowed count would let this
    // binder through the affine gate.
    let over : Term := Term.app (Term.var 0 dbg_x) (Term.var 0 dbg_x) in
    let branches : Term := Term.lit (Literal.if_ Term.hole over (of_of t_var0)) in
    let t : Term := Term.lam b_x Term.hole branches in
    match collect_binder_uses probe_ctors_with_of probe_borrows_of t {
        List.cons u _rest =>
            I64.beq (BinderUse.count u) 2 && I64.beq (BinderUse.borrowed u) 0,
        List.empty => false,
    }
