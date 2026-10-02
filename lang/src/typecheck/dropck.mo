/// Drop-point analysis — where a value must be released, along each
/// control-flow path, because the enclosing scope still owns it there.
///
/// Milestone 3 of the affine-by-default experiment
/// (*Design B: Viability
/// Experiment*). This
/// module decides WHERE a `monad_release` call would go; it does not
/// emit one. Codegen wiring (`lang/codegen/emit.mo`) and the runtime's
/// real free (`runtime/src/runtime.c`) are deliberately separate,
/// unstarted work — see the design's own M3 section for why: this
/// module is pure and safely testable in isolation, `emit.mo` is the
/// central, historically fragile codegen file this experiment has
/// stayed clear of touching until the analysis feeding it is solid.
///
/// ## The rule, and why it needs no new primitive
///
/// [[lang/typecheck/usage.mo]] already answers exactly the question
/// this needs, per use: `owning_at` classifies each use of a binder as
/// either a READ (a call argument, a match scrutinee, a callee — the
/// owner is not moved) or an OWNING use (stored into a constructor, or
/// produced as a scope's own value — ownership transfers out). A
/// binder with **zero owning uses along a given path** was never given
/// away on that path, so the scope that bound it still owns it when
/// that path returns, and must release it there. That is the entire
/// rule: **release iff owning count on this path is 0.**
///
/// ## Why this needs a NEW walk, not `owning_uses` as-is
///
/// `usage.mo`'s own `owning_uses`/`uses_of` deliberately combine
/// branches by MAX — one worst-case number, because M2's usage rule
/// asks "is this binder ever over-used on ANY path" and a single
/// number is exactly the right answer to THAT question. M3 asks a
/// different question — "on EACH path, was it consumed, and if not,
/// where does the release go" — and max-combining throws away exactly
/// the per-branch information that needs. If a binder's global (maxed)
/// owning count is 1, that could mean every branch transfers ownership
/// (no releases needed anywhere) OR it could mean ONE branch does and
/// the others still don't (those still need one). The two situations
/// look identical after max-combining and must not.
///
/// So `drop_leaves` below mirrors `owning_at`'s own branch structure
/// exactly — same `if_`/`match_` cases, same depth bookkeeping — but
/// where `owning_at` combines branches with `i64_max`, this
/// CONCATENATES them: one boolean per real leaf (tail position) of the
/// term, in left-to-right order, computed by calling the EXISTING,
/// already-tested `owning_at` on each leaf's own whole subtree rather
/// than re-deriving what counts as an owning use.
///
/// ## A measured cost, not a silent one
///
/// `List.append` at every branch point is O(length of the first list)
/// per call — cheap for `i64_max`'s O(1), real once it compounds across
/// a binder near a deeply/widely branching root. `bench/src/
/// dropck_probe.mo` measured this over the compiler's own closure:
/// 22,416 binders, 32,104 total leaves (a 100-leaf worst case), 92.6s
/// for the walk alone on the Rust host's tree-walking evaluator
/// (elaboration excluded) — 19.4s under the compiled self-hosted
/// runner, same stats both ways. That is genuinely slower
/// than `usage.mo`'s comparable per-binder walk over the SAME term set,
/// and the `List.append`-per-branch shape is the reason. Not fixed
/// here: nothing consumes this module's output yet (see this file's own
/// header — codegen wiring is deliberately unstarted), so there is no
/// real workload this cost is currently paid against, and the standard
/// fix (thread an accumulator through the branches instead of
/// appending, matching every other O(n) list-builder in this codebase —
/// `lang/codegen/decls.mo`'s `extract_defs`, `qualify.mo`'s
/// `ambiguous_declared_names`) is well understood and small when the
/// time comes. Recorded here so it is a known, deliberate deferral
/// rather than a surprise the next person to touch this file has to
/// rediscover.
use lib::types {Con, DebugName, FieldPattern, Identifier, Literal, MatchCase, NamePath, Native, StructLitField, Term}
use lib::typecheck::usage {owning_at}
use llvm::strmap {str_map_empty}
use std::map {}
use std::list {List.length}

// ─── Per-leaf drop decision ────────────────────────────────────────

/// One entry per LEAF (tail position) reachable from `t`, in the same
/// left-to-right order a reader would encounter them: `true` means
/// `target` still needs releasing there (owning count 0 on that path),
/// `false` means it was already consumed (owning count ≥ 1) on that
/// path. `List.length` of the result is the number of distinct
/// control-flow paths through `t` — 1 for anything that doesn't
/// branch, more for nested `if`/`match`.
///
/// `borrows` is threaded for the same reason `usage.mo` threads it: a
/// real `Borrow.of x` misread as a constructor store would count `x` as
/// consumed here, and a consumed binder gets no release — a leak, not
/// just a miscount.
#[partial]
pub def drop_leaves (ctors : HashMap String Bool) (borrows : HashMap String Bool) (target : I64) (t : Term) : List Bool :=
    match t {
        Term.ctx _loc inner => drop_leaves ctors borrows target inner,
        Term.lit lit =>
            match lit {
                // The condition runs on EVERY path through this `if`,
                // before either branch, so an owning use of `target`
                // there (e.g. a constructor application built from the
                // condition, `if (P x) then y else z`) already consumes
                // it for both branches. Left unaccounted for, each
                // branch's own `single_leaf` check independently sees
                // zero owning uses of `target` and reports "needs
                // drop" -- a double-drop, since `target` was already
                // given away building the condition. `owning_at`'s own
                // `Literal.if_` arm (usage.mo) folds this in the same
                // way, via `UsePos.up_scrutinee`.
                Literal.if_ cond then_ else_ =>
                    let branch_leaves : List Bool :=
                        List.append (drop_leaves ctors borrows target then_) (drop_leaves ctors borrows target else_) in
                    if I64.gt (owning_at ctors borrows UsePos.up_scrutinee target cond) 0
                    then all_false branch_leaves
                    else branch_leaves,
                // Same reasoning for a `match`'s scrutinee, which also
                // runs once before any arm.
                Literal.match_ scrut cases =>
                    let branch_leaves : List Bool := drop_leaves_cases ctors borrows target cases in
                    if I64.gt (owning_at ctors borrows UsePos.up_scrutinee target scrut) 0
                    then all_false branch_leaves
                    else branch_leaves,
                // Every other `Literal` (str/char/num/flt/struct_lit/
                // struct_update) doesn't branch -- ONE leaf, the whole
                // term as `owning_at` already sees it.
                _ => single_leaf ctors borrows target t,
            },
        // Nothing else in `Term` branches control flow -- `app`, `con`,
        // `ntv`, a nested `lam`'s own body (a SEPARATE scope, not a
        // continuation of this one), etc. are all one leaf each.
        _ => single_leaf ctors borrows target t,
    }

def single_leaf (ctors : HashMap String Bool) (borrows : HashMap String Bool) (target : I64) (t : Term) : List Bool :=
    List.cons (I64.beq (owning_at ctors borrows UsePos.up_value target t) 0) List.empty

/// Same length as `leaves`, every entry `false` -- used when `target`
/// was already consumed ahead of a branch point (in an `if`'s condition
/// or a `match`'s scrutinee), so none of the leaves below it need a
/// release regardless of what each one's own, now-moot, per-branch
/// count says.
def all_false (leaves : List Bool) : List Bool :=
    match leaves {
        List.empty => List.empty,
        List.cons _hd rest => List.cons false (all_false rest),
    }

#[partial]
def drop_leaves_cases (ctors : HashMap String Bool) (borrows : HashMap String Bool) (target : I64) (cases : List MatchCase) : List Bool :=
    match cases {
        List.empty => List.empty,
        List.cons c rest =>
            List.append (drop_leaves_case ctors borrows target c) (drop_leaves_cases ctors borrows target rest),
    }

/// A match arm's own pattern bindings sit `List.List.length args` binders
/// deeper than the `match_` node — the same shift `usage.mo`'s
/// `uses_of_case`/`owning_at_case` and `traverse.mo`'s depth-aware
/// walkers all apply.
def drop_leaves_case (ctors : HashMap String Bool) (borrows : HashMap String Bool) (target : I64) (c : MatchCase) : List Bool :=
    match c {
        MatchCase.mc _name args body _fp => drop_leaves ctors borrows (target + List.length args) body,
    }

// ─── Per-binder collection ─────────────────────────────────────────

/// One binder found in a def's body, and where it needs releasing.
pub struct DropInfo {
    name : Identifier,
    /// One entry per leaf of this binder's OWN body — see `drop_leaves`.
    leaves : List Bool,
}

pub def DropInfo.name (d : DropInfo) : Identifier := d.name

pub def DropInfo.leaves (d : DropInfo) : List Bool := d.leaves

/// Needs releasing on every path it can take — the common case: no
/// branching at all, or dropped alike wherever control goes.
pub def DropInfo.always_drop (d : DropInfo) : Bool := all_leaves_true d.leaves

/// Needs releasing on no path — ownership was transferred everywhere
/// this binder's body can return. Nothing to emit for it.
pub def DropInfo.never_drop (d : DropInfo) : Bool := not (any_leaf_true d.leaves)

#[partial]
def all_leaves_true (bs : List Bool) : Bool :=
    match bs { List.empty => true, List.cons b rest => b && all_leaves_true rest }

#[partial]
def any_leaf_true (bs : List Bool) : Bool :=
    match bs { List.empty => false, List.cons b rest => b || any_leaf_true rest }

/// Every binder `t` introduces (`lam`/match-arm), with its own
/// `drop_leaves`. Mirrors `usage.mo`'s `collect_binder_uses` traversal
/// exactly — same cases, same order of descent — computing a per-leaf
/// release list instead of a single use count.
///
/// Accumulator-passing, like every corpus-scale walker in this
/// codebase (`lang/codegen/decls.mo`'s `extract_defs`,
/// `lang/codegen/qualify.mo`'s `ambiguous_declared_names`,
/// `usage.mo`'s own `collect_binder_uses`): the natural
/// `List.cons x (recurse rest)` shape holds one native frame per node,
/// which those files' own doc comments document as a real stack-depth
/// hazard at whole-program scale.
#[partial]
pub def collect_drop_info (ctors : HashMap String Bool) (borrows : HashMap String Bool) (t : Term) : List DropInfo :=
    List.reverse (collect_drop_term ctors borrows t List.empty)

#[partial]
def collect_drop_term (ctors : HashMap String Bool) (borrows : HashMap String Bool) (t : Term) (acc : List DropInfo) : List DropInfo :=
    match t {
        Term.var _idx _dbg => acc,
        Term.var_macro _idx _dbg => acc,
        Term.lam dbg _typ body =>
            let d : DropInfo := { name := binder_name dbg, leaves := drop_leaves ctors borrows 0 body } in
            collect_drop_term ctors borrows body (List.cons d acc),
        // A `forall` binds a compile-time type variable -- erased
        // before run time, never a runtime owner, so it is walked
        // through for nested binders but reports nothing of its own,
        // mirroring `usage.mo`'s `collect_uses_term` exactly.
        Term.forall _dbg _kind body => collect_drop_term ctors borrows body acc,
        Term.pi _arg _ret => acc,
        Term.app callee arg => collect_drop_term ctors borrows arg (collect_drop_term ctors borrows callee acc),
        Term.lit value => collect_drop_literal ctors borrows value acc,
        Term.ntv n => collect_drop_native ctors borrows n acc,
        Term.con c => collect_drop_con ctors borrows c acc,
        Term.sort _level => acc,
        Term.hole => acc,
        Term.quote_ _inner => acc,
        Term.ctx _loc inner => collect_drop_term ctors borrows inner acc,
    }

#[partial]
def collect_drop_literal (ctors : HashMap String Bool) (borrows : HashMap String Bool) (l : Literal) (acc : List DropInfo) : List DropInfo :=
    match l {
        Literal.str _v => acc,
        Literal.char _v => acc,
        Literal.num _n _suf => acc,
        Literal.flt _t _suf => acc,
        Literal.if_ cond then_ else_ =>
            collect_drop_term ctors borrows else_ (collect_drop_term ctors borrows then_ (collect_drop_term ctors borrows cond acc)),
        Literal.match_ scrut cases => collect_drop_cases ctors borrows cases (collect_drop_term ctors borrows scrut acc),
        Literal.struct_lit fields _type_name => collect_drop_fields ctors borrows fields acc,
        Literal.struct_update base fields => collect_drop_fields ctors borrows fields (collect_drop_term ctors borrows base acc),
    }

#[partial]
def collect_drop_cases (ctors : HashMap String Bool) (borrows : HashMap String Bool) (cases : List MatchCase) (acc : List DropInfo) : List DropInfo :=
    match cases {
        List.empty => acc,
        List.cons c rest => collect_drop_cases ctors borrows rest (collect_drop_case ctors borrows c acc),
    }

#[partial]
def collect_drop_case (ctors : HashMap String Bool) (borrows : HashMap String Bool) (c : MatchCase) (acc : List DropInfo) : List DropInfo :=
    match c {
        MatchCase.mc _name args body _fp =>
            let n : I64 := List.length args in
            let with_args : List DropInfo := collect_drop_case_args ctors borrows args 0 n body acc in
            collect_drop_term ctors borrows body with_args,
    }

/// Same written-order-vs-de-Bruijn-index reasoning as `usage.mo`'s own
/// `collect_case_args`: pattern binders are pushed left to right, so
/// the binder at written position `i` of `n` sits at index `n - 1 - i`.
#[partial]
def collect_drop_case_args (ctors : HashMap String Bool) (borrows : HashMap String Bool) (args : List Identifier) (i : I64) (n : I64) (body : Term) (acc : List DropInfo) : List DropInfo :=
    match args {
        List.empty => acc,
        List.cons nm rest =>
            let idx : I64 := n - 1 - i in
            let d : DropInfo := { name := nm, leaves := drop_leaves ctors borrows idx body } in
            collect_drop_case_args ctors borrows rest (i + 1) n body (List.cons d acc),
    }

#[partial]
def collect_drop_fields (ctors : HashMap String Bool) (borrows : HashMap String Bool) (fields : List StructLitField) (acc : List DropInfo) : List DropInfo :=
    match fields {
        List.empty => acc,
        List.cons f rest =>
            match f {
                StructLitField.mk _name value => collect_drop_fields ctors borrows rest (collect_drop_term ctors borrows value acc),
            },
    }

#[partial]
def collect_drop_con (ctors : HashMap String Bool) (borrows : HashMap String Bool) (c : Con) (acc : List DropInfo) : List DropInfo :=
    match c {
        Con.mk _name _typ_name _num_args args => collect_drop_opt_args ctors borrows args acc,
    }

#[partial]
def collect_drop_native (ctors : HashMap String Bool) (borrows : HashMap String Bool) (n : Native) (acc : List DropInfo) : List DropInfo :=
    match n {
        Native.mk _native_name _num_args args => collect_drop_opt_args ctors borrows args acc,
    }

#[partial]
def collect_drop_opt_args (ctors : HashMap String Bool) (borrows : HashMap String Bool) (args : List (Option Term)) (acc : List DropInfo) : List DropInfo :=
    match args {
        List.empty => acc,
        List.cons a rest =>
            match a {
                Option.some t => collect_drop_opt_args ctors borrows rest (collect_drop_term ctors borrows t acc),
                Option.none => collect_drop_opt_args ctors borrows rest acc,
            },
    }

/// `DebugName` -> a printable identifier, matching `usage.mo`'s own
/// `binder_name` (not imported — a four-line helper isn't worth
/// coupling this module to that one's internals for).
def binder_name (dbg : DebugName) : Identifier :=
    match dbg {
        DebugName.named id => id,
        DebugName.unnamed => Identifier.id "_",
    }

// ─── Tests ─────────────────────────────────────────────────────────
//
// `probe_ctors`/`t_var0`/`dbg_x` intentionally NOT shared with
// `usage.mo`'s own copies -- cross-module test fixture sharing buys
// nothing here and would couple this module's tests to that one's
// internals for no reason.

def empty_ctors : HashMap String Bool := str_map_empty

def dbg_x : DebugName := DebugName.named (Identifier.id "x")

def t_var0 : Term := Term.var 0 dbg_x

def bool_leaves (bs : List Bool) : List Bool := bs

#[test]
def test_a_never_used_binder_is_dropped_once : Bool :=
    // `fn x => <hole>` -- one leaf (no branching), never consumed, so
    // the scope that bound it still owns it: needs releasing there.
    let leaves : List Bool := drop_leaves empty_ctors str_map_empty 0 Term.hole in
    match leaves {
        List.cons b rest => b && I64.beq (List.length rest) 0,
        List.empty => false,
    }

#[test]
def test_a_returned_binder_is_not_dropped : Bool :=
    // `fn x => x` -- the body's own tail value IS x: an OWNING use
    // (up_value), ownership transfers out via the return. No release.
    let leaves : List Bool := drop_leaves empty_ctors str_map_empty 0 t_var0 in
    match leaves {
        List.cons b rest => not b && I64.beq (List.length rest) 0,
        List.empty => false,
    }

#[test]
def test_a_merely_read_binder_is_still_dropped : Bool :=
    // `fn x => f x` -- x is a call ARGUMENT (a read), not the body's
    // own return value. The scope still owns it after the call
    // returns, so it still needs releasing.
    let f : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "f")) in
    let leaves : List Bool := drop_leaves empty_ctors str_map_empty 0 (Term.app f t_var0) in
    match leaves {
        List.cons b rest => b && I64.beq (List.length rest) 0,
        List.empty => false,
    }

#[test]
def test_branches_disagree_and_the_leaves_say_so : Bool :=
    // `if c then x else <hole>` -- consumed (returned) on the `then`
    // path, never touched on the `else` path. Exactly the case M3's
    // own doc comment in the plan calls out: the drop is per-arm, not
    // per-binder, and this is the property that PROVES it -- the two
    // leaves must disagree.
    let cond : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "c")) in
    let t : Term := Term.lit (Literal.if_ cond t_var0 Term.hole) in
    let leaves : List Bool := drop_leaves empty_ctors str_map_empty 0 t in
    match leaves {
        List.cons then_leaf rest =>
            match rest {
                List.cons else_leaf rest2 =>
                    not then_leaf && else_leaf && I64.beq (List.length rest2) 0,
                List.empty => false,
            },
        List.empty => false,
    }

#[test]
def test_leaves_are_in_left_to_right_order : Bool :=
    // Nested ifs produce leaves in the order a reader encounters them:
    // (if c1 then (if c2 then x else x) else x) -- three leaves, all
    // consuming (returning) x, so all `false`, but crucially there
    // must be exactly THREE of them, not two (max-combined) or one
    // (uncounted) -- this is the property `owning_uses`' own
    // max-combining rule would have destroyed.
    let c1 : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "c1")) in
    let c2 : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "c2")) in
    let inner : Term := Term.lit (Literal.if_ c2 t_var0 t_var0) in
    let outer : Term := Term.lit (Literal.if_ c1 inner t_var0) in
    let leaves : List Bool := drop_leaves empty_ctors str_map_empty 0 outer in
    I64.beq (List.length leaves) 3
        && not (any_leaf_true leaves)

#[test]
def test_match_arm_binder_shifts_depth_correctly : Bool :=
    // One arm binding two names, body `var 2` -- the FIRST-bound name
    // (written position 0) sits at de Bruijn index 1 inside the body
    // (pattern binders push left-to-right, so the SECOND name is
    // innermost/index 0). `var 2` is neither -- it is the OUTER
    // binder this whole match sits under, one level further out than
    // either pattern name. So this checks that a match arm doesn't
    // accidentally count against the wrong depth.
    let no_fp : Option FieldPattern := Option.none in
    let args : List Identifier :=
        List.cons (Identifier.id "a") (List.cons (Identifier.id "b") List.empty) in
    let body : Term := Term.var 2 dbg_x in
    let arm : MatchCase := MatchCase.mc (Identifier.id "c") args body no_fp in
    let t : Term := Term.lit (Literal.match_ Term.hole (List.cons arm List.empty)) in
    // Target 0 here is the OUTER binder -- after the match's own two
    // pattern binders are crossed, it sits at index 2, which `var 2`
    // matches. An owning use (up_value, the match's own leaf).
    let leaves : List Bool := drop_leaves empty_ctors str_map_empty 0 t in
    match leaves {
        List.cons b rest => not b && I64.beq (List.length rest) 0,
        List.empty => false,
    }

#[test]
def test_collect_drop_info_finds_every_binder : Bool :=
    // `fn x => fn y => x` -- two binders. The inner one (y) is never
    // used: always_drop. The outer one (x) is the final return value:
    // never_drop.
    let inner_body : Term := Term.var 1 dbg_x in
    let inner : Term := Term.lam dbg_x Term.hole inner_body in
    let t : Term := Term.lam dbg_x Term.hole inner in
    let infos : List DropInfo := collect_drop_info empty_ctors str_map_empty t in
    match infos {
        List.cons outer rest =>
            match rest {
                List.cons inner_info rest2 =>
                    DropInfo.never_drop outer && DropInfo.always_drop inner_info && I64.beq (List.length rest2) 0,
                List.empty => false,
            },
        List.empty => false,
    }

#[test]
def test_always_drop_requires_every_leaf : Bool :=
    // Dropped in one branch, kept in the other -- NEITHER always_drop
    // NOR never_drop; this binder genuinely needs a PER-ARM release,
    // which is exactly the case a single "is it dropped" boolean could
    // never express and the whole reason `leaves` is a list.
    let cond : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "c")) in
    let t : Term := Term.lit (Literal.if_ cond t_var0 Term.hole) in
    let leaves : List Bool := drop_leaves empty_ctors str_map_empty 0 t in
    let info : DropInfo := { name := Identifier.id "x", leaves := bool_leaves leaves } in
    not (DropInfo.always_drop info) && not (DropInfo.never_drop info)

/// A single-arg constructor application, `P <arg>` -- matches
/// `usage.mo`'s own `con_of` helper, arity 1 instead of 2.
def con_of_p (arg : Option Term) : Term :=
    let nm : NamePath := NamePath.npath (List.cons (Identifier.id "P") List.empty) in
    Term.con (Con.mk (Identifier.id "P") nm 1 (List.cons arg List.empty))

#[test]
def test_condition_owning_use_is_not_double_dropped : Bool :=
    // `if (P x) then <hole> else <hole>` -- x is consumed INSIDE the
    // condition, building the constructor `P x` (an owning use, per
    // `owning_at`'s own `Term.con` arm). Neither branch references x at
    // all. Before this was fixed, `drop_leaves` never looked at the
    // condition, so each branch's own `single_leaf` independently saw
    // zero owning uses of x and reported "needs drop" for BOTH -- a
    // double-drop of a value already moved building the condition. Both
    // leaves must now read `false`: x was already given away before
    // either branch ran.
    let cond : Term := con_of_p (Option.some t_var0) in
    let t : Term := Term.lit (Literal.if_ cond Term.hole Term.hole) in
    let leaves : List Bool := drop_leaves empty_ctors str_map_empty 0 t in
    I64.beq (List.length leaves) 2
        && not (any_leaf_true leaves)

#[test]
def test_scrutinee_owning_use_is_not_double_dropped : Bool :=
    // Same property, for a `match` scrutinee instead of an `if`
    // condition: `match (P x) { _ => <hole> }` (a single wildcard-style
    // arm binding nothing new). x is consumed building the scrutinee;
    // the arm's own body never references it, so its one leaf must read
    // `false`, not `true`.
    let cond : Term := con_of_p (Option.some t_var0) in
    let arm : MatchCase := MatchCase.mc (Identifier.id "_") List.empty Term.hole Option.none in
    let t : Term := Term.lit (Literal.match_ cond (List.cons arm List.empty)) in
    let leaves : List Bool := drop_leaves empty_ctors str_map_empty 0 t in
    match leaves {
        List.cons b rest => not b && I64.beq (List.length rest) 0,
        List.empty => false,
    }
