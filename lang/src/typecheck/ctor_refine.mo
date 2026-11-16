/// Constructor index inversion for indexed families
/// (`plans/type-system/dependent-elimination-refinement.md`).
///
/// `Inductive.params` mixes uniform parameters and indices: `type Vec (len :
/// Nat) A { nil : Vec Nat.zero A, cons ... : Vec (Nat.succ len) A }` declares
/// `len` as a header binder, but each constructor fixes it in its declared
/// return. A header position is an INDEX when some constructor's declared
/// return argument there is not the bare header binder.
///
/// Matching a constructor against a scrutinee type solves the constructor's
/// index variables from the scrutinee's index (`cons` against `Vec (succ n)
/// A` gives `len := n`), proves it impossible (`nil` against `Vec (succ n)
/// A`: two constructor heads clash), or refines a bound-variable index (`cons`
/// against `Vec m A` with `m` a local: inside the arm, `m` is `succ len@d` for
/// a fresh skolem `len@d`). Anything else is `unknown`, and every caller then
/// keeps its old behaviour: this module only ever adds information.
///
/// Pure: no `infer` import, so `infer` can use it without a cycle.
use lang::types {
    DebugName, Identifier, InductConstructor, Inductive, NamePath, Param, Scope,
    Similar, Term, id_eq, sentinel, term_peel,
}
use lang::scope {CallSpine, flatten_call_spine, scope_find_all_inductives_by_constructor}
use std::list {List.any, List.filter}
use lib::typecheck::name_subst {name_subst_term}
use lib::typecheck::subst {term_shift_above, term_subst}

/// What a constructor's declared indices tell us about one arm.
pub struct IndexSolution {
    /// The constructor's index variables, bound to scrutinee subterms or to
    /// fresh skolems.
    subst : List (Pair Identifier Term),
    /// Bound-variable indices of the scrutinee (outer de Bruijn index) and the
    /// constructor index that replaces each inside the arm.
    refine : List (Pair I64 Term),
    /// The same for an index that is a LOCAL binder written by name (an
    /// implicit `{m : Nat}` appears in a parameter's type as the free name `m`).
    refine_named : List (Pair Identifier Term),
}

pub type IndexMatch {
    solved (s : IndexSolution),
    /// Two constructor heads clash: the arm can never run.
    impossible,
    /// Nothing safe can be concluded.
    unknown,
}

// --- Index positions ---------------------------------------------------------

/// The header positions that some constructor fixes in its declared return.
/// `Vec` -> `[0]`; `Option`, `List`, `Sigma`, `Eq` (whose index is outside the
/// header) -> `[]`, which makes every rule below a no-op for them.
pub def index_positions (ind : Inductive) : List I64 :=
    index_positions_go ind 0 ind.params

#[terminating]
def index_positions_go (ind : Inductive) (i : I64) (params : List Param) : List I64 :=
    match params {
        List.empty => List.empty,
        List.cons p rest =>
            if some_ctor_fixes ind.constructors i p.name
            then List.cons i (index_positions_go ind (i + 1) rest)
            else index_positions_go ind (i + 1) rest,
    }

#[terminating]
def some_ctor_fixes (ctors : List InductConstructor) (i : I64) (header : Identifier) : Bool :=
    match ctors {
        List.empty => false,
        List.cons c rest =>
            match declared_return_args c {
                Option.some args =>
                    match list_nth args i {
                        Option.some a =>
                            if is_named_var header a then some_ctor_fixes rest i header else true,
                        Option.none => some_ctor_fixes rest i header,
                    },
                Option.none => some_ctor_fixes rest i header,
            },
    }

/// The argument spine of a constructor's DECLARED return type, or none for an
/// unannotated constructor (its `typ` is a hole: uniform by construction).
def declared_return_args (c : InductConstructor) : Option (List Term) :=
    match term_peel c.typ {
        Term.hole => Option.none,
        _ => match flatten_call_spine c.typ { CallSpine.mk _head args => Option.some args },
    }

/// This constructor's declared index patterns, one per index position. An
/// unannotated constructor's pattern is the header binder itself.
pub def ctor_index_patterns (ind : Inductive) (c : InductConstructor) (positions : List I64) : List Term :=
    let declared : List Term := match declared_return_args c {
        Option.some args => args,
        Option.none => List.empty,
    } in
    patterns_at ind.params declared positions

#[terminating]
def patterns_at (params : List Param) (declared : List Term) (positions : List I64) : List Term :=
    match positions {
        List.empty => List.empty,
        List.cons i rest =>
            let header : Term := match list_nth params i {
                Option.some p => named_var p.name,
                Option.none => Term.hole,
            } in
            let pat : Term := match list_nth declared i {
                Option.some a => a,
                Option.none => header,
            } in
            List.cons pat (patterns_at params declared rest),
    }

/// The header binders at the index positions: the names a constructor's index
/// pattern and field types may use as its own variables.
pub def index_locals (ind : Inductive) (positions : List I64) : List Identifier :=
    index_locals_go ind.params positions

#[terminating]
def index_locals_go (params : List Param) (positions : List I64) : List Identifier :=
    match positions {
        List.empty => List.empty,
        List.cons i rest =>
            match list_nth params i {
                Option.some p => List.cons p.name (index_locals_go params rest),
                Option.none => index_locals_go params rest,
            },
    }

// --- Matching ---------------------------------------------------------------

/// The matching context: which names are the constructor's index variables,
/// the scope that says which heads are constructors, and the suffix that makes
/// this arm's skolems distinct from any other arm's.
pub struct MatchEnv {
    locals : List Identifier,
    /// The enclosing local binders' names: a free variable spelled with one of
    /// them is a local, not a global, and may be refined by name.
    binders : List Identifier,
    scope : Scope,
    skolem_suffix : String,
}

pub def empty_solution : IndexSolution := { subst := List.empty, refine := List.empty, refine_named := List.empty }

/// Solve `c` against the scrutinee type `sc_typ`. `impossible` wins over
/// `unknown`, which wins over `solved`.
pub def solve_ctor (env : MatchEnv) (ind : Inductive) (c : InductConstructor) (sc_typ : Term) : IndexMatch :=
    let positions : List I64 := index_positions ind in
    let targets : List Term := match flatten_call_spine sc_typ {
        CallSpine.mk _head args => args_at args positions,
    } in
    let patterns : List Term := ctor_index_patterns ind c positions in
    if I64.beq (List.length targets) (List.length positions)
    then match_all env patterns targets (IndexMatch.solved empty_solution)
    else IndexMatch.unknown

#[terminating]
def args_at (args : List Term) (positions : List I64) : List Term :=
    match positions {
        List.empty => List.empty,
        List.cons i rest =>
            match list_nth args i {
                Option.some a => List.cons a (args_at args rest),
                Option.none => args_at args rest,
            },
    }

/// Match pairwise, keeping going after an `unknown` so a later clash still
/// reports `impossible`.
#[terminating]
def match_all (env : MatchEnv) (patterns : List Term) (targets : List Term) (state : IndexMatch) : IndexMatch :=
    match patterns {
        List.empty => state,
        List.cons p prest =>
            match targets {
                List.empty => state,
                List.cons t trest =>
                    match state {
                        IndexMatch.impossible => IndexMatch.impossible,
                        IndexMatch.unknown =>
                            match match_index env p t empty_solution {
                                IndexMatch.impossible => IndexMatch.impossible,
                                _ => match_all env prest trest IndexMatch.unknown,
                            },
                        IndexMatch.solved acc => match_all env prest trest (match_index env p t acc),
                    },
            },
    }

/// One-way structural match of a declared index `pattern` against a scrutinee
/// index `target`. Binds the RAW target subterms (their spelling is the
/// caller's); constructor heads are compared by canonical name only.
#[terminating]
pub def match_index (env : MatchEnv) (pattern : Term) (target : Term) (acc : IndexSolution) : IndexMatch :=
    match local_var_name env.locals pattern {
        Option.some x =>
            match lookup_subst x acc.subst {
                Option.some bound =>
                    if Similar.similar bound target then IndexMatch.solved acc else IndexMatch.unknown,
                Option.none =>
                    let s : IndexSolution := { acc with subst := List.cons (Pair.pair x target) acc.subst } in
                    IndexMatch.solved s,
            },
        Option.none =>
            match ctor_spine env pattern {
                Option.none =>
                    if Similar.similar pattern target && Bool.not (mentions_any env.locals pattern)
                    then IndexMatch.solved acc
                    else IndexMatch.unknown,
                Option.some pspine =>
                    match term_peel target {
                        Term.var k _dbg =>
                            if Bool.not (I64.beq k sentinel) then refine_bound env k pattern acc
                            else match local_var_name env.binders target {
                                Option.some b =>
                                    if is_ctor env.scope b then match_ctor_spines env pspine target acc
                                    else refine_named_local env b pattern acc,
                                Option.none => match_ctor_spines env pspine target acc,
                            },
                        _ => match_ctor_spines env pspine target acc,
                    },
            },
    }

/// A constructor-headed pattern against a target: clash, recurse, or give up.
def match_ctor_spines (env : MatchEnv) (pspine : Pair Identifier (List Term)) (target : Term) (acc : IndexSolution)
    : IndexMatch :=
    match ctor_spine env target {
        Option.none => IndexMatch.unknown,
        Option.some tspine =>
            match pspine {
                Pair.pair pc pargs =>
                    match tspine {
                        Pair.pair tc targs =>
                            if Bool.not (id_eq pc tc) then IndexMatch.impossible
                            else if Bool.not (I64.beq (List.length pargs) (List.length targs)) then IndexMatch.unknown
                            else match_all env pargs targs (IndexMatch.solved acc),
                    },
            },
    }

/// A bound-variable target meets a constructor pattern: inside the arm the
/// variable IS the pattern, with each still-unbound index variable replaced by
/// a fresh skolem (the same name-keyed free-variable representation params
/// already use, so no hidden binder shifts the arm's de Bruijn indices).
def refine_bound (env : MatchEnv) (k : I64) (pattern : Term) (acc : IndexSolution) : IndexMatch :=
    if refines k acc.refine then IndexMatch.unknown
    else
        let with_skolems : List (Pair Identifier Term) := add_skolems env (free_locals env.locals pattern) acc.subst in
        let replacement : Term := apply_subst with_skolems pattern in
        let s : IndexSolution := {
            subst := with_skolems,
            refine := List.cons (Pair.pair k replacement) acc.refine,
            refine_named := acc.refine_named,
        } in
        IndexMatch.solved s

/// `refine_bound` for a local written by name.
def refine_named_local (env : MatchEnv) (b : Identifier) (pattern : Term) (acc : IndexSolution) : IndexMatch :=
    match lookup_subst b acc.refine_named {
        Option.some _ => IndexMatch.unknown,
        Option.none =>
            let with_skolems : List (Pair Identifier Term) :=
                add_skolems env (free_locals env.locals pattern) acc.subst in
            let replacement : Term := apply_subst with_skolems pattern in
            let s : IndexSolution := {
                subst := with_skolems,
                refine := acc.refine,
                refine_named := List.cons (Pair.pair b replacement) acc.refine_named,
            } in
            IndexMatch.solved s,
    }

#[terminating]
def add_skolems (env : MatchEnv) (names : List Identifier) (subst : List (Pair Identifier Term))
    : List (Pair Identifier Term) :=
    match names {
        List.empty => subst,
        List.cons x rest =>
            match lookup_subst x subst {
                Option.some _ => add_skolems env rest subst,
                Option.none =>
                    add_skolems env rest (List.cons (Pair.pair x (skolem_for env x)) subst),
            },
    }

/// `len` -> `len@<suffix>`. `@` cannot appear in a source identifier, so a
/// skolem never captures a user name.
def skolem_for (env : MatchEnv) (x : Identifier) : Term :=
    match x {
        Identifier.id s => named_var (Identifier.id (String.concat s (String.concat "@" env.skolem_suffix))),
    }

// --- Applying a solution ------------------------------------------------------

pub def has_refinement (s : IndexSolution) : Bool :=
    Bool.not (List.is_empty s.refine && List.is_empty s.refine_named)

/// Field types for an arm. The uniform header params are substituted from the
/// scrutinee's spine by name (exactly as before); the index variables take the
/// solution's bindings instead of the scrutinee's raw index.
pub def refine_field_types (ind : Inductive) (sc_typ : Term) (s : IndexSolution) (field_types : List Term)
    : List Term :=
    let positions : List I64 := index_positions ind in
    let actual : List Term := match flatten_call_spine sc_typ { CallSpine.mk _head args => args } in
    let uniform : List Term := subst_uniform ind.params actual positions 0 field_types in
    List.map (apply_subst s.subst) uniform

#[terminating]
def subst_uniform (params : List Param) (actual : List Term) (positions : List I64) (i : I64) (ts : List Term)
    : List Term :=
    match params {
        List.empty => ts,
        List.cons p prest =>
            match actual {
                List.empty => ts,
                List.cons a arest =>
                    let next : List Term :=
                        if List.any (fn (j : I64) => I64.beq i j) positions
                        then ts
                        else List.map (name_subst_term p.name a) ts in
                    subst_uniform prest arest positions (i + 1) next,
            },
    }

/// `expected` with each refined local (by index or by name) replaced by its
/// constructor index, in the scrutinee's (outer) context.
pub def refine_expected (s : IndexSolution) (expected : Term) : Term :=
    apply_subst s.refine_named (refine_indexed s.refine expected)

#[terminating]
def refine_indexed (refine : List (Pair I64 Term)) (expected : Term) : Term :=
    match refine {
        List.empty => expected,
        List.cons r rest =>
            match r {
                Pair.pair k replacement =>
                    // Open a gap above `k`, then let `term_subst` fill `k` and
                    // close it: every other index comes out unchanged.
                    refine_indexed rest (term_subst k replacement (term_shift_above (k + 1) 1 expected)),
            },
    }

#[terminating]
pub def apply_subst (subst : List (Pair Identifier Term)) (t : Term) : Term :=
    match subst {
        List.empty => t,
        List.cons b rest =>
            match b {
                Pair.pair x v => apply_subst rest (name_subst_term x v t),
            },
    }

// --- Small helpers -------------------------------------------------------------

def named_var (x : Identifier) : Term := Term.var sentinel (DebugName.named x)

def is_named_var (x : Identifier) (t : Term) : Bool :=
    match term_peel t {
        Term.var k dbg =>
            I64.beq k sentinel && (match dbg {
                DebugName.named y => id_eq x y,
                DebugName.unnamed => false,
            }),
        _ => false,
    }

/// The index variable `t` is, if it is one.
def local_var_name (locals : List Identifier) (t : Term) : Option Identifier :=
    match term_peel t {
        Term.var k dbg =>
            if I64.beq k sentinel
            then match dbg {
                DebugName.named y =>
                    if List.any (fn (x : Identifier) => id_eq x y) locals then Option.some y else Option.none,
                DebugName.unnamed => Option.none,
            }
            else Option.none,
        _ => Option.none,
    }

/// A constructor application as (canonical name, arguments). A `Term.con` is
/// the checker's own constructor-application node; its present arguments are
/// the spine.
def ctor_spine (env : MatchEnv) (t : Term) : Option (Pair Identifier (List Term)) :=
    match term_peel t {
        Term.con c =>
            match ctor_name_of env.scope (named_var c.name) {
                Option.some n => Option.some (Pair.pair n (present_args c.args)),
                Option.none => Option.none,
            },
        _ =>
            match flatten_call_spine t {
                CallSpine.mk head args =>
                    match ctor_name_of env.scope head {
                        Option.some n => Option.some (Pair.pair n args),
                        Option.none => Option.none,
                    },
            },
    }

/// A constructor reference's canonical BARE name (`Nat.succ` and `succ` are
/// both `succ`), or none when the head is not a constructor.
def ctor_name_of (scope : Scope) (t : Term) : Option Identifier :=
    match term_peel t {
        Term.var k dbg =>
            if Bool.not (I64.beq k sentinel) then Option.none
            else match dbg {
                DebugName.unnamed => Option.none,
                DebugName.named id =>
                    match id {
                        Identifier.id s =>
                            let bare : Identifier := Identifier.id (dotted_tail s) in
                            if is_ctor scope id || is_ctor scope bare then Option.some bare else Option.none,
                    },
            },
        _ => Option.none,
    }

def is_ctor (scope : Scope) (id : Identifier) : Bool :=
    Bool.not (List.is_empty (scope_find_all_inductives_by_constructor (NamePath.mk (List.cons id List.empty)) scope))

def dotted_tail (s : String) : String :=
    let i : I64 := String.find_last s "." in
    if I64.lt i 0 then s else String.slice s (i + 1) (String.length s - i - 1)

#[terminating]
def present_args (args : List (Option Term)) : List Term :=
    match args {
        List.empty => List.empty,
        List.cons a rest =>
            match a {
                Option.some t => List.cons t (present_args rest),
                Option.none => present_args rest,
            },
    }

/// The index variables `t` mentions, each once, in first-occurrence order.
def free_locals (locals : List Identifier) (t : Term) : List Identifier :=
    List.filter (fn (x : Identifier) => mentions_any (List.cons x List.empty) t) locals

def mentions_any (names : List Identifier) (t : Term) : Bool :=
    List.any (fn (x : Identifier) => Bool.not (Similar.similar (name_subst_term x Term.hole t) t)) names

#[terminating]
def lookup_subst (x : Identifier) (subst : List (Pair Identifier Term)) : Option Term :=
    match subst {
        List.empty => Option.none,
        List.cons b rest =>
            match b {
                Pair.pair y v => if id_eq x y then Option.some v else lookup_subst x rest,
            },
    }

#[terminating]
def refines (k : I64) (refine : List (Pair I64 Term)) : Bool :=
    match refine {
        List.empty => false,
        List.cons r rest =>
            match r {
                Pair.pair j _ => I64.beq j k || refines k rest,
            },
    }

#[terminating]
def list_nth (xs : List A) (i : I64) : Option A :=
    match xs {
        List.empty => Option.none,
        List.cons x rest => if I64.beq i 0 then Option.some x else list_nth rest (i - 1),
    }
