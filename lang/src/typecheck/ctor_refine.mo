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
    DebugName, Identifier, InductConstructor, Inductive, Literal, NamePath, Param, Scope,
    Similar, Term, id_eq, sentinel, term_peel,
}
use lang::scope {
    CallSpine, find_constructor_in_inductive, flatten_call_spine, rebuild_call,
    scope_find_all_inductives_by_constructor, scope_find_inductive,
}
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
    match ctor_spine env (nat_literal_unary target) {
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
pub def present_args (args : List (Option Term)) : List Term :=
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

// --- Nat literals ---------------------------------------------------------------

/// The largest `Nat` literal unfolded to a constructor chain; larger ones stay
/// as written and match nothing (`unknown`).
pub def nat_literal_bound : I64 := 64

/// A small `Nat` literal as its canonical unary constructor chain. `Vec 3`
/// must compare with `Vec (succ (succ (succ zero)))`; `Nat.of_i64 3` cannot
/// reduce in the checker (its body tests a native `I64.lt`).
#[partial]
pub def nat_literal_term (n : I64) : Term :=
    if I64.beq n 0 then
        Term.var sentinel (DebugName.named (Identifier.id "Nat.zero"))
    else
        Term.app (Term.var sentinel (DebugName.named (Identifier.id "Nat.succ")))
            (nat_literal_term (I64.sub n 1))

/// `t` as a constructor chain when it is a small non-negative integer literal
/// or `Nat.of_i64` of one; otherwise `t` unchanged.
def nat_literal_unary (t : Term) : Term :=
    match small_nat_literal t {
        Option.some n => nat_literal_term n,
        Option.none => t,
    }

/// `nat_literal_unary` through a constructor chain: `succ 0` is `succ zero`.
#[terminating]
def nat_literal_deep (t : Term) : Term :=
    match small_nat_literal t {
        Option.some n => nat_literal_term n,
        Option.none =>
            match term_peel t {
                Term.app f a => Term.app f (nat_literal_deep a),
                _ => t,
            },
    }

#[terminating]
def small_nat_literal (t : Term) : Option I64 :=
    match term_peel t {
        Term.lit l =>
            match l {
                Literal.num n _ => if I64.lt n 0 || I64.lt nat_literal_bound n then Option.none else Option.some n,
                _ => Option.none,
            },
        _ =>
            match flatten_call_spine t {
                CallSpine.mk head args =>
                    match args {
                        List.cons only rest =>
                            if List.is_empty rest && is_named_var (Identifier.id "Nat.of_i64") head
                            then small_nat_literal only
                            else Option.none,
                        List.empty => Option.none,
                    },
            },
    }

// --- Introduction (Stage 3c) ------------------------------------------------------

/// A constructor application of an indexed family, saturated: one argument
/// per constructor field.
pub struct IntroCtor {
    ind : Inductive,
    ctor : InductConstructor,
    args : List Term,
}

/// `t` as a saturated constructor application of an indexed family, if it is
/// one. A constructor two families share, or a partial application, is none.
pub def intro_ctor (scope : Scope) (t : Term) : Option IntroCtor :=
    match term_peel t {
        Term.con c => intro_ctor_in scope (owner_named scope c.typ_name) c.name (present_args c.args),
        _ =>
            match flatten_call_spine t {
                CallSpine.mk head args =>
                    match term_peel head {
                        Term.var k dbg =>
                            if Bool.not (I64.beq k sentinel) then Option.none
                            else match dbg {
                                DebugName.named id => intro_ctor_named scope id args,
                                DebugName.unnamed => Option.none,
                            },
                        _ => Option.none,
                    },
            },
    }

/// A constructor named by `id`: through its written qualifier (`Vec.cons`), or
/// through the one family owning the bare name.
def intro_ctor_named (scope : Scope) (id : Identifier) (args : List Term) : Option IntroCtor :=
    match id {
        Identifier.id s =>
            let dot : I64 := String.find_last s "." in
            if I64.lt dot 0
            then
                match scope_find_all_inductives_by_constructor (NamePath.mk [id]) scope {
                    List.cons only more =>
                        if List.is_empty more then intro_ctor_in scope (Option.some only) id args else Option.none,
                    List.empty => Option.none,
                }
            else
                intro_ctor_in scope (owner_named scope (NamePath.mk [Identifier.id (String.slice s 0 dot)]))
                    (Identifier.id (dotted_tail s)) args,
    }

/// Does `id` name a constructor in scope: `Nat.zero` through its owner, or a
/// bare `zero` owned by some family?
pub def names_constructor (scope : Scope) (id : Identifier) : Bool :=
    match id {
        Identifier.id s =>
            let dot : I64 := String.find_last s "." in
            if I64.lt dot 0
            then Bool.not (List.is_empty (scope_find_all_inductives_by_constructor (NamePath.mk [id]) scope))
            else match owner_named scope (NamePath.mk [Identifier.id (String.slice s 0 dot)]) {
                Option.some ind =>
                    match find_constructor_in_inductive ind (NamePath.mk [Identifier.id (dotted_tail s)]) {
                        Option.some _ => true,
                        Option.none => false,
                    },
                Option.none => false,
            },
    }

/// The families owning the constructor `id` names: the qualifier's family
/// for `Bool.false`, every family with a constructor `false` for a bare one.
def constructor_owners (scope : Scope) (id : Identifier) : List NamePath :=
    match id {
        Identifier.id s =>
            let dot : I64 := String.find_last s "." in
            if I64.lt dot 0
            then List.map (fn (ind : Inductive) => ind.name) (scope_find_all_inductives_by_constructor (NamePath.mk [id]) scope)
            else match owner_named scope (NamePath.mk [Identifier.id (String.slice s 0 dot)]) {
                Option.some ind =>
                    match find_constructor_in_inductive ind (NamePath.mk [Identifier.id (dotted_tail s)]) {
                        Option.some _ => [ind.name],
                        Option.none => List.empty,
                    },
                Option.none => List.empty,
            },
    }

/// Do `a` and `b` name the same constructor in two spellings (`false` and
/// `Bool.false`)? The tails must agree and the two spellings must share an
/// owning family.
pub def same_constructor_ref (scope : Scope) (a : Identifier) (b : Identifier) : Bool :=
    match a {
        Identifier.id sa =>
            match b {
                Identifier.id sb =>
                    String.beq (dotted_tail sa) (dotted_tail sb)
                        && shares_owner (constructor_owners scope a) (constructor_owners scope b),
            },
    }

def shares_owner (xs : List NamePath) (ys : List NamePath) : Bool :=
    List.any (fn (x : NamePath) => List.any (fn (y : NamePath) => x == y) ys) xs

def owner_named (scope : Scope) (name : NamePath) : Option Inductive :=
    match scope_find_inductive name scope {
        Result.ok ind => Option.some ind,
        Result.err _ => Option.none,
    }

def intro_ctor_in (scope : Scope) (owner : Option Inductive) (bare : Identifier) (args : List Term)
    : Option IntroCtor :=
    match owner {
        Option.none => Option.none,
        Option.some ind =>
            if List.is_empty (index_positions ind) then Option.none
            else match find_constructor_in_inductive ind (NamePath.mk [bare]) {
                Option.some c =>
                    if I64.beq (List.length c.params) (List.length args)
                    then
                        let ic : IntroCtor := { ind := ind, ctor := c, args := args } in
                        Option.some ic
                    else Option.none,
                Option.none => Option.none,
            },
    }

/// The bindings for a constructor's index variables when it is checked against
/// `expected`: the solved values (`cons : Vec 1 A` gives `len := zero`, so the
/// tail is checked at `Vec zero A`), or none when the solution is not plain
/// (unknown, impossible, or a refinement of a variable index).
pub def intro_index_bindings (scope : Scope) (ind : Inductive) (c : InductConstructor) (expected : Term)
    : Option (List (Pair Identifier Term)) :=
    let positions : List I64 := index_positions ind in
    if List.is_empty positions || Bool.not (is_family_type ind expected) then Option.none
    else
        let env : MatchEnv := {
            locals := index_locals ind positions,
            binders := List.empty,
            scope := scope,
            skolem_suffix := "intro",
        } in
        match solve_ctor env ind c expected {
            IndexMatch.solved sol => if has_refinement sol then Option.none else Option.some sol.subst,
            _ => Option.none,
        }

/// The indices a constructor application produces, one per index position:
/// the constructor's declared index patterns with its index variables solved
/// from the arguments. A field typed by the same family supplies its
/// argument's indices -- a nested constructor application's own, or what
/// `arg_type` reports for anything else (a typed local). None when an index
/// variable stays unsolved.
#[terminating]
pub def intro_indices (scope : Scope) (arg_type : Term -> Option Term) (ic : IntroCtor) : Option (List Term) :=
    let positions : List I64 := index_positions ic.ind in
    let env : MatchEnv := {
        locals := index_locals ic.ind positions,
        binders := List.empty,
        scope := scope,
        skolem_suffix := "intro",
    } in
    let fields : List Term := List.map (fn (p : Param) => p.type_) ic.ctor.params in
    match intro_fields env arg_type ic.ind positions fields ic.args (IndexMatch.solved empty_solution) {
        IndexMatch.solved s =>
            let idx : List Term := List.map (apply_subst s.subst) (ctor_index_patterns ic.ind ic.ctor positions) in
            if List.any (fn (i : Term) => mentions_any env.locals i) idx then Option.none else Option.some idx,
        _ => Option.none,
    }

#[terminating]
def intro_fields (env : MatchEnv) (arg_type : Term -> Option Term) (ind : Inductive) (positions : List I64)
    (fields : List Term) (args : List Term) (state : IndexMatch) : IndexMatch :=
    match fields {
        List.empty => state,
        List.cons f frest =>
            match args {
                List.empty => state,
                List.cons a arest =>
                    let next : IndexMatch := match state {
                        IndexMatch.solved acc =>
                            match arg_indices env.scope arg_type ind a {
                                Option.some found =>
                                    match_all env (family_indices ind positions f) found (IndexMatch.solved acc),
                                Option.none => state,
                            },
                        _ => state,
                    } in
                    intro_fields env arg_type ind positions frest arest next,
            },
    }

/// The indices of `a` as a value of family `ind`: its own when it is a
/// constructor application of `ind`, else read off `arg_type a`.
#[terminating]
def arg_indices (scope : Scope) (arg_type : Term -> Option Term) (ind : Inductive) (a : Term) : Option (List Term) :=
    match intro_ctor scope a {
        Option.some inner =>
            if same_family ind inner.ind then intro_indices scope arg_type inner else Option.none,
        Option.none =>
            match arg_type a {
                Option.some t =>
                    if is_family_type ind t
                    then Option.some (family_indices ind (index_positions ind) t)
                    else Option.none,
                Option.none => Option.none,
            },
    }

/// The index arguments of a type `t` that is an application of `ind`, or the
/// empty list for any other type (which then matches nothing).
def family_indices (ind : Inductive) (positions : List I64) (t : Term) : List Term :=
    if is_family_type ind t
    then match flatten_call_spine t { CallSpine.mk _head args => args_at args positions }
    else List.empty

def is_family_type (ind : Inductive) (t : Term) : Bool :=
    match flatten_call_spine t {
        CallSpine.mk head args =>
            I64.beq (List.length args) (List.length ind.params) && names_family ind head,
    }

def names_family (ind : Inductive) (head : Term) : Bool :=
    match term_peel head {
        Term.var k dbg =>
            I64.beq k sentinel && (match dbg {
                DebugName.named id =>
                    match id {
                        Identifier.id s =>
                            match family_bare_name ind {
                                Option.some b => String.beq (dotted_tail s) b,
                                Option.none => false,
                            },
                    },
                DebugName.unnamed => false,
            }),
        _ => false,
    }

def family_bare_name (ind : Inductive) : Option String :=
    match ind.name {
        NamePath.mk ids =>
            match list_last ids {
                Option.some id => match id { Identifier.id s => Option.some (dotted_tail s) },
                Option.none => Option.none,
            },
    }

def same_family (a : Inductive) (b : Inductive) : Bool :=
    match family_bare_name a {
        Option.some x =>
            match family_bare_name b {
                Option.some y => String.beq x y,
                Option.none => false,
            },
        Option.none => false,
    }

/// Whether an indexed constructor application can have type `expected`:
/// `some found` (the application's type, spelled with `expected`'s uniform
/// arguments) when a computed index's constructor head clashes with
/// `expected`'s; none when it fits or nothing safe can be concluded. A
/// variable index on either side is never a clash: it may be refined by an
/// enclosing match the checker does not track.
pub def intro_clash (scope : Scope) (arg_type : Term -> Option Term) (ic : IntroCtor) (expected : Term) : Option Term :=
    let positions : List I64 := index_positions ic.ind in
    if Bool.not (is_family_type ic.ind expected) then Option.none
    else match intro_indices scope arg_type ic {
        Option.none => Option.none,
        Option.some found =>
            let env : MatchEnv := {
                locals := List.empty,
                binders := List.empty,
                scope := scope,
                skolem_suffix := "intro",
            } in
            let wanted : List Term := family_indices ic.ind positions expected in
            let unary : List Term := List.map nat_literal_deep found in
            match match_all env unary wanted (IndexMatch.solved empty_solution) {
                IndexMatch.impossible => Option.some (with_indices expected positions unary),
                _ => Option.none,
            },
    }

/// `t`'s spine with the arguments at `positions` replaced, in order.
pub def with_indices (t : Term) (positions : List I64) (idx : List Term) : Term :=
    match flatten_call_spine t {
        CallSpine.mk head args => rebuild_call head (replace_at args positions idx 0),
    }

#[terminating]
def replace_at (args : List Term) (positions : List I64) (idx : List Term) (i : I64) : List Term :=
    match args {
        List.empty => List.empty,
        List.cons a rest =>
            match positions {
                List.cons p prest =>
                    if I64.beq p i
                    then match idx {
                        List.cons x xrest => List.cons x (replace_at rest prest xrest (i + 1)),
                        List.empty => List.cons a (replace_at rest positions idx (i + 1)),
                    }
                    else List.cons a (replace_at rest positions idx (i + 1)),
                List.empty => List.cons a (replace_at rest positions idx (i + 1)),
            },
    }

#[terminating]
def list_last (xs : List A) : Option A :=
    match xs {
        List.empty => Option.none,
        List.cons x rest => if List.is_empty rest then Option.some x else list_last rest,
    }
