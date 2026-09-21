use lib::types {
  Con, DebugName, Identifier, Literal, LocalScope, MatchCase, NamePath,
  NameRef, Scope, Term, id_eq, show_identifier, sentinel, term_peel,
}
use lib::scope {
  flatten_call_spine, last_dot_index, scope_find_def_body,
  scope_find_inductive_by_constructor, scope_find_local, scope_resolve_name,
}
use lib::typecheck::subst {beta_reduce, term_shift, term_subst}

// ─── Weak-head normal form ───────────────────────────────────────────
//
// Conversion checking: two types are definitionally equal when they
// REDUCE to the same thing, not only when they are written the same
// way. `lang/typecheck/unify.mo` compares `Term`s structurally, so a
// declared type that is still an unreduced application (`identity_type
// foo`) never gets compared against what it computes to (`Bool`). This
// module supplies the missing reduction step; `unify` calls it only
// after a structural comparison has already failed, so the happy path
// pays nothing.
//
// Three reduction rules, which is what conversion checking at this stage
// needs:
//
//   beta   `(fn x => body) arg`  ->  `body[x := arg]`
//   delta  a free `Term.var` naming a global def  ->  that def's body
//   iota   `match c { K xs => body }` (c a KNOWN constructor
//          application) -> `body[xs := c's fields]`; same for `if` on
//          `Bool.true`/`Bool.false`
//
// Beta and delta are needed together, and neither is useful alone
// here: a type-level application like `identity_type foo` is headed by
// a FREE variable, not a `Term.lam`, so beta has nothing to fire on
// until delta has unfolded the head into the `Term.lam` chain a `def`'s
// body actually is (`def_params_of_term`, `lang/scope.mo`). Iota sits on
// top of both: a scrutinee like `f P.p0` only becomes a constructor
// application after delta and beta have had their turn.
//
// Iota is the delicate one because `Literal.match_`'s arms are a
// binding form that binds `List.length args` de Bruijn levels at once
// (AGENTS.md item 22) -- substituting several levels simultaneously is
// where this kind of code goes subtly wrong; see
// `whnf_subst_case_fields`'s own doc comment for the exact trap.
//
// Iota is also step 1 of the eliminator roadmap recorded in
// `plans/type-system/match-to-recursor.md`: iota -> dependent index
// refinement -> `Eq.rec` as a real def -> optionally generating `T.rec`
// per inductive. Converting `match` to recursors would need this same
// reduction machinery (a primitive recursor reduces by a MORE complex
// rule than this arm), so this arm is the cheap half of that path
// either way.
//
// There is no metavariable handling here because this checker has no
// metavariables: `Term.hole` is a matches-anything wildcard, not a
// solvable meta (see `unify`'s own `Term.hole` arms). A reducer for a
// checker WITH metas would have to avoid committing to a reduction
// path before they are solved.

/// Default step budget. Conversion checking needs a handful of steps --
/// unfold a type-level def, beta it, look at the head -- so this is
/// generous rather than tight. It is a bound on DIVERGENCE, not a
/// tuning knob: the self-hosted compiler has no termination checker
/// yet, and `#[partial]` is applied to ~2000 defs in this tree, so
/// nothing verifies that an unfolded body terminates. Running out of
/// fuel is not an error -- reduction simply stops and the term is
/// compared in whatever form it reached, which is exactly the
/// (conservative) behaviour this had before reduction existed.
def whnf_fuel : I64 := 64

/// Reduce `t` to weak-head normal form: keep reducing at the HEAD until
/// the head is rigid (a `pi`, a sort, a literal, a constructor, a
/// variable with no body, ...). Sub-terms are left alone -- the head is
/// all a structural comparison looks at before recursing, and each
/// recursive step goes back through `unify`, which reduces again.
def whnf (scope : Scope) (locals : LocalScope) (t : Term) : Term :=
    whnf_go whnf_fuel scope locals t

/// `#[partial]`: fuel-bounded, but the decrement is not a structural
/// subterm the checker can see.
#[partial]
def whnf_go (fuel : I64) (scope : Scope) (locals : LocalScope) (t0 : Term) : Term :=
    // Peel `Term.ctx` here rather than at each arm: a located wrapper
    // would otherwise fall through to the rigid-head case and stop
    // reduction dead, silently.
    let t : Term := term_peel t0 in
    if I64.lt fuel 1 then
        t
    else
        match t {
            Term.app f a =>
                // Reducing `f` recursively is what handles a spine of
                // any length: `f g x` reduces `f g` first, so a
                // multi-parameter def unfolds and betas one argument at
                // a time without collecting the spine explicitly.
                let f_r : Term := whnf_go (fuel - 1) scope locals f in
                match f_r {
                    Term.lam _dbg _typ body => whnf_go (fuel - 1) scope locals (beta_reduce body a),
                    // Stuck head. Keep the reduced head anyway -- it is
                    // no less reduced than what came in, and a caller
                    // comparing two stuck applications compares heads.
                    _ => Term.app f_r a,
                },
            Term.var idx dbg =>
                if I64.beq idx sentinel then
                    match whnf_delta scope locals dbg {
                        Option.some body => whnf_go (fuel - 1) scope locals body,
                        Option.none => t,
                    }
                else
                    // A bound de Bruijn variable. Its binder is outside
                    // this term, so there is nothing to unfold.
                    t,
            Term.lit l =>
                // Iota. A `match`/`if` reduces only when its scrutinee
                // has already reduced to a KNOWN constructor
                // application; anything else is rigid here exactly
                // like the heads below. The reduced scrutinee is kept
                // in the stuck case -- a caller comparing two stuck
                // matches then compares reduced scrutinees.
                match l {
                    Literal.match_ scrut cases =>
                        let scrut_r : Term := whnf_go (fuel - 1) scope locals scrut in
                        match whnf_iota_case scrut_r cases scope {
                            Option.some body => whnf_go (fuel - 1) scope locals body,
                            Option.none => Term.lit (Literal.match_ scrut_r cases),
                        },
                    Literal.if_ cond then_ else_ =>
                        let cond_r : Term := whnf_go (fuel - 1) scope locals cond in
                        match whnf_bool_con cond_r scope {
                            Option.some b =>
                                if b
                                then whnf_go (fuel - 1) scope locals then_
                                else whnf_go (fuel - 1) scope locals else_,
                            Option.none => Term.lit (Literal.if_ cond_r then_ else_),
                        },
                    // `str`/`char`/`num`/`flt` and the two deprecated
                    // struct forms are rigid. Already in WHNF.
                    _ => t,
                },
            // Rigid heads: `pi`, `forall`, `type_`, `ntv`, `con`,
            // `hole`, and the two macro-only forms. Already in WHNF.
            _ => t,
        }

// ─── Iota ────────────────────────────────────────────────────────────
//
// Dispatch and substitution for the two literal reduction rules. The
// order of the pieces below mirrors reduction order: recognize a
// constructor application (`whnf_con_head`), pick the arm
// (`whnf_case_for`), then substitute its pattern binders
// (`whnf_fire_case`).

/// The constructor's own simple name: the LAST dotted segment of
/// whatever spelling the term carries. Constructor references are
/// written qualified (`Sigma.dpair`, `P.p0`) or bare (`dpair`, after
/// an `open`), but scope registers them under their bare name only
/// (`add_constructors_go`, `lang/scope.mo`) and match arms are stored
/// stripped the same way (`match_case_name`, `lang/parser.mo`), so the
/// simple name is the one thing all three spellings agree on. Local
/// twin of `last_dotted_segment` (`lang/typecheck/infer.mo`) -- the
/// same cannot just be imported from there, since `infer.mo` itself
/// depends on this module's `unify` path.
def whnf_simple_name (id : Identifier) : Identifier :=
    let s : String := show_identifier id in
    let dot : I64 := last_dot_index s 0 (0 - 1) in
    if I64.lt dot 0 then id else Identifier.id (String.drop (dot + 1) s)

/// Whether `simple` names SOME registered constructor. One lookup
/// settles it because constructors live in scope under their bare
/// name; this is what keeps iota from firing on a stuck NON-constructor
/// head that merely shares a case's name -- a head that named a `def`
/// would have been delta-unfolded already, but a type name, a class,
/// or an unbound name all stay stuck and must not dispatch.
def whnf_is_constructor (simple : Identifier) (scope : Scope) : Bool :=
    match scope_find_inductive_by_constructor (NamePath.npath (List.cons simple List.empty)) scope {
        Option.some _ => true,
        Option.none => false,
    }

/// A reduced scrutinee read as a constructor application: the
/// constructor's simple name and its field arguments in declaration
/// order. `Option.none` when the scrutinee is anything else -- a
/// variable, a stuck head, another literal.
///
/// Two shapes, because a constructor application has two spellings in
/// this compiler. What the parser and elaborator actually build is a
/// FREE-VAR application spine (`Two.mk a b` -- the parser never builds
/// `Term.con`, see `type_check_con`'s own doc comment,
/// `lang/typecheck/infer.mo`); `Term.con` exists for lowering, pretty
/// printing and hand-built fixtures, and is trusted rather than
/// re-resolved.
def whnf_con_head (scrut : Term) (scope : Scope) : Option (Pair Identifier (List Term)) :=
    match scrut {
        Term.con c =>
            match c {
                Con.mk cname _typ_name _num_args args =>
                    match whnf_con_args args {
                        Option.some field_args =>
                            Option.some (Pair.pair (whnf_simple_name cname) field_args),
                        Option.none => Option.none,
                    },
            },
        _ =>
            match flatten_call_spine scrut {
                CallSpine.mk head args =>
                    match head {
                        Term.var idx dbg =>
                            if I64.beq idx sentinel then
                                match dbg {
                                    DebugName.named id =>
                                        let simple : Identifier := whnf_simple_name id in
                                        if whnf_is_constructor simple scope
                                        then Option.some (Pair.pair simple args)
                                        else Option.none,
                                    DebugName.unnamed => Option.none,
                                }
                            else Option.none,
                        _ => Option.none,
                    },
            },
    }

/// `Con`'s arguments are `Option Term` (unelaborated positions stay
/// `none`); every one must be present for iota to fire.
#[partial]
def whnf_con_args (args : List (Option Term)) : Option (List Term) :=
    match args {
        List.empty => Option.some List.empty,
        List.cons hd rest =>
            match hd {
                Option.some a =>
                    match whnf_con_args rest {
                        Option.some tl => Option.some (List.cons a tl),
                        Option.none => Option.none,
                    },
                Option.none => Option.none,
            },
    }

/// The first NAMED case whose pattern name matches, else none. Wildcard
/// fallback is `whnf_iota_case`'s job -- it has to rescan from the
/// ORIGINAL list, since a `_` arm may sit before the named scan's
/// position. Mirrors `find_case_for_ctor` + `find_wildcard_case`
/// (`lang/lower_core_ir.mo`) so reduction and the runtime's tag-indexed
/// dispatch agree on which arm wins. Case names are stored
/// already-stripped, but `whnf_simple_name` is applied anyway so
/// hand-built terms written qualified behave the same.
#[partial]
def whnf_named_case_for (con_name : Identifier) (cases : List MatchCase) : Option MatchCase :=
    match cases {
        List.empty => Option.none,
        List.cons hd rest =>
            match hd {
                MatchCase.mc name _ _ _ =>
                    if id_eq (whnf_simple_name name) con_name
                    then Option.some hd
                    else whnf_named_case_for con_name rest,
            },
    }

/// The `_` fallback arm, reached only after every named case missed --
/// scanned from the head of the FULL case list, because a wildcard
/// written before other arms must still win the fallback. A wildcard
/// binds nothing (`type_check_match_case` rejects `_` with arguments),
/// and that is enforced again at fire time by the arity check in
/// `whnf_fire_case`.
#[partial]
def whnf_wildcard_case (cases : List MatchCase) : Option MatchCase :=
    match cases {
        List.empty => Option.none,
        List.cons hd rest =>
            match hd {
                MatchCase.mc name _ _ _ =>
                    if String.beq (show_identifier (whnf_simple_name name)) "_"
                    then Option.some hd
                    else whnf_wildcard_case rest,
            },
    }

/// Dispatch: reduce `match scrut cases` by firing whichever arm `scrut`
/// selects. `Option.none` = stuck (scrutinee not a constructor, no
/// matching arm, or an arity mismatch -- reduction only ever widens
/// what a sound checker accepts, so an ill-shaped match stays as it
/// came in).
def whnf_iota_case (scrut : Term) (cases : List MatchCase) (scope : Scope) : Option Term :=
    match whnf_con_head scrut scope {
        Option.none => Option.none,
        Option.some p =>
            match p {
                Pair.pair con_name field_args =>
                    match whnf_named_case_for con_name cases {
                        Option.some case_ => whnf_fire_case case_ field_args,
                        Option.none =>
                            match whnf_wildcard_case cases {
                                Option.some case_ => whnf_fire_case case_ field_args,
                                Option.none => Option.none,
                            },
                    },
            },
    }

/// Fire one arm: substitute the constructor's field arguments for the
/// case's pattern binders. `Option.none` unless the argument count
/// matches the binder count -- a partial application has nothing to
/// project, and a well-typed checked match never over-applies.
def whnf_fire_case (case_ : MatchCase) (field_args : List Term) : Option Term :=
    match case_ {
        MatchCase.mc _name binders body _field_pattern =>
            let n : I64 := List.length binders in
            if I64.beq n (List.length field_args)
            then Option.some (whnf_subst_case_fields body field_args n)
            else Option.none,
    }

/// Substitute `args` (the constructor's fields, in declaration order)
/// for a case body's `n` pattern binders.
///
/// The binders are the case's `List.length args` levels-at-once
/// (AGENTS.md item 22), FIRST-declared field OUTERMOST -- the same
/// convention as a `Term.lam` chain, and as the runtime's
/// `extend_env_with_fields` (`lang/core_eval.mo`), which binds fields
/// in declaration order so the last one ends up innermost. So the
/// outermost binder sits at de Bruijn index `n-1`, and the fold
/// substitutes OUTERMOST-FIRST: step `k` replaces index `k-1` with its
/// argument shifted up by the `k-1` binders still in scope, and each
/// later step's decrement brings every earlier argument down again.
///
/// Substituting innermost-first instead would insert each argument
/// under-scoped -- its free variables still counting binders that have
/// not been substituted yet -- and the next step would then overwrite
/// them. `beta_reduce` never faces this because it peels exactly ONE
/// `Term.lam` at a time; this is the many-at-once sibling.
#[partial]
def whnf_subst_case_fields (body : Term) (args : List Term) (k : I64) : Term :=
    match args {
        List.empty => body,
        List.cons a rest =>
            whnf_subst_case_fields (term_subst (k - 1) (term_shift (k - 1) a) body) rest (k - 1),
    }

/// `Option.some b` when `cond` has reduced to `Bool`'s constructor
/// `true`/`false` (by simple name -- those two are the only
/// constructors an `if` condition can inhabit; the con-shape and
/// constructor-ness checks are shared with `match` dispatch above).
/// Anything else is stuck.
def whnf_bool_con (cond : Term) (scope : Scope) : Option Bool :=
    match whnf_con_head cond scope {
        Option.some p =>
            match p {
                Pair.pair name args =>
                    match args {
                        List.empty =>
                            if String.beq (show_identifier name) "true"
                            then Option.some true
                            else if String.beq (show_identifier name) "false"
                            then Option.some false
                            else Option.none,
                        _ => Option.none,
                    },
            },
        Option.none => Option.none,
    }

/// Delta: the body of the global `def` this free variable names, if it
/// names one.
///
/// The local check is not an optimisation -- it is what keeps this
/// sound. A free `Term.var` is not necessarily a global: `locals_with_
/// def_typevars` (`lang/module.mo`) skolemises a def's implicit type
/// parameters into NAMED locals, and those resolve through this same
/// path. Unfolding a local `V` into a same-named global `V`'s body
/// would substitute an unrelated definition for a bound type variable.
def whnf_delta (scope : Scope) (locals : LocalScope) (dbg : DebugName) : Option Term :=
    match dbg {
        DebugName.named id =>
            match scope_find_local id locals {
                Option.some _ => Option.none,
                Option.none =>
                    // Resolve first, then look the body up under the
                    // name resolution returned: the same two-step
                    // `type_check_free_var` uses for `def_sigs`, so a
                    // bare name and its qualified form reach the same
                    // entry.
                    match scope_resolve_name (NameRef.nid id) scope locals {
                        ok sd => scope_find_def_body sd.name scope,
                        err _ => Option.none,
                    },
            },
        DebugName.unnamed => Option.none,
    }
