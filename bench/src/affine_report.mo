/// Affine-usage report — Milestone 1 of the affine-by-default viability
/// experiment (*Design B: Viability Experiment*).
///
/// The experiment's whole first question is a number: **if every binder
/// were affine, how many places in this corpus would break?**
/// [[lang/typecheck/usage.mo]] answers it per binder; this file
/// aggregates that over real elaborated modules and prints it.
///
/// It lives in `bench/` rather than as a `monad` subcommand on purpose.
/// A subcommand means rebuilding the self-hosted CLI — a bootstrap
/// cycle — for a measurement that exists to decide whether the
/// experiment is worth continuing at all. `bench/` is already the
/// "`#[test]`-driven, run it by hand, not every commit" mote — but
/// `scripts/check-monad-tests.sh` sweeps it all the same, so the
/// measurements below are gated behind `MONAD_AFFINE_REPORT` and
/// early-return when it is unset: the sweep pays for the aggregation
/// unit tests only. Promote it to a subcommand if it earns one.
///
/// Run the measurements with:
///
/// ```text
/// MONAD_AFFINE_REPORT=1 monad test bench/src/affine_report.mo
/// ```
///
/// ## What the numbers mean
///
/// Each binder lands in one of three buckets by its runtime use count Σ:
///
/// - **Σ = 0** — never used. Affine-legal (weakening is admissible under
///   Design B's R2) and, under Milestone 3, a release at scope exit.
///   This bucket is the automatic-free opportunity, so a large one is
///   good news.
/// - **Σ = 1** — used exactly once. The affine sweet spot: moves, no
///   copy, no release needed at the binding site.
/// - **Σ ≥ 2** — used more than once. Under affine-by-default each of
///   these needs `Copy`, a borrow, or a rewrite. **This is the
///   migration cost.**
///
/// ## The scalar approximation, stated plainly
///
/// The bucket that decides the milestone gate is "Σ ≥ 2 on a type that
/// is not `Copy`". Deciding `Copy` properly means resolving a real
/// instance, which needs the `class Copy` declaration and a `Scope` —
/// Milestone 2's work, not this one's. So this report approximates
/// `Copy` by the builtin scalars (`is_copy_approx` below), which is
/// exactly the set that gets compiler-provided instances anyway.
///
/// The approximation errs in one direction only, and it is the safe
/// one: a user type that would have earned a `Copy` instance is counted
/// here as non-Copy. So the "needs Copy, a borrow, or a rewrite" figure
/// is an **upper bound** on the real migration cost. It cannot flatter
/// the design.
use std::io {println}
open IO {get_env, println}
use lang::module {
  ElaboratedAndCache, ElaboratedModules, elaborate_loaded_modules, elaborate_loaded_modules_cached,
  expand_check_paths, module_info_cache_empty,
}
use lang::types {Decl, Def, Scope, SortLevel, Term, TypeError, show_identifier}
use lang::scope {scope_data_empty}
use lang::typecheck::usage {
  BinderUse, attribute_binder_types, borrow_of_name_set, collect_binder_uses, ctor_name_set,
}
use lang::typecheck::copy_class {copy_verdict}
use lang::typecheck::affine {check_def}
use lang::typecheck::diagnostic {type_error_message}
use std::map {}
use std::list {length}

// ─── Run-by-hand gating ─────────────────────────────────────────────
//
// The measurements below elaborate whole dependency closures — minutes
// each. The sweep runs every #[test] in this mote, so each heavy one
// starts with this gate and returns true when MONAD_AFFINE_REPORT is
// unset (the `std/ansi.mo` NO_COLOR pattern), leaving the sweep to pay
// for the aggregation unit tests only.

def env_flag_set (v : Option String) : Bool :=
    match v {
        some _ => true,
        none => false
    }

def report_enabled : IO Bool := do {
    let v <- get_env "MONAD_AFFINE_REPORT";
    return (env_flag_set v)
}

// ─── Reading a binder's type ───────────────────────────────────────

/// The head symbol of a type term, as a printable name.
///
/// `List Term` reports as `List`, `Term` as `Term`, an unannotated or
/// unresolved binder as `?`. The point is to group the Σ ≥ 2 binders by
/// what they hold, because that is what says whether the migration is
/// "add `Copy` to four types" or "rewrite the compiler".
///
/// Peels `Term.ctx` (a transparent wrapper) and walks the application
/// spine left, since a type is written head-first (`HashMap String
/// Decl` is `app (app HashMap String) Decl`).
#[partial]
def type_head_name (t : Term) : String :=
    match t {
        Term.ctx _loc inner => type_head_name inner,
        Term.app callee _arg => type_head_name callee,
        Term.var _idx dbg =>
            match dbg {
                DebugName.named id => show_identifier id,
                DebugName.unnamed => "?",
            },
        Term.con c =>
            match c {
                Con.mk name _typ_name _num_args _args => show_identifier name,
            },
        Term.ntv n =>
            match n {
                Native.mk name _num_args _args => show_identifier name,
            },
        Term.sort level =>
            match level {
                SortLevel.concrete u => "Type" ++ I64.to_string u,
                SortLevel.var _name => "Type?",
                SortLevel.max _left _right => "Type?",
                SortLevel.succ _inner => "Type?",
            },
        // A binder whose type never got resolved. Common for match-arm
        // binders, whose type lives on the matched constructor and needs
        // a `Scope` `usage.mo` deliberately does not take.
        Term.hole => "?",
        Term.pi _arg _ret => "->",
        Term.forall _dbg _kind body => type_head_name body,
        Term.lam _dbg _typ body => type_head_name body,
        Term.lit _v => "?",
        Term.quote_ _inner => "?",
        Term.var_macro _idx _dbg => "?",
    }

/// Was the scalar approximation of `Copy`; is now the real gate.
///
/// Milestone 2 replaced a hardcoded list of scalar names with
/// `copy_class.copy_verdict`, which resolves an actual `Copy` instance
/// out of the scope (`init/src/copy.mo` declares the class and the
/// builtin instances). The report is the first consumer precisely
/// because it exercises the gate over the whole corpus before anything
/// uses it to reject a program.
///
/// The fail-closed direction is unchanged, so the headline figure keeps
/// meaning the same thing: anything the gate cannot resolve counts as
/// non-Copy, and the "needs Copy, a borrow, or a rewrite" number stays
/// an upper bound.
def binder_is_copy (scope : Scope) (typ : Term) : Bool :=
    match copy_verdict scope typ {
        CopyVerdict.cv_copy => true,
        CopyVerdict.cv_not_copy => false,
        CopyVerdict.cv_ambiguous => false,
    }

def binder_is_ambiguous (scope : Scope) (typ : Term) : Bool :=
    match copy_verdict scope typ {
        CopyVerdict.cv_ambiguous => true,
        _ => false,
    }

// ─── Tallies ───────────────────────────────────────────────────────

/// One type name and how many Σ ≥ 2 binders held it.
pub struct TypeTally {
    name : String,
    count : I64,
}

pub def TypeTally.name (t : TypeTally) : String := t.name

pub def TypeTally.count (t : TypeTally) : I64 := t.count

/// Insert-or-increment. Linear scan: the distinct-type-name list is in
/// the hundreds at most, and a `Map` here would cost more than it saves
/// (see `bench/src/scope_lookup.mo`'s measured 25x regression from
/// exactly that swap at this scale).
#[partial]
def tally_bump (name : String) (ts : List TypeTally) : List TypeTally :=
    match ts {
        List.empty =>
            let fresh : TypeTally := { name := name, count := 1 } in
            List.cons fresh List.empty,
        List.cons t rest =>
            if String.beq (TypeTally.name t) name then
                let bumped : TypeTally := { name := name, count := TypeTally.count t + 1 } in
                List.cons bumped rest
            else
                List.cons t (tally_bump name rest),
    }

/// The whole report, as counted.
pub struct Totals {
    binders : I64,
    zero : I64,
    one : I64,
    many : I64,
    /// Σ ≥ 2 on a type the scalar approximation does NOT call `Copy` —
    /// the upper bound on the migration cost, and the milestone gate.
    many_non_copy : I64,
    by_type : List TypeTally,
    /// Over-used match-arm binders whose type attribution FAILED,
    /// tallied by the constructor that bound them. Makes the `?` row
    /// legible instead of a shrug -- see `print_totals`.
    unresolved : List TypeTally,
    /// Of the Σ ≥ 2 binders, those with **at most one owning use** —
    /// one move plus any number of reads, which a borrow discipline
    /// serves without duplicating anything.
    borrowable : I64,
    /// Total uses that are the direct argument of a real `Borrow.of`
    /// call (`BinderUse.borrowed`, summed over every binder, not just
    /// the 2+ set). Today it is near-zero by construction — B1
    /// converted one call site — so what it measures is that the
    /// borrow-aware budget is LIVE in this report path: if identity
    /// resolution ever silently regressed to an empty borrow set,
    /// this is the line that would drop to 0 and say so.
    borrowed_uses : I64,
    /// Of the Σ ≥ 2 binders, those with **two or more owning uses** —
    /// the same value stored or returned twice. No borrow rescues
    /// these: they need `Copy`, `Clone`, or a rewrite. The irreducible
    /// migration cost.
    needs_dup : I64,
    /// `needs_dup`, restricted to types the scalar approximation does
    /// not call `Copy`.
    needs_dup_non_copy : I64,
    /// Σ ≥ 2 binders the real `Copy` gate granted ω to. Under the old
    /// scalar approximation this was implicit; with real instances it
    /// is worth seeing, because it is the first measurement of whether
    /// instance resolution works at corpus scale.
    copy_granted : I64,
    /// Σ ≥ 2 binders whose carrier matched TWO OR MORE concrete `Copy`
    /// instances. Denied ω, and a real instance collision worth
    /// knowing about.
    copy_ambiguous : I64,
    /// Diagnostics the Milestone 2 rule actually produced, by kind.
    /// Counted independently of the buckets above, so the two must
    /// agree — see `print_totals`'s cross-check.
    diag_copy_required : I64,
    diag_used_after_move : I64,
    diag_linear_unused : I64,
    diag_other : I64,
    /// The first few rendered messages, newest first — what a user
    /// would actually see.
    samples : List String,
}

pub def Totals.binders (t : Totals) : I64 := t.binders

pub def Totals.zero (t : Totals) : I64 := t.zero

pub def Totals.one (t : Totals) : I64 := t.one

pub def Totals.many (t : Totals) : I64 := t.many

pub def Totals.many_non_copy (t : Totals) : I64 := t.many_non_copy

pub def Totals.by_type (t : Totals) : List TypeTally := t.by_type

pub def Totals.unresolved (t : Totals) : List TypeTally := t.unresolved

pub def Totals.borrowable (t : Totals) : I64 := t.borrowable

pub def Totals.borrowed_uses (t : Totals) : I64 := t.borrowed_uses

pub def Totals.needs_dup (t : Totals) : I64 := t.needs_dup

pub def Totals.needs_dup_non_copy (t : Totals) : I64 := t.needs_dup_non_copy

pub def Totals.copy_granted (t : Totals) : I64 := t.copy_granted

pub def Totals.copy_ambiguous (t : Totals) : I64 := t.copy_ambiguous

pub def Totals.diag_copy_required (t : Totals) : I64 := t.diag_copy_required

pub def Totals.diag_used_after_move (t : Totals) : I64 := t.diag_used_after_move

pub def Totals.diag_linear_unused (t : Totals) : I64 := t.diag_linear_unused

pub def Totals.diag_other (t : Totals) : I64 := t.diag_other

pub def Totals.samples (t : Totals) : List String := t.samples

def totals_empty : Totals :=
    { binders := 0, zero := 0, one := 0, many := 0, many_non_copy := 0,
      by_type := List.empty, unresolved := List.empty,
      borrowable := 0, borrowed_uses := 0, needs_dup := 0, needs_dup_non_copy := 0,
      copy_granted := 0, copy_ambiguous := 0,
      diag_copy_required := 0, diag_used_after_move := 0, diag_linear_unused := 0,
      diag_other := 0, samples := List.empty }

/// How an unattributed over-used binder is labelled in the residue
/// table. A `bk_lam` binder carries no constructor, and its blank name
/// read as a mystery row -- it is not one: it is a lambda whose
/// elaborated annotation is a hole, a different gap from an ambiguous
/// constructor and worth telling apart.
def residue_key (u : BinderUse) : String :=
    match BinderUse.kind u {
        BinderKind.bk_lam => "(lambda, no annotation)",
        // A blank name here is the third case, and a small one: a
        // destructured parameter's field pattern is elaborated with
        // `Identifier.id ""` as its case name (`lam_parsed_params_loop`,
        // `lang/parser.mo`), so there is no constructor to look up.
        BinderKind.bk_match => show_identifier (BinderUse.ctor u),
    }

/// Fold one binder into the running totals. Accumulator-passing all the
/// way down, like every list walker in `lang/codegen/` — this runs over
/// whole modules, and the natural non-tail shape holds a native frame
/// per binder.
def tally_binder (scope : Scope) (u : BinderUse) (acc : Totals) : Totals :=
    let n : I64 := BinderUse.count u in
    let tname : String := type_head_name (BinderUse.typ u) in
    let copyable : Bool := binder_is_copy scope (BinderUse.typ u) in
    // Borrow-argument uses summed over ALL binders, not just the 2+
    // set — see the field's doc comment for why the report needs this.
    let acc : Totals := { acc with borrowed_uses := Totals.borrowed_uses acc + BinderUse.borrowed u } in
    if I64.beq n 0 then
        { acc with binders := Totals.binders acc + 1, zero := Totals.zero acc + 1 }
    else if I64.beq n 1 then
        { acc with binders := Totals.binders acc + 1, one := Totals.one acc + 1 }
    else
        let non_copy : I64 :=
            if copyable then Totals.many_non_copy acc
            else Totals.many_non_copy acc + 1 in
        let residue : List TypeTally :=
            if String.beq tname "?" then
                tally_bump (residue_key u) (Totals.unresolved acc)
            else Totals.unresolved acc in
        // At most one owning use means one move plus reads, which
        // borrows serve. Two or more is real duplication.
        let dup : Bool := I64.gt (BinderUse.owning u) 1 in
        { acc with
            binders := Totals.binders acc + 1,
            many := Totals.many acc + 1,
            many_non_copy := non_copy,
            by_type := tally_bump tname (Totals.by_type acc),
            unresolved := residue,
            borrowable := if dup then Totals.borrowable acc else Totals.borrowable acc + 1,
            needs_dup := if dup then Totals.needs_dup acc + 1 else Totals.needs_dup acc,
            needs_dup_non_copy :=
                if dup && not copyable then Totals.needs_dup_non_copy acc + 1
                else Totals.needs_dup_non_copy acc,
            copy_granted :=
                if copyable then Totals.copy_granted acc + 1 else Totals.copy_granted acc,
            copy_ambiguous :=
                if binder_is_ambiguous scope (BinderUse.typ u) then Totals.copy_ambiguous acc + 1
                else Totals.copy_ambiguous acc }

#[partial]
def tally_binders (scope : Scope) (us : List BinderUse) (acc : Totals) : Totals :=
    match us {
        List.empty => acc,
        List.cons u rest => tally_binders scope rest (tally_binder scope u acc),
    }

// ─── Walking a module's defs ───────────────────────────────────────

def def_term (d : Def) : Term := d.term

/// `attribute_binder_types` runs between collection and tallying: the
/// counter is a pure function of the term and so reports every match-arm
/// binder as unknown, and on the compiler's own closure that was 723 of
/// the 2,419 over-used binders -- 30% of the number this whole report
/// exists to produce.
#[partial]
def tally_decls (ctors : HashMap String Bool) (borrows : HashMap String Bool) (s : Scope) (ds : List Decl) (acc : Totals) : Totals :=
    match ds {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Decl.def_d def_ =>
                    let raw : List BinderUse := collect_binder_uses ctors borrows (def_term def_) in
                    let counted : Totals := tally_binders s (attribute_binder_types s raw) acc in
                    // The Milestone 2 rule, run over the same def. Counted
                    // independently of the buckets above so the two can be
                    // cross-checked -- if the rule and the tally disagree,
                    // one of them is wrong, and silence would hide it.
                    let diags : List TypeError := check_def s ctors borrows def_ in
                    tally_decls ctors borrows s rest (tally_diags diags counted),
                // A macro body is a template, not code that runs; its
                // binders are not runtime owners.
                Decl.def_macro_d _def => tally_decls ctors borrows s rest acc,
                // A scoped open wraps one real decl. Codegen ignores
                // these today (`Decl.scoped_open_d`'s own doc comment),
                // so the report does too rather than disagree with the
                // backend it is sizing work for.
                Decl.scoped_open_d _path _filter _inner => tally_decls ctors borrows s rest acc,
                _ => tally_decls ctors borrows s rest acc,
            },
    }

/// Fold the rule's own diagnostics into the totals, keeping the first
/// handful rendered so the report can show what a user would see.
#[partial]
def tally_diags (ds : List TypeError) (acc : Totals) : Totals :=
    match ds {
        List.empty => acc,
        List.cons d rest => tally_diags rest (tally_one_diag d acc),
    }

def tally_one_diag (d : TypeError) (acc : Totals) : Totals :=
    let kept : List String :=
        if I64.lt (List.length (Totals.samples acc)) 6
        then List.cons (type_error_message d) (Totals.samples acc)
        else Totals.samples acc in
    match d {
        TypeError.copy_required _n _t _u =>
            { acc with diag_copy_required := Totals.diag_copy_required acc + 1, samples := kept },
        TypeError.value_used_after_move _n _t _o =>
            { acc with diag_used_after_move := Totals.diag_used_after_move acc + 1, samples := kept },
        TypeError.linear_unused _n _t =>
            { acc with diag_linear_unused := Totals.diag_linear_unused acc + 1, samples := kept },
        _ => { acc with diag_other := Totals.diag_other acc + 1, samples := kept },
    }

#[partial]
def print_lines (ls : List String) : IO I64 :=
    match ls {
        List.empty => do { return 0 },
        List.cons l rest => do {
            println ("    " ++ l);
            print_lines rest
        },
    }

// ─── Rendering ─────────────────────────────────────────────────────

/// Percent of `total`, to one decimal, without a float: `(n * 1000) /
/// total` split at the last digit. `Bench`-style integer formatting,
/// because a float here would print differently under the two runtimes.
def pct (n : I64) (total : I64) : String :=
    if I64.beq total 0 then "0.0"
    else
        let scaled : I64 := (n * 1000) / total in
        I64.to_string (scaled / 10) ++ "." ++ I64.to_string (scaled - (scaled / 10) * 10)

def tally_line (t : TypeTally) : String :=
    "    " ++ I64.to_string (TypeTally.count t) ++ "  " ++ TypeTally.name t

/// Highest count first, by repeated extraction. O(n*k) for the k lines
/// printed, which beats sorting a list this small and needs no
/// comparator plumbing.
#[partial]
def print_top (ts : List TypeTally) (k : I64) : IO I64 :=
    if I64.lt k 1 then do { return 0 }
    else
        match extract_max ts {
            Option.none => do { return 0 },
            Option.some r =>
                match r {
                    MaxSplit.mk best rest => do {
                        println (tally_line best);
                        print_top rest (k - 1)
                    },
                },
        }

pub type MaxSplit {
    mk (best : TypeTally) (rest : List TypeTally),
}

#[partial]
def extract_max (ts : List TypeTally) : Option MaxSplit :=
    match ts {
        List.empty => Option.none,
        List.cons t rest =>
            match extract_max rest {
                Option.none =>
                    let only : MaxSplit := MaxSplit.mk t List.empty in
                    Option.some only,
                Option.some r =>
                    match r {
                        MaxSplit.mk best others =>
                            if I64.gt (TypeTally.count best) (TypeTally.count t) then
                                let keep : MaxSplit := MaxSplit.mk best (List.cons t others) in
                                Option.some keep
                            else
                                let swap : MaxSplit := MaxSplit.mk t (List.cons best others) in
                                Option.some swap,
                    },
            },
    }

def print_totals (label : String) (t : Totals) : IO Bool := do {
    let n : I64 := Totals.binders t;
    println "";
    println ("affine report: " ++ label);
    println ("  binders analysed       " ++ I64.to_string n);
    println ("  used 0 times (free)    " ++ I64.to_string (Totals.zero t) ++ "  (" ++ pct (Totals.zero t) n ++ "%)");
    println ("  used 1 time  (move)    " ++ I64.to_string (Totals.one t) ++ "  (" ++ pct (Totals.one t) n ++ "%)");
    println ("  used 2+ times          " ++ I64.to_string (Totals.many t) ++ "  (" ++ pct (Totals.many t) n ++ "%)");
    println ("  ... of those, non-Copy " ++ I64.to_string (Totals.many_non_copy t) ++ "  (" ++ pct (Totals.many_non_copy t) n ++ "%)");
    println ("  ... Copy granted           " ++ I64.to_string (Totals.copy_granted t) ++ "   (real instances, init/src/copy.mo)");
    println ("  ... Copy ambiguous          " ++ I64.to_string (Totals.copy_ambiguous t) ++ "   (2+ concrete instances matched; denied)");
    println "  ^ PESSIMISTIC bound: what Copy alone would have to cover.";
    println "";
    println "  splitting the 2+ set by how the extra uses are spent:";
    println ("    borrowable (<=1 owning use) " ++ I64.to_string (Totals.borrowable t) ++ "  (" ++ pct (Totals.borrowable t) (Totals.many t) ++ "% of the 2+ set)");
    println ("    borrow-argument uses (all binders) " ++ I64.to_string (Totals.borrowed_uses t) ++ "  (live iff Borrow.of identity resolution works)");
    println ("    needs duplication (2+ owning) " ++ I64.to_string (Totals.needs_dup t) ++ "  (" ++ pct (Totals.needs_dup t) (Totals.many t) ++ "%)");
    println ("    ... of those, non-Copy       " ++ I64.to_string (Totals.needs_dup_non_copy t) ++ "  (" ++ pct (Totals.needs_dup_non_copy t) n ++ "% of all binders)");
    println "  ^ OPTIMISTIC bound: assumes a callee never retains an argument.";
    println "    The real cost sits between the two.";
    println "";
    println "  what the Milestone 2 rule actually reports:";
    println ("    copy_required         " ++ I64.to_string (Totals.diag_copy_required t) ++ "  (borrow it, or add a Copy instance)");
    println ("    value_used_after_move " ++ I64.to_string (Totals.diag_used_after_move t) ++ "  (moved twice; no borrow helps)");
    println ("    linear_unused         " ++ I64.to_string (Totals.diag_linear_unused t));
    println ("    other                 " ++ I64.to_string (Totals.diag_other t));
    // If the rule and the tally disagree, one of them is wrong. Saying
    // so out loud beats two plausible numbers that quietly differ.
    let rule_total : I64 := Totals.diag_copy_required t + Totals.diag_used_after_move t;
    if I64.beq rule_total (Totals.many_non_copy t) then
        println ("    cross-check OK: rule total " ++ I64.to_string rule_total ++ " == non-Copy 2+ binders")
    else
        println ("    CROSS-CHECK FAILED: rule says " ++ I64.to_string rule_total
            ++ " but the tally says " ++ I64.to_string (Totals.many_non_copy t));
    println "  a sample, as a user would see them:";
    let _shown : I64 <- print_lines (Totals.samples t);
    println "  2+ uses by type, most first:";
    let _printed : I64 <- print_top (Totals.by_type t) 20;
    println "  unattributed (`?`) 2+ binders, by the constructor that bound them:";
    let _residue : I64 <- print_top (Totals.unresolved t) 10;
    println "  ^ every row here is GENUINE ambiguity, resolved fail-closed:";
    println "    `mk` is every struct's constructor; `cons` is List and Vec;";
    println "    `ok` is Result and CompileResult. Disambiguating needs the";
    println "    scrutinee's type, which is inference, not lookup.";
    return true
}

// ─── Entry point ───────────────────────────────────────────────────

/// Elaborate one file (with its whole dependency closure) and report on
/// every def the elaboration produced.
///
/// `elaborate_loaded_modules` with `check_deps := false`: the report
/// wants the elaborated terms, and dependency-manifest enforcement is
/// not its business. `elaborated_decls` is the whole closure, not just
/// the target file's own decls, which is what makes one invocation over
/// `lang/src/lib.mo` a corpus-wide measurement.
def report_on (path : String) : IO Bool := do {
    let on <- report_enabled;
    if Bool.not on then return true
    else do {
        let r : Result String ElaboratedModules <- elaborate_loaded_modules path false false;
        match r {
            Result.err e => do {
                println ("affine report: could not elaborate " ++ path ++ ": " ++ e);
                return false
            },
            Result.ok em => do {
                // Built once per run: a per-node scope lookup would be a
                // full scan of the inductives map at every one of the
                // corpus's 44,609 application nodes.
                let ctors : HashMap String Bool := ctor_name_set em.scope;
                let borrows : HashMap String Bool := borrow_of_name_set em.scope;
                let totals : Totals := tally_decls ctors borrows em.scope em.elaborated_decls totals_empty;
                print_totals path totals
            }
        }
    }
}

#[test]
def report_affine_usage_std : IO Bool := report_on "std/src/list.mo"

#[test]
def report_affine_usage_lang : IO Bool := report_on "lang/src/typecheck/traverse.mo"

/// The headline number: the self-hosted compiler's own dependency
/// closure. The target is `affine_target.mo`, not `lang/src/lib.mo`
/// directly -- it pulls in the same closure PLUS `init::copy`, so the
/// scope the `Copy` gate resolves against actually contains the
/// instances. See that file for why the shim is still needed after
/// `Copy` moved into `init`, and for the shortcut that did not work.
#[test]
def report_affine_usage_compiler : IO Bool := report_on "bench/src/affine_target.mo"

// ─── Corpus-wide sweep ─────────────────────────────────────────────
//
// The reports above measure CLOSURES: elaborate one entry file, tally
// every decl the elaboration produced. That was the right shape while
// `lang` was the only mote being measured, but Phase 3 of the
// enforcement plan asks for every mote `scripts/check-monad-tests.sh`
// grades, and closure reports cannot be summed: every mote's closure
// re-includes `init`/`std`/`lang`, so summing counts each shared module
// once per mote that depends on it. De-duping summed decls by NAME is
// also wrong, for a reason worth spelling out: names are NOT unique
// across modules. Every examples file has its own `main`, test names
// collide freely across files, and a name-keyed merge would silently
// merge those and under-count.
//
// So the sweep measures FILES instead. Elaborate every corpus file and
// tally only its OWN decls (`ElaboratedModules.target_decls`): each
// file is the target of exactly one elaboration, so the corpus total
// counts every decl exactly once — de-dup by construction, no
// (module_id, name) key needed. This also COVERS MORE than any
// closure report can: files no lib.mo re-exports (`lang`'s own
// typecheck/parser modules are not in `lang/src/lib.mo`'s closure, for
// one) still get measured, because they are the target of their own
// elaboration.
//
// Cost is bounded by `ModuleInfoCache`: one `elaborate_loaded_modules_
// cached` per file threads the cache to the next, so each module is
// parsed once per sweep rather than once per importer.

/// The sweep set — `scripts/check-monad-tests.sh`'s `corpus_dirs`
/// (line 458), the same eleven directories CI grades.
def corpus_dirs : List String :=
    ["init", "std", "examples", "lang", "cli", "llvm", "runtime", "motes",
     "slow_tests", "bench", "proofs"]

/// One corpus directory's measured totals, accumulated across the
/// files expand_check_paths found under it.
pub struct MoteTotal {
    label : String,
    files : I64,
    totals : Totals,
}

/// The threaded state of the whole sweep: the elaboration cache, the
/// combined (all-corpus) totals, the per-directory blocks pushed in
/// sweep order, and the in-progress directory block.
pub struct Sweep {
    cache : ModuleInfoCache,
    grand : Totals,
    motes : List MoteTotal,
    label : String,
    dir : Totals,
    dir_files : I64,
    failed : List String,
}

pub def Sweep.cache (s : Sweep) : ModuleInfoCache := s.cache

pub def Sweep.grand (s : Sweep) : Totals := s.grand

pub def Sweep.motes (s : Sweep) : List MoteTotal := s.motes

pub def Sweep.label (s : Sweep) : String := s.label

pub def Sweep.dir (s : Sweep) : Totals := s.dir

pub def Sweep.dir_files (s : Sweep) : I64 := s.dir_files

pub def Sweep.failed (s : Sweep) : List String := s.failed

pub def MoteTotal.label (m : MoteTotal) : String := m.label

pub def MoteTotal.files (m : MoteTotal) : I64 := m.files

pub def MoteTotal.totals (m : MoteTotal) : Totals := m.totals

def sweep_empty : Sweep :=
    { cache := module_info_cache_empty, grand := totals_empty, motes := List.empty,
      label := "", dir := totals_empty, dir_files := 0, failed := List.empty }

/// The sweep's own file, skipped: this test runs INSIDE
/// affine_report.mo, and elaborating the very module whose test is
/// executing hands the registry a second copy of it. Every other
/// re-elaboration is fine — the closure reports above already
/// re-elaborate `lang` while the harness holds its own copy — but the
/// self case is untested and buys nothing: this file's own #[test]s
/// contribute no corpus binders worth counting.
#[partial]
def sweep_file (f : String) (st : Sweep) : IO Sweep := do {
    if String.beq f "bench/src/affine_report.mo" then do { return st }
    else do { sweep_target f st }
}

/// The non-self case, hoisted out of the `else` arm: a `match` nested
/// inside an `if` arm inside a do-block trips the nested-match parse
/// trap, so each arm of the decision lives in its own def.
#[partial]
def sweep_target (f : String) (st : Sweep) : IO Sweep := do {
    let r : ElaboratedAndCache <- elaborate_loaded_modules_cached f false (Sweep.cache st) false;
    match r.elaborated {
        Result.err e => do {
            println ("  could not elaborate " ++ f ++ ": " ++ e);
            let out : Sweep := { st with cache := r.cache, failed := List.cons f (Sweep.failed st) };
            return out
        },
        Result.ok em => do {
            // Per-file, not per-run: each elaboration's scope is
            // that file's own view of the corpus.
            let ctors : HashMap String Bool := ctor_name_set em.scope;
            let borrows : HashMap String Bool := borrow_of_name_set em.scope;
            let dir : Totals := tally_decls ctors borrows em.scope em.target_decls (Sweep.dir st);
            let grand : Totals := tally_decls ctors borrows em.scope em.target_decls (Sweep.grand st);
            let out : Sweep :=
                { st with cache := r.cache, dir := dir, grand := grand,
                  dir_files := Sweep.dir_files st + 1 };
            return out
        },
    }
}

#[partial]
def sweep_files (files : List String) (st : Sweep) : IO Sweep := do {
    match files {
        List.empty => do { return st },
        List.cons f rest => do {
            let walked : Sweep <- sweep_file f st;
            sweep_files rest walked
        },
    }
}

#[partial]
def sweep_dir (d : String) (st : Sweep) : IO Sweep := do {
    // Annotated local, not a bare literal argument: `expand_check_paths
    // [d]` is exactly the argument-position literal that miscompiles.
    let one : List String := [d];
    let files : List String <- expand_check_paths one;
    let started : Sweep := { st with label := d, dir := totals_empty, dir_files := 0 };
    let finished : Sweep <- sweep_files files started;
    let mt : MoteTotal := { label := d, files := Sweep.dir_files finished, totals := Sweep.dir finished };
    let out : Sweep := { finished with motes := List.cons mt (Sweep.motes finished) };
    return out
}

#[partial]
def sweep_dirs (dirs : List String) (st : Sweep) : IO Sweep := do {
    match dirs {
        List.empty => do { return st },
        List.cons d rest => do {
            let walked : Sweep <- sweep_dir d st;
            sweep_dirs rest walked
        },
    }
}

/// One compact line per corpus directory — the full per-type breakdown
/// prints only for the combined total.
def print_mote_line (m : MoteTotal) : IO Unit := do {
    let t : Totals := MoteTotal.totals m;
    println ("  " ++ MoteTotal.label m
        ++ "  " ++ I64.to_string (MoteTotal.files m) ++ " files"
        ++ ", binders " ++ I64.to_string (Totals.binders t)
        ++ ", copy_required " ++ I64.to_string (Totals.diag_copy_required t)
        ++ ", value_used_after_move " ++ I64.to_string (Totals.diag_used_after_move t)
        ++ ", linear_unused " ++ I64.to_string (Totals.diag_linear_unused t)
        ++ ", borrowed " ++ I64.to_string (Totals.borrowed_uses t));
}

#[partial]
def print_mote_lines (ms : List MoteTotal) : IO Unit := do {
    match ms {
        List.empty => do { return Unit.unit },
        List.cons m rest => do {
            let _u : Unit <- print_mote_line m;
            print_mote_lines rest
        },
    }
}

/// The Phase 3 re-baseline: every `.mo` file under CI's `corpus_dirs`,
/// each counted exactly once (see the section header for why per-file
/// `target_decls` and not summed closures). Fails if any corpus file
/// fails to elaborate — the sweep script itself would be failing on the
/// same file, so hiding it here would only misreport the corpus as
/// cleaner than it is.
#[test]
def report_affine_usage_corpus : IO Bool := do {
    let on <- report_enabled;
    if Bool.not on then return true
    else do {
        let st : Sweep <- sweep_dirs corpus_dirs sweep_empty;
        println "";
        println "affine corpus sweep (per-file target_decls, de-duped by construction):";
        let _shown : Unit <- print_mote_lines (List.reverse (Sweep.motes st));
        let _grand : Bool <- print_totals "corpus (all corpus_dirs)" (Sweep.grand st);
        match Sweep.failed st {
            List.empty => do { return true },
            List.cons f rest => do {
                println ("  SWEEP FAILED to elaborate: " ++ f);
                let _rest : List String := rest;
                return false
            },
        }
    }
}

// ─── Tests for the aggregation itself ──────────────────────────────

def tally_of (count : I64) (typ : Term) : BinderUse :=
    { name := Identifier.id "x", kind := BinderKind.bk_lam, typ := typ, count := count,
      owning := count, ctor := Identifier.id "", pos := 0 - 1 }

def i64_type : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "I64"))

def term_type : Term := Term.var (0 - 1) (DebugName.named (Identifier.id "Term"))

#[test]
def test_type_head_name_peels_application_spine : Bool :=
    // `List Term` -- the head is what the binder holds.
    let applied : Term := Term.app (Term.var (0 - 1) (DebugName.named (Identifier.id "List"))) term_type in
    String.beq (type_head_name applied) "List"

#[test]
def test_type_head_name_reports_unknown_as_question : Bool :=
    String.beq (type_head_name Term.hole) "?"

/// An empty scope has no `Copy` instances at all, so the gate denies
/// every carrier. That is the fail-closed direction, and it is what the
/// aggregation tests below are built on: they check the tally's own
/// arithmetic, not instance resolution, which only a real corpus scope
/// can exercise (and which `report_affine_usage_compiler` does).
def probe_scope : Scope :=
    { module_id := ModulePath.mp (List.cons (Identifier.id "probe") List.empty),
      scope := scope_data_empty,
      parent := Option.none }

#[test]
def test_empty_scope_grants_no_copy : Bool :=
    not (binder_is_copy probe_scope i64_type)

#[test]
def test_tally_splits_the_three_buckets : Bool :=
    let us : List BinderUse :=
        List.cons (tally_of 0 term_type)
            (List.cons (tally_of 1 term_type)
                (List.cons (tally_of 3 term_type) List.empty)) in
    let t : Totals := tally_binders probe_scope us totals_empty in
    I64.beq (Totals.zero t) 1 && I64.beq (Totals.one t) 1 && I64.beq (Totals.many t) 1

#[test]
def test_tally_counts_every_overuse_as_non_copy_without_instances : Bool :=
    // With no `Copy` instances in scope the gate denies both, so both
    // count against the migration cost. The fail-closed direction,
    // measured through the tally rather than asserted at the gate.
    let us : List BinderUse :=
        List.cons (tally_of 2 i64_type) (List.cons (tally_of 2 term_type) List.empty) in
    let t : Totals := tally_binders probe_scope us totals_empty in
    I64.beq (Totals.many t) 2 && I64.beq (Totals.many_non_copy t) 2

#[test]
def test_tally_bump_increments_an_existing_name : Bool :=
    let once : List TypeTally := tally_bump "Term" List.empty in
    let twice : List TypeTally := tally_bump "Term" once in
    match twice {
        List.cons t rest => I64.beq (TypeTally.count t) 2 && I64.beq (List.length rest) 0,
        List.empty => false,
    }

#[test]
def test_pct_renders_one_decimal : Bool :=
    String.beq (pct 1 4) "25.0" && String.beq (pct 1 3) "33.3"

#[test]
def test_extract_max_takes_the_largest : Bool :=
    let small : TypeTally := { name := "a", count := 1 } in
    let big : TypeTally := { name := "b", count := 9 } in
    let ts : List TypeTally := List.cons small (List.cons big List.empty) in
    match extract_max ts {
        Option.some r =>
            match r {
                MaxSplit.mk best rest => String.beq (TypeTally.name best) "b" && I64.beq (List.length rest) 1,
            },
        Option.none => false,
    }
