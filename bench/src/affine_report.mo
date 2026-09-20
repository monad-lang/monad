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
/// "`#[test]`-driven, run it by hand, not every commit" mote, and it is
/// outside the pre-commit sweep (`devenv.nix` runs `test init std lang
/// examples`), so a report that takes a minute over `lang/` gates
/// nothing. Promote it to a subcommand if it earns one.
///
/// Run it with:
///
/// ```text
/// monad test bench/src/affine_report.mo
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
open IO {println}
use lang::module {ElaboratedModules, elaborate_loaded_modules}
use lang::types {Decl, Def, Term, show_identifier}
use lang::typecheck::usage {BinderUse, collect_binder_uses}
use std::list {length}

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
        Term.type_ u => "Type" ++ I64.to_string u,
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

/// The builtin-scalar approximation of `Copy` — see this file's own doc
/// comment for why it is an approximation and which way it errs.
///
/// These are the types Design B lists as getting compiler-provided
/// `Copy` instances (`quantitative-types.md`, *Copy policy for core
/// types*): scalars, `Bool`, `Char`, `Unit`. `String` is deliberately
/// absent — it is a heap buffer, and Design B says share it via a
/// borrow, not a copy.
def is_copy_approx (name : String) : Bool :=
    String.beq name "I64" || String.beq name "U64" || String.beq name "I32"
        || String.beq name "U32" || String.beq name "U8" || String.beq name "F64"
        || String.beq name "Bool" || String.beq name "Char" || String.beq name "Unit"

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
}

pub def Totals.binders (t : Totals) : I64 := t.binders

pub def Totals.zero (t : Totals) : I64 := t.zero

pub def Totals.one (t : Totals) : I64 := t.one

pub def Totals.many (t : Totals) : I64 := t.many

pub def Totals.many_non_copy (t : Totals) : I64 := t.many_non_copy

pub def Totals.by_type (t : Totals) : List TypeTally := t.by_type

def totals_empty : Totals :=
    { binders := 0, zero := 0, one := 0, many := 0, many_non_copy := 0, by_type := List.empty }

/// Fold one binder into the running totals. Accumulator-passing all the
/// way down, like every list walker in `lang/codegen/` — this runs over
/// whole modules, and the natural non-tail shape holds a native frame
/// per binder.
def tally_binder (u : BinderUse) (acc : Totals) : Totals :=
    let n : I64 := BinderUse.count u in
    let tname : String := type_head_name (BinderUse.typ u) in
    if I64.beq n 0 then
        { acc with binders := Totals.binders acc + 1, zero := Totals.zero acc + 1 }
    else if I64.beq n 1 then
        { acc with binders := Totals.binders acc + 1, one := Totals.one acc + 1 }
    else
        let non_copy : I64 :=
            if is_copy_approx tname then Totals.many_non_copy acc
            else Totals.many_non_copy acc + 1 in
        { acc with
            binders := Totals.binders acc + 1,
            many := Totals.many acc + 1,
            many_non_copy := non_copy,
            by_type := tally_bump tname (Totals.by_type acc) }

#[partial]
def tally_binders (us : List BinderUse) (acc : Totals) : Totals :=
    match us {
        List.empty => acc,
        List.cons u rest => tally_binders rest (tally_binder u acc),
    }

// ─── Walking a module's defs ───────────────────────────────────────

def def_term (d : Def) : Term := d.term

#[partial]
def tally_decls (ds : List Decl) (acc : Totals) : Totals :=
    match ds {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Decl.def_d def_ => tally_decls rest (tally_binders (collect_binder_uses (def_term def_)) acc),
                // A macro body is a template, not code that runs; its
                // binders are not runtime owners.
                Decl.def_macro_d _def => tally_decls rest acc,
                // A scoped open wraps one real decl. Codegen ignores
                // these today (`Decl.scoped_open_d`'s own doc comment),
                // so the report does too rather than disagree with the
                // backend it is sizing work for.
                Decl.scoped_open_d _path _filter _inner => tally_decls rest acc,
                _ => tally_decls rest acc,
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
    println "  ^ upper bound on the migration cost (scalar approximation of Copy)";
    println "  2+ uses by type, most first:";
    let _printed : I64 <- print_top (Totals.by_type t) 20;
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
    let r : Result String ElaboratedModules <- elaborate_loaded_modules path false false;
    match r {
        Result.err e => do {
            println ("affine report: could not elaborate " ++ path ++ ": " ++ e);
            return false
        },
        Result.ok em => do {
            let totals : Totals := tally_decls em.elaborated_decls totals_empty;
            print_totals path totals
        }
    }
}

#[test]
def report_affine_usage_std : IO Bool := report_on "std/src/list.mo"

#[test]
def report_affine_usage_lang : IO Bool := report_on "lang/src/typecheck/traverse.mo"

/// The headline number: the self-hosted compiler's own dependency
/// closure. `lang/src/lib.mo` is the compiler as a library, so one
/// elaboration here covers prelude, init, std and every compiler module
/// -- the corpus the experiment actually has to carry.
#[test]
def report_affine_usage_compiler : IO Bool := report_on "lang/src/lib.mo"

// ─── Tests for the aggregation itself ──────────────────────────────

def tally_of (count : I64) (typ : Term) : BinderUse :=
    { name := Identifier.id "x", kind := BinderKind.bk_lam, typ := typ, count := count }

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

#[test]
def test_scalar_is_copy_but_string_is_not : Bool :=
    is_copy_approx "I64" && not (is_copy_approx "String")

#[test]
def test_tally_splits_the_three_buckets : Bool :=
    let us : List BinderUse :=
        List.cons (tally_of 0 term_type)
            (List.cons (tally_of 1 term_type)
                (List.cons (tally_of 3 term_type) List.empty)) in
    let t : Totals := tally_binders us totals_empty in
    I64.beq (Totals.zero t) 1 && I64.beq (Totals.one t) 1 && I64.beq (Totals.many t) 1

#[test]
def test_tally_excludes_scalars_from_the_migration_cost : Bool :=
    // Two over-used binders, one `I64` and one `Term`. Only the `Term`
    // one is a migration cost -- the scalar gets a builtin Copy.
    let us : List BinderUse :=
        List.cons (tally_of 2 i64_type) (List.cons (tally_of 2 term_type) List.empty) in
    let t : Totals := tally_binders us totals_empty in
    I64.beq (Totals.many t) 2 && I64.beq (Totals.many_non_copy t) 1

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
