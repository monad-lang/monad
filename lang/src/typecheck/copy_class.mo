/// Is a type `Copy`? — the gate that decides whether a binder may be
/// used more than once.
///
/// Milestone 2 of the affine-by-default experiment
/// (*Design B: Viability
/// Experiment*). Under Design B every binder is affine by default and
/// **`Copy A` resolving is the only route to ω**, so this one predicate
/// is what stands between a program and a use-after-move. It is
/// deliberately small and deliberately paranoid.
///
/// ## Real instances, not a table
///
/// The verdict comes from resolving a genuine `Copy` instance
/// (`init/src/copy.mo`) through the scope's own instance registry, so a
/// user type can opt in with `instance Copy T { ... }` and the gate is
/// extensible rather than closed.
///
/// This module deliberately does NOT import `init::copy`. Importing it
/// here looks like it should put the instances in scope and does not:
/// they reach a scope only via the elaborated dependency closure of
/// whatever is being checked, and `lang/src/lib.mo` re-exports a small
/// surface that never reaches this file. Measured, not assumed — see
/// `bench/src/affine_target.mo`, which records the experiment that
/// established it.
///
/// A concern was raised and checked before this was built: the corpus
/// documents a "first-registered-instance-wins" fragility in instance
/// resolution. That is real, but it is the **evaluator's**
/// `resolve_class_method_instance` — a different path.
/// `find_matching_instance` (`lang/src/scope.mo`) does match on the
/// carrier, preferring fully-concrete instances and falling back to
/// wildcards. It is sound to build on. What it does *not* do is notice
/// when two instances both match, which is why this module counts
/// matches itself rather than taking the first.
///
/// ## Two rules that make it safe
///
/// **Fail closed.** Anything this cannot resolve confidently — an
/// unknown head, a bare type variable, a hole, a function type —
/// registers as NOT Copy. The asymmetry is the whole point: a missed
/// `Copy` costs one redundant release at run time, while a wrongly
/// granted `Copy` is a double free. Every uncertain case must fall on
/// the cheap side.
///
/// **Ambiguity is an answer, not a coin flip.** Two concrete instances
/// matching the same carrier is reported as `cv_ambiguous`, never
/// silently resolved to whichever the scan reached first. `mk`-style
/// collisions are endemic here — `lang/src/typecheck/usage.mo`'s own
/// attribution had to fail closed on exactly this — and a wrong pick in
/// *this* predicate frees memory that is still live.
use lib::types {Identifier, Instance, NamePath, Scope, Term, term_peel}
use lib::scope {
  instance_args_match_carrier, instance_is_fully_concrete, instance_wildcard_names,
  scope_globals, scope_instance_candidates, term_is_wildcard,
}

/// The gate's verdict. Three outcomes, not two, because "I could not
/// tell" and "no" need to be distinguishable by the caller even though
/// both deny ω.
pub type CopyVerdict {
    /// A single instance matched: the binder may be used freely.
    cv_copy,
    /// No instance matched. Affine.
    cv_not_copy,
    /// Two or more concrete instances matched the same carrier.
    /// Affine, and worth reporting — it means the program has a real
    /// instance collision that some other resolution path is currently
    /// deciding arbitrarily.
    cv_ambiguous,
}

pub def copy_verdict_grants_omega (v : CopyVerdict) : Bool :=
    match v {
        CopyVerdict.cv_copy => true,
        CopyVerdict.cv_not_copy => false,
        CopyVerdict.cv_ambiguous => false,
    }

/// The class this module resolves. A `NamePath` of one segment, matching
/// how every other constructor/class lookup in the checker builds one.
def copy_class_name : NamePath := NamePath.npath (List.cons (Identifier.id "Copy") List.empty)

/// Does `typ` have a `Copy` instance in `scope`?
pub def is_copy (scope : Scope) (typ : Term) : Bool :=
    copy_verdict_grants_omega (copy_verdict scope typ)

/// The full verdict, for callers that want to distinguish "no" from
/// "could not tell".
pub def copy_verdict (scope : Scope) (typ : Term) : CopyVerdict :=
    let carrier : Term := carrier_of typ in
    if not (carrier_is_resolvable carrier) then CopyVerdict.cv_not_copy
    else
        let candidates : List Instance := scope_instance_candidates (scope_globals scope) copy_class_name in
        let concrete : List Instance := keep_admissible candidates in
        let matches : I64 := count_matching concrete carrier in
        if I64.beq matches 1 then CopyVerdict.cv_copy
        else if I64.gt matches 1 then CopyVerdict.cv_ambiguous
        else CopyVerdict.cv_not_copy

/// The head of a type application, peeled of `ctx`.
///
/// `Copy (Pair A B)` is decided by the instance for `Pair`, so the
/// carrier handed to instance matching is the spine head, not the whole
/// applied type. A CONSTRAINED parametric instance
/// (`instance [Copy A] [Copy B] Copy (Pair A B)`) would need to check
/// those constraints against the real type arguments the carrier
/// erased here — that resolution is not implemented, so such an
/// instance keeps falling through to affine. An UNCONSTRAINED one
/// (`instance {A : Type} Copy (Borrow A)`) needs no such check — it
/// holds for every `A` — and `instance_unconditionally_copy` below is
/// what admits exactly that shape without pretending to resolve the
/// constrained one.
#[partial]
def carrier_of (t : Term) : Term :=
    match t {
        Term.ctx _loc inner => carrier_of inner,
        Term.app callee _arg => carrier_of callee,
        _ => t,
    }

/// Can this carrier be resolved against at all?
///
/// A hole, a function type, a universe or a bare de-Bruijn type variable
/// carries no name to match an instance against. Each is a case where
/// the honest answer is "unknown", and unknown means affine.
///
/// `Term.var` with a `named` `DebugName` IS resolvable — that is how an
/// ordinary named type reference arrives here (`I64`, `Term`, `String`).
/// A `var` with no name is not.
def carrier_is_resolvable (t : Term) : Bool :=
    match t {
        Term.var _idx dbg =>
            match dbg {
                DebugName.named _id => true,
                DebugName.unnamed => false,
            },
        Term.con _c => true,
        Term.ntv _n => true,
        // A function type is never Copy under Design B, and a hole or a
        // universe names nothing. All affine.
        Term.pi _arg _ret => false,
        Term.forall _dbg _kind _body => false,
        Term.lam _dbg _typ _body => false,
        Term.hole => false,
        Term.sort _level => false,
        Term.lit _v => false,
        Term.quote_ _inner => false,
        Term.var_macro _idx _dbg => false,
        Term.app _callee _arg => false,
        Term.ctx _loc _inner => false,
    }

/// Kept for `instance_admissible` below to fall back on — every
/// literally concrete instance is still admitted exactly as before.
#[partial]
def keep_admissible (instances : List Instance) : List Instance :=
    keep_admissible_go instances List.empty

#[partial]
def keep_admissible_go (instances : List Instance) (acc : List Instance) : List Instance :=
    match instances {
        List.empty => acc,
        List.cons ins rest =>
            if instance_admissible ins then keep_admissible_go rest (List.cons ins acc)
            else keep_admissible_go rest acc,
    }

/// Is this instance safe to match against a carrier WITHOUT resolving
/// any obligation this module cannot discharge?
///
/// `instance_is_fully_concrete` (`lang/scope.mo`) is the right filter
/// for the class-method dispatch it was built to protect — calling
/// `Show.show` through a wildcard-headed instance needs the REAL type
/// argument to pick field-wise behaviour, so an unresolved wildcard
/// there is a genuine gap. `Copy` can be different: a builtin instance
/// like `instance {A : Type} Copy (Borrow A)` is true for every `A`
/// without ever inspecting it — the body duplicates the `Borrow`
/// marker, not the value underneath — so there is no missing
/// information to fail closed over, and excluding it (what
/// `instance_is_fully_concrete` alone would do) denies `Copy` to
/// something that genuinely has it.
///
/// So an instance is admitted here under either of two conditions:
///
/// - it is fully concrete (unchanged from before), or
/// - it carries **no class constraints** — a `[Copy A]` clause is a
///   real recursive obligation this module does not resolve, so an
///   instance with one is excluded exactly as it was — **and** its
///   carrier's own applied HEAD is not itself one of its wildcards.
///   That second clause is what stops an accidental blanket
///   `instance {A : Type} Copy A` (head IS the wildcard) from granting
///   ω to every type in the language; only a wildcard NESTED inside a
///   concrete head (`Borrow`'s own `A`) is admitted.
def instance_admissible (ins : Instance) : Bool :=
    instance_is_fully_concrete ins || instance_unconditionally_copy ins

def instance_unconditionally_copy (ins : Instance) : Bool :=
    match ins {
        Instance.mk _name _cls constraints args _vis implicit_params _defs =>
            List.is_empty constraints
                && not (List.is_empty implicit_params)
                && carrier_head_is_concrete (instance_wildcard_names ins) args,
    }

/// `args` is the class's own parameter list, instantiated at this
/// instance — one element for `class Copy A`. Its outermost applied
/// head must name a real type constructor, not a wildcard; see
/// `instance_unconditionally_copy`'s doc comment for why.
def carrier_head_is_concrete (wildcards : List Identifier) (args : List Term) : Bool :=
    match args {
        List.cons a _rest => not (term_is_wildcard wildcards (spine_head a)),
        List.empty => false,
    }

/// Like `carrier_of`, minus the `Copy`-specific resolvability question —
/// just the structural "peel `ctx`, walk to the outermost applied
/// head" that both this module's carrier AND an instance's own
/// declared arg need.
#[partial]
def spine_head (t : Term) : Term :=
    match term_peel t {
        Term.app f _a => spine_head f,
        _ => t,
    }

/// How many of `instances` match `carrier`.
///
/// Counts rather than short-circuits on the first hit, which is the
/// whole difference from `find_matching_instance`: one match grants ω,
/// two must not.
#[partial]
def count_matching (instances : List Instance) (carrier : Term) : I64 :=
    count_matching_go instances carrier 0

#[partial]
def count_matching_go (instances : List Instance) (carrier : Term) (acc : I64) : I64 :=
    match instances {
        List.empty => acc,
        List.cons ins rest =>
            if instance_args_match_carrier ins carrier
            then count_matching_go rest carrier (acc + 1)
            else count_matching_go rest carrier acc,
    }

// ─── Tests ─────────────────────────────────────────────────────────
//
// These cover the fail-closed rules, which are the part that must not
// regress: every one of them is a case where saying "Copy" would free
// live memory. Resolution against a real populated scope is exercised
// by `bench/src/affine_report.mo`, which runs this over the whole
// corpus and prints what it decided.

def named_type (nm : String) : Term := Term.var (0 - 1) (DebugName.named (Identifier.id nm))

#[test]
def test_a_named_type_is_resolvable : Bool :=
    carrier_is_resolvable (named_type "I64")

#[test]
def test_a_hole_is_not_resolvable : Bool :=
    not (carrier_is_resolvable Term.hole)

#[test]
def test_a_function_type_is_never_copy : Bool :=
    // Design B: function/Pi types are never Copy.
    not (carrier_is_resolvable (Term.pi (named_type "I64") (named_type "I64")))

#[test]
def test_an_unnamed_variable_is_not_resolvable : Bool :=
    // No name to match an instance against, so the answer is unknown,
    // and unknown is affine.
    not (carrier_is_resolvable (Term.var 0 DebugName.unnamed))

#[test]
def test_carrier_peels_the_application_spine : Bool :=
    // `Pair A B` is decided by the instance for `Pair`.
    let applied : Term := Term.app (Term.app (named_type "Pair") (named_type "A")) (named_type "B") in
    carrier_is_resolvable (carrier_of applied)

#[test]
def test_carrier_peels_ctx : Bool :=
    carrier_is_resolvable (carrier_of (Term.ctx (Location.mk 0 1 1) (named_type "I64")))

#[test]
def test_count_matching_of_nothing_is_zero : Bool :=
    I64.beq (count_matching List.empty (named_type "I64")) 0

#[test]
def test_ambiguous_denies_omega : Bool :=
    // The rule that matters most: two matches must not grant sharing.
    not (copy_verdict_grants_omega CopyVerdict.cv_ambiguous)

#[test]
def test_not_copy_denies_omega : Bool :=
    not (copy_verdict_grants_omega CopyVerdict.cv_not_copy)

#[test]
def test_copy_grants_omega : Bool :=
    copy_verdict_grants_omega CopyVerdict.cv_copy
