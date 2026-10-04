/// A one-shot Phase 6 probe (Milestone 6's per-mote promotion): print
/// the actual `--affine`
/// diagnostics for a named file, the same ones
/// `monad check --affine <file>` would fail on, with binder names —
/// the corpus sweep reports per-mote totals, and fixing a mote's
/// violations needs to know WHICH binders they are.
///
/// Run it with:
///
/// ```text
/// MONAD_AFFINE_REPORT=1 monad test bench/src/affine_probe.mo
/// ```
///
/// Every test below elaborates `runtime/src/natives.mo` with its whole
/// closure, so each one starts with a gate that early-returns unless
/// MONAD_AFFINE_REPORT is set (the `std/ansi.mo` NO_COLOR pattern) —
/// `scripts/check-monad-tests.sh` sweeps this mote, and the probe is
/// meant to run by hand, not every commit.
use std::io {IO.println}
open IO {get_env, println}
use lang::module {
  ElaboratedAndCache, FileCheckAndCache, FileCheckResult, check_file_cached_affine,
  elaborate_loaded_modules_cached, module_info_cache_empty,
}
use lang::scope {scope_globals, scope_instance_candidates}
use lang::typecheck::copy_class {copy_verdict, CopyVerdict}
use lang::types {DebugName, Identifier, NamePath, ScopeData, Term}
use std::list {List.length}

#[partial]
def print_all (diags : List String) : IO I64 :=
    match diags {
        List.empty => do { return 0 },
        List.cons d rest => do {
            println d;
            print_all rest
        }
    }

def env_flag_set (v : Option String) : Bool :=
    match v {
        some _ => true,
        none => false
    }

def report_enabled : IO Bool := do {
    let v <- get_env "MONAD_AFFINE_REPORT";
    return (env_flag_set v)
}

#[test]
def report_affine_diagnostics_of_file : IO Bool := do {
    let on <- report_enabled;
    if Bool.not on then return true
    else do {
        let checked <- check_file_cached_affine module_info_cache_empty "runtime/src/natives.mo" false;
        match checked {
            FileCheckAndCache.mk result _cache =>
                match result {
                    FileCheckResult.mk path diags => do {
                        println ("affine diagnostics for " ++ path ++ ":");
                        let n <- print_all diags;
                        println ("(" ++ I64.to_string (List.length diags) ++ " total)");
                        // A probe reports, never fails: the mote is not
                        // promoted yet, so violations are expected.
                        return true
                    }
                }
        }
    }
}

/// Why do binders of a scalar type count as non-Copy when init
/// declares `instance Copy I64`? Print the verdict the elaborated
/// scope of a real file actually gives, plus how many Copy-instance
/// candidates the scope holds at all.
#[test]
def probe_copy_resolution_in_a_real_scope : IO Bool := do {
    let on <- report_enabled;
    if Bool.not on then return true
    else do {
        let r : ElaboratedAndCache <- elaborate_loaded_modules_cached "runtime/src/natives.mo" false module_info_cache_empty false;
        match r.elaborated {
            Result.err e => do {
                println ("could not elaborate: " ++ e);
                return false
            },
            Result.ok em => do {
                let i64_type : Term := Term.var 0 (DebugName.named (Identifier.id "I64"));
                let copy_name : NamePath := NamePath.npath (List.cons (Identifier.id "Copy") List.empty);
                let candidates : I64 := List.length (scope_instance_candidates (scope_globals em.scope) copy_name);
                println ("Copy instance candidates in scope: " ++ I64.to_string candidates);
                println ("verdict for I64: " ++
                    match copy_verdict em.scope i64_type {
                        CopyVerdict.cv_copy => "copy",
                        CopyVerdict.cv_not_copy => "not_copy",
                        CopyVerdict.cv_ambiguous => "ambiguous",
                    });
                return true
            }
        }
    }
}
#[partial]
def np1 (nm : String) : NamePath := NamePath.npath (List.cons (Identifier.id nm) List.empty)

#[partial]
def np3 (a : String) (b : String) (c : String) : NamePath :=
    NamePath.npath (List.cons (Identifier.id a) (List.cons (Identifier.id b) (List.cons (Identifier.id c) List.empty)))

#[test]
def probe_instance_buckets_in_a_real_scope : IO Bool := do {
    let on <- report_enabled;
    if Bool.not on then return true
    else do {
        let r : ElaboratedAndCache <- elaborate_loaded_modules_cached "runtime/src/natives.mo" false module_info_cache_empty false;
        match r.elaborated {
            Result.err e => do {
                println ("could not elaborate: " ++ e);
                return false
            },
            Result.ok em => do {
                let sd : ScopeData := scope_globals em.scope;
                let bare : I64 := List.length (scope_instance_candidates sd (np1 "Copy"));
                let qualified : I64 := List.length (scope_instance_candidates sd (np3 "init" "copy" "Copy"));
                println ("Copy candidates under bare `Copy`: " ++ I64.to_string bare);
                println ("Copy candidates under `init copy Copy`: " ++ I64.to_string qualified);
                return true
            }
        }
    }
}
