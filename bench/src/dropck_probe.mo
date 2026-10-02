/// Corpus-scale sanity probe for `lang/typecheck/dropck.mo`'s
/// drop-point analysis -- not a permanent report, unlike
/// `affine_report.mo`. `drop_leaves` concatenates a list PER BRANCH
/// POINT (`if`/`match`), which is a genuinely different growth shape
/// from `usage.mo`'s own max-combining walk -- a term with many
/// nested/wide matches could in principle produce a large leaf list
/// per binder. This exists to answer, with a real number instead of
/// assumption, whether that is actually a problem on real code before
/// anything is built on top of this module.
///
/// Run it with:
///
/// ```text
/// MONAD_AFFINE_REPORT=1 monad test bench/src/dropck_probe.mo
/// ```
///
/// It elaborates `lang/src/lib.mo`'s whole closure (~90 s), so the test
/// starts with a gate that early-returns unless MONAD_AFFINE_REPORT is
/// set (the `std/ansi.mo` NO_COLOR pattern) — the sweep that runs this
/// mote's #[test]s should not pay for a run-by-hand probe.
use lang::module {ElaboratedModules, elaborate_loaded_modules}
use lang::types {Decl, Def, Term}
use lang::typecheck::usage {ctor_name_set, borrow_of_name_set}
use lang::typecheck::dropck {DropInfo, collect_drop_info}
use std::io {IO.println}
open IO {get_env, println}
use std::map {HashMap}
use std::bench {Bench.now}
use std::list {List.length}

def def_term (d : Def) : Term := d.term

pub struct Stats { binders : I64, leaves : I64, max_leaves : I64, always : I64, never : I64, mixed : I64 }

pub def Stats.binders (s : Stats) : I64 := s.binders
pub def Stats.leaves (s : Stats) : I64 := s.leaves
pub def Stats.max_leaves (s : Stats) : I64 := s.max_leaves
pub def Stats.always (s : Stats) : I64 := s.always
pub def Stats.never (s : Stats) : I64 := s.never
pub def Stats.mixed (s : Stats) : I64 := s.mixed

def stats_empty : Stats := { binders := 0, leaves := 0, max_leaves := 0, always := 0, never := 0, mixed := 0 }

def fold_info (d : DropInfo) (acc : Stats) : Stats :=
    let n : I64 := List.length (DropInfo.leaves d) in
    let bucket : Stats :=
        if DropInfo.always_drop d then { acc with always := Stats.always acc + 1 }
        else if DropInfo.never_drop d then { acc with never := Stats.never acc + 1 }
        else { acc with mixed := Stats.mixed acc + 1 } in
    { bucket with
        binders := Stats.binders bucket + 1,
        leaves := Stats.leaves bucket + n,
        max_leaves := if I64.gt n (Stats.max_leaves bucket) then n else Stats.max_leaves bucket }

#[partial]
def fold_infos (infos : List DropInfo) (acc : Stats) : Stats :=
    match infos {
        List.empty => acc,
        List.cons d rest => fold_infos rest (fold_info d acc),
    }

#[partial]
def walk_decls (ctors : HashMap String Bool) (borrows : HashMap String Bool) (ds : List Decl) (acc : Stats) : Stats :=
    match ds {
        List.empty => acc,
        List.cons d rest =>
            match d {
                Decl.def_d def_ => walk_decls ctors borrows rest
                    (fold_infos (collect_drop_info ctors borrows (def_term def_)) acc),
                _ => walk_decls ctors borrows rest acc,
            },
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
def probe_dropck_on_the_compiler_itself : IO Bool := do {
    let on <- report_enabled;
    if Bool.not on then return true
    else do {
        let t0 : I64 <- Bench.now;
        let r : Result String ElaboratedModules <- elaborate_loaded_modules "lang/src/lib.mo" false false;
        match r {
            Result.err e => do { println ("probe failed: " ++ e); return false },
            Result.ok em => do {
                let ctors : HashMap String Bool := ctor_name_set em.scope;
                let borrows : HashMap String Bool := borrow_of_name_set em.scope;
                let stats : Stats := walk_decls ctors borrows em.elaborated_decls stats_empty;
                let t1 : I64 <- Bench.now;
                println ("dropck probe over lang/src/lib.mo's closure:");
                println ("  binders        " ++ I64.to_string (Stats.binders stats));
                println ("  total leaves   " ++ I64.to_string (Stats.leaves stats));
                println ("  max leaves/one " ++ I64.to_string (Stats.max_leaves stats));
                println ("  always_drop    " ++ I64.to_string (Stats.always stats));
                println ("  never_drop     " ++ I64.to_string (Stats.never stats));
                println ("  mixed (per-arm)" ++ I64.to_string (Stats.mixed stats));
                println ("  elapsed_ms     " ++ I64.to_string (t1 - t0));
                return true
            }
        }
    }
}
