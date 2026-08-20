use lang.core_eval {basic_native_table}
use lang.core_ir {CoreIr, IrLit, MatchArm}
use lang.core_value {GlobalDef, GlobalTable, NativeTable}
use lang.scope {
  build_scope_from_decls, modpath_eq, scope_data_empty, scope_find_inductive,
  scope_globals, scope_resolve_name,
}
use lang.types {
  Con, Decl, Def, DebugName, Identifier, Inductive, InductConstructor, Literal,
  MatchCase, ModulePath, Native, Scope, ScopeDef, Term,
}
use lang.typecheck.infer {empty_locals}

/// Lowers Monad's checked, de-Bruijn `Term` (`lang/types.mo`) to
/// `CoreIr` (`lang/core_ir.mo`), mirroring `core/src/lower_core_ir.rs`
/// (Rust). This is the missing piece the former self-hosted evaluator
/// never had: real global resolution (the former `lower_v0` sent every
/// unresolved name to a constant placeholder, `EvalTerm.econst 0`) and
/// real `if`/`match` compilation (`lower_v0` hard-stubbed `if` to the
/// literal `true` and `match` to an empty recursor, unconditionally).
///
/// **Whole-program flattening without mutable state.** Rust's
/// `lower_core_ir::lower_program` builds `GlobalTable` by mutating an
/// intern table as it walks defs. This module instead threads a
/// `LowerAcc` (an interned `seen: List ModulePath` plus the `done: List
/// GlobalDef` lowered so far, in the same order) through every lowering
/// call — the same functional-state-passing shape `lang/core_eval.mo`
/// uses for `GlobalCache`. A free variable reference *interns* its
/// target path (assigning it a stable index immediately, without
/// lowering its body yet — see `intern_path`); a separate worklist pass
/// (`process_pending`) then lowers each interned path's body in turn,
/// which may itself intern further, not-yet-seen paths. Because new
/// paths are always appended to the end of `seen` and `done` is built in
/// strict processing order, `done`'s `i`-th entry is always the lowered
/// form of `seen`'s `i`-th entry once `process_pending` reaches a fixed
/// point — `done`'s length no longer growing.
///
/// **Def bodies come from an explicit `List Def`, not `ScopeDef.body`.**
/// `lang/scope.mo`'s `build_scope_def` (confirmed directly) always
/// stores `body := Term.hole` in the `ScopeDef` it adds to scope --
/// scope-building in this codebase was never wired up to actually carry
/// a def's real checked body, only its existence/name for resolution
/// purposes. So `LowerCtx` below carries a `Scope` (used only for what
/// it *is* reliable for: `scope_resolve_name`'s name/path resolution --
/// its returned `ScopeDef.name`, not `.body` -- and
/// `scope_find_inductive`/inductive-constructor-order lookups, both of
/// which store their real payload correctly) alongside a separate flat
/// `List Def` that this module queries directly (`find_def_body`) for
/// actual lowerable bodies.
///
/// **Free-variable resolution still reuses `scope_resolve_name` for name
/// identity**, just not for body content. The checker
/// (`lang/typecheck/infer.mo`'s `type_check_free_var`) leaves an
/// unresolved name as `Term.var sentinel (DebugName.named id)` -- it
/// doesn't bake a resolved path into `Term` itself. This module
/// re-resolves such a name via `scope_resolve_name (NameRef.nid id)
/// scope empty_locals` to obtain its canonical `ModulePath` (for `Def`
/// lookup and interning) -- passing an *empty* `LocalScope` is safe
/// specifically because `idx == sentinel` already proves (by the
/// checker's own construction) that no local binder shadows `id` at this
/// position, so the local-shadowing lookup `scope_resolve_name` would
/// otherwise perform can only ever come up empty here regardless of what
/// `locals` value is supplied.
///
/// **Not attempted**: point-free constructor/native references (a
/// constructor or native used as a bare value, never applied) are not
/// specially resolved -- `lower_one_global` only handles ordinary `Def`
/// bodies found in `LowerCtx`'s `defs`; anything not found there becomes
/// `gd_unresolved`, mirroring Rust's `GlobalDef::Unresolved` fallback.
/// Constructor holes (`Con`'s sparse `List (Option Term)`) are only
/// handled as a filled-prefix-then-`None`-suffix shape (ordinary partial
/// application); a hole appearing *before* a filled argument would need
/// eta-expansion to preserve left-to-right order and is reported as a
/// `LowerError` instead.

/// What this pass needs to resolve names against: a `Scope` (for
/// `scope_resolve_name`/`scope_find_inductive`'s reliable parts -- name
/// identity and inductive/constructor structure) plus the flat `List
/// Def` giving real bodies (see this module's doc comment).
type LowerCtx {
  lower_ctx (scope: Scope) (defs: List Def),
}

def ctx_scope (ctx : LowerCtx) : Scope :=
  match ctx {
    LowerCtx.lower_ctx s _ => s,
  }

def ctx_defs (ctx : LowerCtx) : List Def :=
  match ctx {
    LowerCtx.lower_ctx _ d => d,
  }

#[partial]
def find_def_body (defs : List Def) (path : ModulePath) : Option Term :=
  match defs {
    List.empty => Option.none,
    List.cons d rest =>
      match d {
        Def.mk name _typ term _constraints _attrs _vis =>
          if modpath_eq name path
          then Option.some term
          else find_def_body rest path,
      },
  }

type LowerError {
  le_unresolved_name (name: Identifier),
  le_unresolved_module_path (path: ModulePath),
  le_unknown_inductive (path: ModulePath),
  le_unknown_constructor (path: ModulePath),
  le_unknown_native (name: Identifier),
  /// `Term.forall`/`pi`/`type_`/`hole` reached at lowering time -- these
  /// are type-level-only and should never occur in a well-typed
  /// runtime-relevant subterm.
  le_type_level_term,
  /// A constructor's `args : List (Option Term)` had a hole before a
  /// filled slot -- see this module's own doc comment.
  le_con_hole_before_filled_arg,
}

/// Accumulates whole-program global discovery + lowering. See this
/// module's doc comment.
type LowerAcc {
  lower_acc (seen: List ModulePath) (done: List GlobalDef),
}

def lower_acc_empty : LowerAcc := LowerAcc.lower_acc List.empty List.empty

// ─── Path interning ──────────────────────────────────────────────────

#[partial]
def modpath_index_from (i : I64) (path : ModulePath) (paths : List ModulePath) : Option I64 :=
  match paths {
    List.empty => Option.none,
    List.cons hd rest =>
      if modpath_eq path hd
      then Option.some i
      else modpath_index_from (i + 1) path rest,
  }

def modpath_index (path : ModulePath) (paths : List ModulePath) : Option I64 :=
  modpath_index_from 0 path paths

/// Assign (or reuse) a stable global index for `path` -- does not lower
/// its body; that happens later, in `process_pending`.
def intern_path (path : ModulePath) (acc : LowerAcc) : Pair I64 LowerAcc :=
  match acc {
    LowerAcc.lower_acc seen done =>
      match modpath_index path seen {
        Option.some idx => Pair.pair idx acc,
        Option.none => Pair.pair (List.length seen) (LowerAcc.lower_acc (List.append seen [path]) done),
      },
  }

def single_segment_path (id : Identifier) : ModulePath := ModulePath.mp [id]

// ─── The Result-plus-threaded-accumulator "monad" this module runs in ──

def lower_ok (ir : CoreIr) (acc : LowerAcc) : Pair (Result LowerError CoreIr) LowerAcc :=
  Pair.pair (Result.ok ir) acc

def lower_err (e : LowerError) (acc : LowerAcc) : Pair (Result LowerError CoreIr) LowerAcc :=
  Pair.pair (Result.err e) acc

def lower_then
    (outcome : Pair (Result LowerError CoreIr) LowerAcc)
    (f : CoreIr -> LowerAcc -> Pair (Result LowerError CoreIr) LowerAcc)
    : Pair (Result LowerError CoreIr) LowerAcc :=
  match outcome {
    Pair.pair r acc =>
      match r {
        Result.ok ir => f ir acc,
        Result.err e => Pair.pair (Result.err e) acc,
      },
  }

// ─── Free-variable / global resolution ──────────────────────────────

def sentinel : I64 := -1

def lower_resolved_name (sdef : ScopeDef) (acc : LowerAcc) : Pair (Result LowerError CoreIr) LowerAcc :=
  match sdef {
    ScopeDef.mk name _module _sig _body =>
      match intern_path name acc {
        Pair.pair idx acc1 => lower_ok (CoreIr.global idx) acc1,
      },
  }

def lower_free_var (ctx : LowerCtx) (dbg : DebugName) (acc : LowerAcc) : Pair (Result LowerError CoreIr) LowerAcc :=
  match dbg {
    DebugName.named id =>
      match scope_resolve_name (NameRef.nid id) (ctx_scope ctx) empty_locals {
        Result.ok sdef => lower_resolved_name sdef acc,
        Result.err _ => lower_err (LowerError.le_unresolved_name id) acc,
      },
    DebugName.unnamed => lower_err (LowerError.le_unresolved_name (Identifier.id "<unnamed>")) acc,
  }

// ─── if / match -> match_ ────────────────────────────────────────────

/// `Bool { true, false }` (`init/prelude.mo`) -- `true` is declared
/// first, so tag 0; `false` is tag 1. Matches `lang/core_eval.mo`'s
/// `bool_value` -- both must agree, since natives (`i64_lt`, ...) return
/// values built by `bool_value` at runtime, and this is the tag `if`
/// dispatches on.
#[partial]
def lower_if (ctx : LowerCtx) (cond : Term) (then_ : Term) (else_ : Term) (acc : LowerAcc) : Pair (Result LowerError CoreIr) LowerAcc :=
  lower_then (lower_term ctx cond acc) (fn cir => fn acc1 =>
    lower_then (lower_term ctx then_ acc1) (fn tir => fn acc2 =>
      lower_then (lower_term ctx else_ acc2) (fn eir => fn acc3 =>
        lower_ok (CoreIr.match_ cir [MatchArm.arm 0 tir, MatchArm.arm 0 eir]) acc3)))

// `ScopeData.inductives` is a `HashMap ModulePath Inductive` (see its own
// doc comment in `lang/types.mo`) -- `find_inductive_by_case_name` below
// needs to scan by CONSTRUCTOR, not by the map's own by-type-name key,
// so this still has to flatten to a plain `List Inductive` first via
// `HashMap.to_list` + dropping each pair's key.
def scope_all_inductives (s : Scope) : List Inductive :=
  match scope_globals s {
    ScopeData.mk _ _ _ inds _ _ _ _ => inductive_pairs_values (HashMap.to_list inds),
  }

def inductive_pairs_values (pairs : List (Pair ModulePath Inductive)) : List Inductive :=
  match pairs {
    List.empty => List.empty,
    List.cons p rest =>
      match p {
        Pair.pair _ ind => List.cons ind (inductive_pairs_values rest),
      },
  }

def constructor_simple_name_eq (c : InductConstructor) (name : Identifier) : Bool :=
  match c {
    InductConstructor.mk cname _ _ => modpath_eq cname (single_segment_path name),
  }

#[partial]
def list_has_constructor_named (cs : List InductConstructor) (name : Identifier) : Bool :=
  match cs {
    List.empty => false,
    List.cons c rest =>
      if constructor_simple_name_eq c name then true else list_has_constructor_named rest name,
  }

def inductive_has_constructor_named (ind : Inductive) (name : Identifier) : Bool :=
  match ind {
    Inductive.mk _ _ _ constructors _ _ => list_has_constructor_named constructors name,
  }

#[partial]
def find_inductive_by_case_name (inds : List Inductive) (name : Identifier) : Option Inductive :=
  match inds {
    List.empty => Option.none,
    List.cons ind rest =>
      if inductive_has_constructor_named ind name
      then Option.some ind
      else find_inductive_by_case_name rest name,
  }

/// A `match`'s `MatchCase`s don't carry the scrutinee's inductive path
/// directly (`MatchCase.mc`'s `name` is a bare `Identifier`, per
/// `lang/parser.mo`'s own doc comment on `match_case_name`) -- resolve it
/// by finding which inductive in scope owns a constructor named after the
/// first case. Well-typed, exhaustive matches always have at least one
/// real (non-wildcard) case naming a real constructor of the scrutinee's
/// type, so this is sufficient in practice.
def find_case_inductive (scope : Scope) (cases : List MatchCase) : Option Inductive :=
  match cases {
    List.empty => Option.none,
    List.cons c _ =>
      match c {
        MatchCase.mc name _ _ _ => find_inductive_by_case_name (scope_all_inductives scope) name,
      },
  }

def is_wildcard_case (c : MatchCase) : Bool :=
  match c {
    MatchCase.mc name _ _ _ =>
      match name {
        Identifier.id s => String.beq s "_",
      },
  }

#[partial]
def find_case_for_ctor (ctor : InductConstructor) (cases : List MatchCase) : Option MatchCase :=
  match cases {
    List.empty => Option.none,
    List.cons c rest =>
      match c {
        MatchCase.mc name _ _ _ =>
          if constructor_simple_name_eq ctor name
          then Option.some c
          else find_case_for_ctor ctor rest,
      },
  }

#[partial]
def find_wildcard_case (cases : List MatchCase) : Option MatchCase :=
  match cases {
    List.empty => Option.none,
    List.cons c rest =>
      if is_wildcard_case c then Option.some c else find_wildcard_case rest,
  }

def ctor_name (ctor : InductConstructor) : Identifier :=
  match ctor {
    InductConstructor.mk name _ _ => single_segment_path_head name,
  }

def single_segment_path_head (mp : ModulePath) : Identifier :=
  match mp {
    ModulePath.mp ids => list_last_or_empty ids,
  }

#[partial]
def list_last_or_empty (ids : List Identifier) : Identifier :=
  match ids {
    List.empty => Identifier.id "",
    List.cons hd rest =>
      match rest {
        List.empty => hd,
        List.cons _ _ => list_last_or_empty rest,
      },
  }

/// One arm per constructor of `ind`, in declaration order: an explicit
/// case if the source `match` covered it, else the wildcard case's body
/// (if any), else a synthesized `match_fail`.
#[partial]
def lower_one_match_arm
    (ctx : LowerCtx) (ind_name : ModulePath) (ctor : InductConstructor) (cases : List MatchCase)
    (acc : LowerAcc) (k : MatchArm -> LowerAcc -> Pair (Result LowerError CoreIr) LowerAcc)
    : Pair (Result LowerError CoreIr) LowerAcc :=
  match find_case_for_ctor ctor cases {
    Option.some found_case => lower_explicit_match_case ctx found_case acc k,
    Option.none =>
      match find_wildcard_case cases {
        Option.some wc => lower_wildcard_match_case ctx wc acc k,
        Option.none => k (MatchArm.arm 0 (CoreIr.match_fail ind_name (ctor_name ctor))) acc,
      },
  }

#[partial]
def lower_explicit_match_case
    (ctx : LowerCtx) (found_case : MatchCase) (acc : LowerAcc)
    (k : MatchArm -> LowerAcc -> Pair (Result LowerError CoreIr) LowerAcc)
    : Pair (Result LowerError CoreIr) LowerAcc :=
  match found_case {
    MatchCase.mc _ case_args case_body _ =>
      lower_then (lower_term ctx case_body acc) (fn bir => fn acc1 =>
        k (MatchArm.arm (List.length case_args) bir) acc1),
  }

#[partial]
def lower_wildcard_match_case
    (ctx : LowerCtx) (wc : MatchCase) (acc : LowerAcc)
    (k : MatchArm -> LowerAcc -> Pair (Result LowerError CoreIr) LowerAcc)
    : Pair (Result LowerError CoreIr) LowerAcc :=
  match wc {
    MatchCase.mc _ _ wc_body _ =>
      lower_then (lower_term ctx wc_body acc) (fn bir => fn acc1 =>
        k (MatchArm.arm 0 bir) acc1),
  }

#[partial]
def lower_match_arms_for_ctors
    (ctx : LowerCtx) (ind_name : ModulePath) (ctors : List InductConstructor) (cases : List MatchCase)
    (acc : LowerAcc) (k : List MatchArm -> LowerAcc -> Pair (Result LowerError CoreIr) LowerAcc)
    : Pair (Result LowerError CoreIr) LowerAcc :=
  match ctors {
    List.empty => k List.empty acc,
    List.cons ctor rest =>
      lower_one_match_arm ctx ind_name ctor cases acc (fn arm_ir => fn acc1 =>
        lower_match_arms_for_ctors ctx ind_name rest cases acc1 (fn arms => fn acc2 =>
          k (List.cons arm_ir arms) acc2)),
  }

#[partial]
def lower_match_arms
    (ctx : LowerCtx) (ind : Inductive) (cases : List MatchCase) (acc : LowerAcc)
    (k : List MatchArm -> LowerAcc -> Pair (Result LowerError CoreIr) LowerAcc)
    : Pair (Result LowerError CoreIr) LowerAcc :=
  match ind {
    Inductive.mk ind_name _ _ constructors _ _ =>
      lower_match_arms_for_ctors ctx ind_name constructors cases acc k,
  }

#[partial]
def lower_match (ctx : LowerCtx) (value : Term) (cases : List MatchCase) (acc : LowerAcc) : Pair (Result LowerError CoreIr) LowerAcc :=
  match find_case_inductive (ctx_scope ctx) cases {
    Option.none => lower_err (LowerError.le_unknown_inductive (ModulePath.mp List.empty)) acc,
    Option.some ind =>
      lower_then (lower_term ctx value acc) (fn vir => fn acc1 =>
        lower_match_arms ctx ind cases acc1 (fn arms => fn acc2 =>
          lower_ok (CoreIr.match_ vir arms) acc2)),
  }

#[partial]
def lower_literal (ctx : LowerCtx) (l : Literal) (acc : LowerAcc) : Pair (Result LowerError CoreIr) LowerAcc :=
  match l {
    Literal.str s => lower_ok (CoreIr.lit (IrLit.ir_str s)) acc,
    Literal.num n suffix => lower_ok (CoreIr.lit (IrLit.ir_num n suffix)) acc,
    Literal.if_ cond then_ else_ => lower_if ctx cond then_ else_ acc,
    Literal.match_ value cases => lower_match ctx value cases acc,
  }

// ─── Con / Native (both share the same sparse-args shape) ──────────────

def list_all_none (args : List (Option Term)) : Bool :=
  match args {
    List.empty => true,
    List.cons hd rest =>
      match hd {
        Option.none => list_all_none rest,
        Option.some _ => false,
      },
  }

/// Lowers `args`'s filled prefix, stopping at the first hole (a valid,
/// ordinary partial application) -- but only if every remaining slot
/// after that first hole is *also* a hole. A hole followed by a later
/// filled slot can't be represented as a simple prefix and is reported
/// as `le_con_hole_before_filled_arg` (see this module's doc comment).
#[partial]
def lower_sparse_args
    (ctx : LowerCtx) (args : List (Option Term)) (acc : LowerAcc)
    (k : List CoreIr -> LowerAcc -> Pair (Result LowerError CoreIr) LowerAcc)
    : Pair (Result LowerError CoreIr) LowerAcc :=
  match args {
    List.empty => k List.empty acc,
    List.cons hd rest =>
      match hd {
        Option.some t =>
          lower_then (lower_term ctx t acc) (fn ir => fn acc1 =>
            lower_sparse_args ctx rest acc1 (fn more => fn acc2 => k (List.cons ir more) acc2)),
        Option.none =>
          if list_all_none rest
          then k List.empty acc
          else lower_err LowerError.le_con_hole_before_filled_arg acc,
      },
  }

#[partial]
def find_ctor_tag_from (i : I64) (ctors : List InductConstructor) (name : Identifier) : Option I64 :=
  match ctors {
    List.empty => Option.none,
    List.cons ctor rest =>
      if constructor_simple_name_eq ctor name
      then Option.some i
      else find_ctor_tag_from (i + 1) rest name,
  }

def find_ctor_tag (ctors : List InductConstructor) (name : Identifier) : Option I64 :=
  find_ctor_tag_from 0 ctors name

#[partial]
def lower_con_with_inductive
    (ctx : LowerCtx) (ind : Inductive) (name : Identifier) (num_args : I64) (args : List (Option Term))
    (acc : LowerAcc)
    : Pair (Result LowerError CoreIr) LowerAcc :=
  match ind {
    Inductive.mk _ _ _ constructors _ _ =>
      match find_ctor_tag constructors name {
        Option.some tag =>
          lower_sparse_args ctx args acc (fn present_args => fn acc1 =>
            lower_ok (CoreIr.con tag num_args present_args) acc1),
        Option.none => lower_err (LowerError.le_unknown_constructor (single_segment_path name)) acc,
      },
  }

#[partial]
def lower_con (ctx : LowerCtx) (c : Con) (acc : LowerAcc) : Pair (Result LowerError CoreIr) LowerAcc :=
  match c {
    Con.mk name typ_name num_args args =>
      match scope_find_inductive typ_name (ctx_scope ctx) {
        Result.ok ind => lower_con_with_inductive ctx ind name num_args args acc,
        Result.err _ => lower_err (LowerError.le_unknown_inductive typ_name) acc,
      },
  }

/// A fixed name -> id mapping matching `lang/core_eval.mo`'s
/// `basic_native_table`/`exec_native_by_name` exactly -- this module
/// doesn't own the native table, just maps into it.
def native_id_for_name (name : Identifier) : Option I64 :=
  match name {
    Identifier.id s =>
      if String.beq s "i64_add" then Option.some 0
      else if String.beq s "i64_sub" then Option.some 1
      else if String.beq s "i64_mul" then Option.some 2
      else if String.beq s "i64_eq" then Option.some 3
      else if String.beq s "i64_lt" then Option.some 4
      else Option.none,
  }

#[partial]
def lower_native (ctx : LowerCtx) (native : Native) (acc : LowerAcc) : Pair (Result LowerError CoreIr) LowerAcc :=
  match native {
    Native.mk native_name num_args args =>
      match native_id_for_name native_name {
        Option.some nid =>
          lower_sparse_args ctx args acc (fn present_args => fn acc1 =>
            lower_ok (CoreIr.ntv nid present_args) acc1),
        Option.none => lower_err (LowerError.le_unknown_native native_name) acc,
      },
  }

// ─── Term -> CoreIr, per node ────────────────────────────────────────

#[partial]
def lower_term (ctx : LowerCtx) (t : Term) (acc : LowerAcc) : Pair (Result LowerError CoreIr) LowerAcc :=
  match t {
    Term.var idx dbg =>
      if I64.beq idx sentinel
      then lower_free_var ctx dbg acc
      else lower_ok (CoreIr.local idx) acc,
    Term.lam _dbg _typ body =>
      lower_then (lower_term ctx body acc) (fn ir => fn acc1 => lower_ok (CoreIr.lam ir) acc1),
    Term.app fun_ arg =>
      lower_then (lower_term ctx fun_ acc) (fn fir => fn acc1 =>
        lower_then (lower_term ctx arg acc1) (fn air => fn acc2 =>
          lower_ok (CoreIr.app fir air) acc2)),
    Term.lit value => lower_literal ctx value acc,
    Term.ntv native => lower_native ctx native acc,
    Term.con c => lower_con ctx c acc,
    Term.forall _ _ _ => lower_err LowerError.le_type_level_term acc,
    Term.pi _ _ => lower_err LowerError.le_type_level_term acc,
    Term.type_ _ => lower_err LowerError.le_type_level_term acc,
    Term.hole => lower_err LowerError.le_type_level_term acc,
  }

// ─── Whole-program global table: the worklist pass ──────────────────

def push_done (acc : LowerAcc) (gd : GlobalDef) : LowerAcc :=
  match acc {
    LowerAcc.lower_acc seen done => LowerAcc.lower_acc seen (List.append done [gd]),
  }

/// Resolve one interned path's real body from `ctx`'s flat `List Def`
/// and lower it -- anything not found there becomes `gd_unresolved`,
/// matching Rust's `GlobalDef::Unresolved` fallback (see this module's
/// doc comment on what's not attempted).
#[partial]
def lower_one_global (ctx : LowerCtx) (path : ModulePath) (acc : LowerAcc) : Result LowerError LowerAcc :=
  match find_def_body (ctx_defs ctx) path {
    Option.none => Result.ok (push_done acc (GlobalDef.gd_unresolved path)),
    Option.some body =>
      match lower_term ctx body acc {
        Pair.pair r acc1 =>
          match r {
            Result.ok ir => Result.ok (push_done acc1 (GlobalDef.gd_def ir)),
            Result.err e => Result.err e,
          },
      },
  }

/// Process the worklist to a fixed point: `seen`'s `i`-th path gets
/// lowered once `done` reaches length `i`. Terminates because every step
/// either lowers one more `seen` entry into `done` (shrinking the
/// remaining backlog) or -- if lowering that entry discovers new paths --
/// grows `seen`, but `lower_term` only interns a *finite* number of new
/// paths per body (it walks a finite `Term`), so the backlog can't grow
/// forever between two fixed sizes of `done`.
#[partial]
def process_pending (ctx : LowerCtx) (acc : LowerAcc) : Result LowerError LowerAcc :=
  match acc {
    LowerAcc.lower_acc seen done =>
      match List.get (List.length done) seen {
        Option.none => Result.ok acc,
        Option.some path =>
          match lower_one_global ctx path acc {
            Result.ok acc1 => process_pending ctx acc1,
            Result.err e => Result.err e,
          },
      },
  }

/// Lower the `root` def's body to `CoreIr`, plus a `GlobalTable` covering
/// every def transitively reachable from it -- ready to feed straight
/// into `lang/core_eval.mo`'s `eval` (together with
/// `lang.core_eval.basic_native_table`).
#[partial]
def lower_root (ctx : LowerCtx) (root : ModulePath) : Result LowerError (Pair CoreIr GlobalTable) :=
  match find_def_body (ctx_defs ctx) root {
    Option.none => Result.err (LowerError.le_unresolved_module_path root),
    Option.some body =>
      match lower_term ctx body lower_acc_empty {
        Pair.pair r acc1 =>
          match r {
            Result.err e => Result.err e,
            Result.ok ir => lower_root_finish ir acc1 ctx,
          },
      },
  }

#[partial]
def lower_root_finish (ir : CoreIr) (acc1 : LowerAcc) (ctx : LowerCtx) : Result LowerError (Pair CoreIr GlobalTable) :=
  match process_pending ctx acc1 {
    Result.err e => Result.err e,
    Result.ok acc2 =>
      match acc2 {
        LowerAcc.lower_acc _ done => Result.ok (Pair.pair ir (GlobalTable.global_table done)),
      },
  }

/// The native table this lowering pass targets -- re-exported so callers
/// don't need to import both this module and `lang.core_eval` just to
/// find it.
def natives : NativeTable := basic_native_table

/// Build a `LowerCtx` from a flat `List Decl` -- pulls `Def`s out
/// directly (for `find_def_body`) and builds a `Scope` from the same
/// decl_list (for `scope_resolve_name`/`scope_find_inductive`).
def lower_ctx_from_decls (path : ModulePath) (decl_list : List Decl) : LowerCtx :=
  LowerCtx.lower_ctx (Scope.mk path (build_scope_from_decls path decl_list) Option.none) (decls_to_defs decl_list)

#[partial]
def decls_to_defs (decl_list : List Decl) : List Def :=
  match decl_list {
    List.empty => List.empty,
    List.cons d rest =>
      match d {
        Decl.def_d df => List.cons df (decls_to_defs rest),
        _ => decls_to_defs rest,
      },
  }

// ─── Tests: pure helpers only (no real Scope/Term needed) ─────────────

#[test]
def test_modpath_index_finds_existing : Bool :=
  let a : ModulePath := ModulePath.mp [Identifier.id "A"] in
  let b : ModulePath := ModulePath.mp [Identifier.id "B"] in
  I64.beq (Option.get_or_default (-1) (modpath_index b [a, b])) 1

#[test]
def test_modpath_index_missing_is_none : Bool :=
  let a : ModulePath := ModulePath.mp [Identifier.id "A"] in
  let z : ModulePath := ModulePath.mp [Identifier.id "Z"] in
  match modpath_index z [a] {
    Option.none => true,
    Option.some _ => false,
  }

#[test]
def test_intern_path_reuses_existing_index : Bool :=
  let a : ModulePath := ModulePath.mp [Identifier.id "A"] in
  match intern_path a lower_acc_empty {
    Pair.pair idx0 acc1 =>
      match intern_path a acc1 {
        Pair.pair idx1 _ => I64.beq idx0 0 && I64.beq idx1 0,
      },
  }

#[test]
def test_intern_path_assigns_fresh_indices : Bool :=
  let a : ModulePath := ModulePath.mp [Identifier.id "A"] in
  let b : ModulePath := ModulePath.mp [Identifier.id "B"] in
  match intern_path a lower_acc_empty {
    Pair.pair idx_a acc1 =>
      match intern_path b acc1 {
        Pair.pair idx_b _ => I64.beq idx_a 0 && I64.beq idx_b 1,
      },
  }

#[test]
def test_list_all_none_true_on_all_holes : Bool :=
  let holes : List (Option Term) := [Option.none, Option.none] in
  list_all_none holes

#[test]
def test_list_all_none_false_when_one_filled : Bool :=
  let mixed : List (Option Term) := [Option.none, Option.some Term.hole] in
  Bool.not (list_all_none mixed)

#[test]
def test_find_ctor_tag_matches_declaration_order : Bool :=
  let none_ctor : InductConstructor := InductConstructor.mk (single_segment_path (Identifier.id "none")) List.empty Term.hole in
  let some_ctor : InductConstructor := InductConstructor.mk (single_segment_path (Identifier.id "some")) List.empty Term.hole in
  let ctors : List InductConstructor := [none_ctor, some_ctor] in
  I64.beq (Option.get_or_default (-1) (find_ctor_tag ctors (Identifier.id "none"))) 0
    && I64.beq (Option.get_or_default (-1) (find_ctor_tag ctors (Identifier.id "some"))) 1

#[test]
def test_find_ctor_tag_unknown_is_none : Bool :=
  let some_ctor : InductConstructor := InductConstructor.mk (single_segment_path (Identifier.id "some")) List.empty Term.hole in
  match find_ctor_tag [some_ctor] (Identifier.id "nope") {
    Option.none => true,
    Option.some _ => false,
  }

#[test]
def test_native_id_for_name_known_and_unknown : Bool :=
  I64.beq (Option.get_or_default (-1) (native_id_for_name (Identifier.id "i64_add"))) 0
    && I64.beq (Option.get_or_default (-1) (native_id_for_name (Identifier.id "i64_lt"))) 4
    && match native_id_for_name (Identifier.id "not_a_native") {
      Option.none => true,
      Option.some _ => false,
    }

#[test]
def test_lower_simple_literal_needs_no_scope_lookup : Bool :=
  // `Term.lit (Literal.num 7 i64)` never touches `ctx` -- any `LowerCtx`
  // value would do; since building a real one from scratch is
  // significant machinery on its own, exercise the literal path in
  // isolation here and leave real end-to-end lowering (which does need a
  // real, built `LowerCtx`) to lang/tests/core_eval_lang_tests.mo.
  match lower_literal dummy_ctx (Literal.num 7 NumSuffix.i64) lower_acc_empty {
    Pair.pair r _ =>
      match r {
        Result.ok ir => ir_is_num_lit ir 7,
        Result.err _ => false,
      },
  }

def ir_is_num_lit (ir : CoreIr) (expected : I64) : Bool :=
  match ir {
    CoreIr.lit l => irlit_is_num l expected,
    _ => false,
  }

def irlit_is_num (l : IrLit) (expected : I64) : Bool :=
  match l {
    IrLit.ir_num n _ => I64.beq n expected,
    _ => false,
  }

def dummy_ctx : LowerCtx := LowerCtx.lower_ctx dummy_scope List.empty

def dummy_scope : Scope :=
  Scope.mk (ModulePath.mp List.empty) scope_data_empty Option.none
