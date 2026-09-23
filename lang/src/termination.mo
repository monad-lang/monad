/// Structural termination checking for recursive definitions.
///
/// A port of the reference implementation in `core/src/eval/termination.rs`
/// (the host's `check_termination_all`), reached from the same point in the
/// pipeline: once a module's declarations have been checked, each of that
/// module's own `def`s is verified to recurse only on a *structural subterm* of
/// one of its formal parameters. A recursive call that cannot be shown to
/// decrease something is an error unless the def carries `#[terminating]` or
/// `#[partial]`.
///
/// Before this module, both attributes parsed and were ignored self-hosted --
/// `#[terminating] def loop (x : I64) : I64 := loop x` checked clean while the
/// host rejected it. The two compilers now agree, and both attributes mean here
/// exactly what they mean there.
///
/// Four things about this port are worth knowing before reading it, because
/// three are deviations from the reference and all four are load-bearing:
///
/// * **Mutual groups come from mutual reachability, not Tarjan.** A group is
///   the set of defs that all reach each other, which is exactly a strongly
///   connected component of more than one member -- mutual reachability is an
///   equivalence relation, so its classes *are* the SCCs. Computing them
///   directly costs one transitive closure per def and threads no mutable
///   index/lowlink state, which a pure language cannot carry through a `List`
///   walk anyway. The partition is identical to the reference's.
/// * **Diagnostics accumulate instead of failing fast.** The reference returns
///   `Err` at the first bad def (`?`); this returns one message per bad def,
///   which is the convention `check_module_with_scope`'s own per-decl walk
///   already follows. The *set* of failing defs is the same either way. The
///   message *text* is the reference's `Display` output character for
///   character, down to its em dash; `render_diag` below adds the `error: `
///   prefix that every other diagnostic in that walk gets from
///   `render_type_error`, so the two compilers' output for the same bad def is
///   line for line the same.
/// * **Names are compared as rendered strings.** Identifiers cannot contain
///   `.` or `:`, so `show_identifier`/`show_name_path` are injective, and
///   comparing on them sidesteps `Identifier`/`NamePath` identity entirely.
///   This is also what the reference does -- `recursion_name` takes a qualified
///   name's *name half* and compares that, deliberately over-approximating so
///   the check errs toward rejecting rather than accepting.
/// * **A constrained def's term is not shaped like its call sites.** Its
///   leading `Term.lam`s include the `__dict_<Class>` binders
///   `add_constraint_dict_params` prepends (`lib::scope`), while a recursive
///   call site passes no dictionary -- those are inserted far later, in codegen.
///   The reference has the mirror-image problem and solves it by skipping
///   implicit `Par::I` parameters. `extract_params` and `drop_leading_dict_args`
///   below drop that same leading run from both sides, so a def's declared
///   parameters line up with its call sites' arguments exactly as they do there.
///
/// One residual hole is inherited rather than introduced, and is left as the
/// reference leaves it: neither walk descends into a `Literal.struct_lit` /
/// `struct_update`'s field values, so a recursive call written *only* inside a
/// struct literal is invisible to the checker. Struct literals are desugared
/// before this runs, so nothing in the corpus reaches that shape.
///
/// The comparison on name halves is safe specifically because this runs on ONE
/// module's own declarations, before any qualification: `check_module_with_scope`
/// is reached from `elaborate_loaded_modules`, whose `target_decls` is
/// `main_module.decl_list` (`lang/module.mo`), and the pass that rewrites names
/// to `module.path::name` is `qualify_modules` in `lang/codegen/qualify.mo` -- a
/// codegen pass, downstream of every check. Within one module no two defs share a
/// name, so discarding the qualifier (as `recursion_name` does) cannot conflate
/// two of them.

use lib::types {
  Attribute, Decl, DebugName, Def, Identifier, MatchCase, Term,
  def_d, has_attr, show_identifier, show_name_path,
}
use lib::pretty {show_term}

// ---------------------------------------------------------------- strings

/// `s` with everything up to and including its last `::` removed: the NAME half
/// of a possibly module-qualified reference, which is the half the reference
/// implementation compares.
def strip_module_qualifier (s : String) : String :=
    let n := String.length s in
    let idx := last_sep_index s 0 n (0 - 1) in
    if I64.lt idx 0 then s
    else String.slice s (I64.add idx 2) (I64.sub (I64.sub n idx) 2)

/// The index of the last `::` in `s`, scanning to `n`, or `found` (started at
/// -1) when there is none. Hand-rolled rather than `String.find_last`: that
/// exists in `init.string` but is not `pub`, and a left-to-right scan that
/// remembers its last hit is the same thing without reaching into a library
/// this module has no other reason to depend on.
#[partial]
def last_sep_index (s : String) (i : I64) (n : I64) (found : I64) : I64 :=
    if I64.gt (I64.add i 2) n then found
    else if String.beq (String.slice s i 2) "::" then last_sep_index s (I64.add i 1) n i
    else last_sep_index s (I64.add i 1) n found

def str_mem (x : String) (xs : List String) : Bool :=
    match xs {
        List.empty => false,
        List.cons hd tl => if String.beq x hd then true else str_mem x tl,
    }

/// `a`'s elements followed by `b`'s. Deliberately this module's own rather than
/// the ambient `list_append`: `lang/module.mo` records that the two do not agree
/// on their binder (`lang/scope.mo`'s takes an explicit `{A : Type}`), and this
/// module has no stake in which one wins.
def strs_append (a b : List String) : List String :=
    match a {
        List.empty => b,
        List.cons hd tl => List.cons hd (strs_append tl b),
    }

def str_join (sep : String) (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons hd tl =>
            match tl {
                List.empty => hd,
                List.cons _ _ => String.concat hd (String.concat sep (str_join sep tl)),
            },
    }

def str_add_uniq (x : String) (xs : List String) : List String :=
    if str_mem x xs then xs else List.cons x xs

def str_union (a b : List String) : List String :=
    match a {
        List.empty => b,
        List.cons hd tl => str_add_uniq hd (str_union tl b),
    }

/// The key every name comparison in this module uses. The de Bruijn index a
/// `Term.var` also carries is deliberately ignored, matching the reference: it
/// compares the name half of a reference and nothing else, which
/// over-approximates "is this the def under check" and is therefore sound in
/// the direction that matters. `unnamed` never denotes a def, and `"_"` is
/// unreachable as a def name, so it is a safe key for one.
def debug_name_key (dbg : DebugName) : String :=
    match dbg {
        DebugName.named ident => strip_module_qualifier (show_identifier ident),
        DebugName.unnamed => "_",
    }

/// The pattern binders of a `match` case as keys, with `_` dropped -- a
/// wildcard proves nothing about the value it matched, so it is not a usable
/// witness that anything got smaller.
def id_keys (idents : List Identifier) : List String :=
    match idents {
        List.empty => List.empty,
        List.cons hd tl =>
            let k := show_identifier hd in
            if String.beq k "_" then id_keys tl else List.cons k (id_keys tl),
    }

// ------------------------------------------------------------ subterm env

/// `SubtermEnv`, to use the reference's own name for it: each formal parameter
/// mapped to the binders a `match` on that parameter (or on a known subterm of
/// it) has proved smaller than it. An association LIST rather than a map type,
/// because the entries are a handful of strings and a map would mean taking a
/// class-instance dependency purely to store them.
def env_lookup (param : String) (env : List (Pair String (List String))) : List String :=
    match env {
        List.empty => List.empty,
        List.cons hd tl =>
            match hd {
                Pair.pair k v => if String.beq k param then v else env_lookup param tl,
            },
    }

def env_add (param : String) (subs : List String) (env : List (Pair String (List String))) : List (Pair String (List String)) :=
    match env {
        List.empty => List.cons (Pair.pair param subs) List.empty,
        List.cons hd tl =>
            match hd {
                Pair.pair k v =>
                    if String.beq k param then List.cons (Pair.pair k (strs_append v subs)) tl
                    else List.cons (Pair.pair k v) (env_add param subs tl),
            },
    }

/// The one parameter `ident` is currently known to be a subterm of, if any.
/// This is what makes a `match` on an already-matched subterm extend the
/// ORIGINAL parameter's set rather than starting a new one.
def env_owner (ident : String) (env : List (Pair String (List String))) : Option String :=
    match env {
        List.empty => Option.none,
        List.cons hd tl =>
            match hd {
                Pair.pair k v => if str_mem ident v then Option.some k else env_owner ident tl,
            },
    }

// ------------------------------------------------------------------ terms

/// `t` with a `Term.ctx` position wrapper removed. Every step of every walk
/// below unwraps at most one `Ctx`, which is what the reference's walks do too
/// -- and it matters here more than there, because self-hosted wraps most terms
/// in one, so a `Ctx`-wrapped self-reference would otherwise read as neither an
/// identity (no decrease, keep looking) nor a subterm (a rejected call).
def strip_ctx (t : Term) : Term :=
    match t {
        Term.ctx _loc inner => strip_ctx inner,
        _ => t,
    }

/// An application chain's arguments, in SOURCE order: arguments are consed
/// outermost-first as the walk descends, and the outermost application holds
/// the last argument, so the list needs no reversing.
#[partial]
def app_args (t : Term) (acc : List Term) : List Term :=
    let inner := strip_ctx t in
    match inner {
        Term.app fun arg => app_args fun (List.cons arg acc),
        _ => acc,
    }

/// The head of an application chain -- the function something is being applied
/// to, which `as_recursive_call` tests for a recursive name.
#[partial]
def app_head (t : Term) : Term :=
    let inner := strip_ctx t in
    match inner {
        Term.app fun _arg => app_head fun,
        _ => inner,
    }

def term_is_recursive_ref (t : Term) (names : List String) : Bool :=
    match strip_ctx t {
        Term.var _idx dbg => str_mem (debug_name_key dbg) names,
        _ => false,
    }

/// A call to one of `names`, as its argument list, or `none` when `t` is not
/// such a call. A bare reference is deliberately NOT a call: the reference
/// implementation returns `None` for an empty argument list, and a self-
/// reference with nothing applied to it cannot decrease anything.
def as_recursive_call (t : Term) (names : List String) : Option (List Term) :=
    if term_is_recursive_ref (app_head t) names then
        let call_args := app_args t List.empty in
        if List.is_empty call_args then Option.none else Option.some call_args
    else Option.none

// ------------------------------------------------------------- parameters

/// A constrained def's term opens with the `__dict_<Class>` binders
/// `add_constraint_dict_params` prepends, and no call site passes them (see this
/// module's header). Dropping that leading run leaves exactly the declared
/// parameters, which is what the reference's implicit-skipping `extract_params`
/// produces. A def with no such binder -- the overwhelmingly common case -- is
/// returned unchanged.
def drop_leading_dict_params (params : List String) : List String :=
    match params {
        List.empty => List.empty,
        List.cons hd tl =>
            if String.starts_with "__dict_" hd then drop_leading_dict_params tl
            else params,
    }

/// The argument-side half of the same asymmetry, for the case where a leading
/// dictionary argument has already been inserted as a bare `__dict_*` variable.
def drop_leading_dict_args (args : List Term) : List Term :=
    match args {
        List.empty => List.empty,
        List.cons hd tl =>
            let is_dict := match strip_ctx hd {
                Term.var _idx dbg => String.starts_with "__dict_" (debug_name_key dbg),
                _ => false,
            } in
            if is_dict then drop_leading_dict_args tl else args,
    }

#[partial]
def collect_lam_params (t : Term) : List String :=
    match strip_ctx t {
        Term.lam dbg _typ inner => List.cons (debug_name_key dbg) (collect_lam_params inner),
        _ => List.empty,
    }

/// The formal parameters a def's body binds, outermost first, with any leading
/// implicit dictionary binder dropped. Only the LEADING `Term.lam` chain is
/// walked -- a lambda further inside the body binds nothing a call site can be
/// compared against.
def extract_params (t : Term) : List String :=
    drop_leading_dict_params (collect_lam_params t)

// -------------------------------------------------------------- the check

/// The reference's `is_identity`: this argument IS its parameter, so it says
/// nothing about decrease at this position -- not a failure, just no evidence.
def arg_is_self (arg : Term) (param : String) : Bool :=
    match strip_ctx arg {
        Term.var _idx dbg => String.beq (debug_name_key dbg) param,
        _ => false,
    }

/// The reference's `is_subterm`: this argument is a variable some `match` on
/// `param` (or on a known subterm of it) has proved strictly smaller.
def arg_is_subterm (env : List (Pair String (List String))) (param : String) (arg : Term) : Bool :=
    match strip_ctx arg {
        Term.var _idx dbg => str_mem (debug_name_key dbg) (env_lookup param env),
        _ => false,
    }

/// Whether any position of a recursive call shows a decrease. Lexicographic,
/// like the reference: no decrease at a position is not a failure, it just
/// means a LATER position has to supply one. Only running out of positions
/// without ever finding one is.
def args_have_decrease (args : List Term) (params : List String) (env : List (Pair String (List String))) : Bool :=
    match args {
        List.empty => false,
        List.cons a rest =>
            match params {
                List.empty => false,
                List.cons p prest =>
                    if arg_is_self a p then args_have_decrease rest prest env
                    else if arg_is_subterm env p a then true
                    else args_have_decrease rest prest env,
            },
    }

/// A `match` makes each of its case binders a strict subterm of the scrutinee,
/// provided the scrutinee is a formal parameter or a known subterm of one --
/// directly if so, transitively (against the ORIGINAL parameter) if not. A
/// `match` on anything else, or a case whose binders are all `_`, extends
/// nothing.
def extend_env_from_match (env : List (Pair String (List String))) (scrutinee : Term) (cargs : List Identifier) (params : List String) : List (Pair String (List String)) :=
    match strip_ctx scrutinee {
        Term.var _idx dbg =>
            let sid := debug_name_key dbg in
            let news := id_keys cargs in
            if List.is_empty news then env
            else if str_mem sid params then env_add sid news env
            else match env_owner sid env {
                Option.some owner => env_add owner news env,
                Option.none => env,
            },
        _ => env,
    }

/// Each case of a `match` is checked against a FRESH copy of the outer
/// environment extended by that case's own binders: a binder in one arm says
/// nothing about another arm.
def check_cases (cases : List MatchCase) (key : String) (names : List String) (params : List String) (env : List (Pair String (List String))) (scrutinee : Term) : Option String :=
    match cases {
        List.empty => Option.none,
        List.cons c rest =>
            match c {
                MatchCase.mc _cname cargs cbody _fp =>
                    match check_body cbody key names params (extend_env_from_match env scrutinee cargs params) {
                        Option.some msg => Option.some msg,
                        Option.none => check_cases rest key names params env scrutinee,
                    },
            },
    }

/// The reference's `check_body_termination`. On an application that IS a
/// recursive call the arguments are judged and the walk STOPS -- it does not
/// descend into the call's own subexpressions. That asymmetry is deliberate
/// there (the call is the thing under judgement, and a decrease found anywhere
/// inside it would be evidence about a different call) and is preserved here.
def check_body (body : Term) (key : String) (names : List String) (params : List String) (env : List (Pair String (List String))) : Option String :=
    match body {
        Term.lam _dbg _typ inner => check_body inner key names params env,
        Term.ctx _loc inner => check_body inner key names params env,
        Term.app fun arg =>
            match as_recursive_call body names {
                Option.some call_args =>
                    if args_have_decrease (drop_leading_dict_args call_args) params env then Option.none
                    else Option.some (args_not_structural_msg key body call_args params),
                Option.none =>
                    match check_body fun key names params env {
                        Option.some msg => Option.some msg,
                        Option.none => check_body arg key names params env,
                    },
            },
        Term.lit value =>
            match value {
                Literal.match_ scrutinee cases => check_cases cases key names params env scrutinee,
                Literal.if_ one two three =>
                    match check_body one key names params env {
                        Option.some msg => Option.some msg,
                        Option.none =>
                            match check_body two key names params env {
                                Option.some msg => Option.some msg,
                                Option.none => check_body three key names params env,
                            },
                    },
                _ => Option.none,
            },
        _ => Option.none,
    }

// ------------------------------------------------------------- call graph

def find_callees_cases (cases : List MatchCase) (names : List String) : List String :=
    match cases {
        List.empty => List.empty,
        List.cons c rest =>
            match c {
                MatchCase.mc _cname _cargs cbody _fp => str_union (find_callees cbody names) (find_callees_cases rest names),
            },
    }

/// Every name in `names` that `t` references anywhere, deduplicated. This walk
/// is deliberately WIDER than `check_body`'s: the call graph only needs to know
/// who may call whom, so it descends into binders, into both sides of an
/// application, and into `Pi`/`Forall` types, where `check_body` does not.
def find_callees (t : Term) (names : List String) : List String :=
    match t {
        Term.var _idx dbg =>
            let k := debug_name_key dbg in
            if str_mem k names then List.cons k List.empty else List.empty,
        Term.app fun arg => str_union (find_callees fun names) (find_callees arg names),
        Term.lam _dbg _typ inner => find_callees inner names,
        Term.ctx _loc inner => find_callees inner names,
        Term.pi arg ret => str_union (find_callees arg names) (find_callees ret names),
        Term.forall _dbg kind inner => str_union (find_callees kind names) (find_callees inner names),
        Term.lit value =>
            match value {
                Literal.match_ scrutinee cases => str_union (find_callees scrutinee names) (find_callees_cases cases names),
                Literal.if_ one two three => str_union (find_callees one names) (str_union (find_callees two names) (find_callees three names)),
                _ => List.empty,
            },
        _ => List.empty,
    }

def graph_lookup (key : String) (graph : List (Pair String (List String))) : List String :=
    match graph {
        List.empty => List.empty,
        List.cons hd tl =>
            match hd {
                Pair.pair k v => if String.beq k key then v else graph_lookup key tl,
            },
    }

/// Every node reachable from `seeds` by following `graph`. `seen` doubles as the
/// visited set and the result, so a cycle terminates rather than recursing
/// forever -- which is the whole point of running this over a call graph.
#[partial]
def reach_acc (graph : List (Pair String (List String))) (work : List String) (seen : List String) : List String :=
    match work {
        List.empty => seen,
        List.cons hd tl =>
            if str_mem hd seen then reach_acc graph tl seen
            else reach_acc graph (strs_append (graph_lookup hd graph) tl) (List.cons hd seen),
    }

def filter_mutual (graph : List (Pair String (List String))) (start : String) (fwd : List String) (keys : List String) : List String :=
    match keys {
        List.empty => List.empty,
        List.cons k tl =>
            if String.beq k start then List.cons k (filter_mutual graph start fwd tl)
            else if str_mem k fwd then
                if str_mem start (reach_acc graph (graph_lookup k graph) List.empty)
                then List.cons k (filter_mutual graph start fwd tl)
                else filter_mutual graph start fwd tl
            else filter_mutual graph start fwd tl,
    }

/// The defs that both reach and are reached by `start`, including `start`
/// itself. That is exactly the strongly connected component of `start`, so a
/// class of more than one member is a mutually recursive group -- and a class of
/// one means `start` is only self-recursive. This is where `find_mutual_groups`
/// lands without Tarjan: mutual reachability is an equivalence relation, so its
/// classes partition the graph the same way SCCs do, and no mutable
/// index/lowlink state has to be threaded through the walk.
def mutual_class (graph : List (Pair String (List String))) (start : String) (keys : List String) : List String :=
    let fwd := reach_acc graph (graph_lookup start graph) List.empty in
    filter_mutual graph start fwd keys

def list_has_two (xs : List String) : Bool :=
    match xs {
        List.empty => false,
        List.cons _hd tl =>
            match tl {
                List.empty => false,
                List.cons _ _ => true,
            },
    }

// ------------------------------------------------------------- the driver

def def_key (d : Def) : String :=
    match d {
        Def.mk {name, ..} => show_name_path name,
    }

def def_term (d : Def) : Term :=
    match d {
        Def.mk {term, ..} => term,
    }

def def_attrs (d : Def) : List Attribute :=
    match d {
        Def.mk {attrs, ..} => attrs,
    }

/// `#[terminating]` or `#[partial]` -- the two attributes that take a def out of
/// the check. Both are real corpus usage (`std/src/map.mo`'s `insert` is
/// `#[terminating]`), so recognising them is not a courtesy.
def has_terminating_or_partial (attrs : List Attribute) : Bool :=
    if has_attr (Identifier.id "terminating") attrs then true
    else has_attr (Identifier.id "partial") attrs

def args_not_structural_msg (key : String) (call : Term) (args : List Term) (params : List String) : String :=
    let detail :=
        String.concat "Argument(s) ("
            (String.concat (str_join ", " (List.map show_term args))
                (String.concat ") are not structural subterms of parameter(s) ("
                    (String.concat (str_join ", " params) ")"))) in
    String.concat "Termination check failed for '"
        (String.concat key
            (String.concat "'\n  Recursive call: "
                (String.concat (show_term call)
                    (String.concat "\n  "
                        (String.concat detail " — add #[terminating] if this function is well-founded")))))

def no_params_msg (key : String) : String :=
    String.concat "No recursive parameters found for '" (String.concat key "'")

/// One def's diagnostics. `in_group` picks between the reference's two modes: a
/// member of a mutually recursive group with no formal parameters is itself an
/// error there (`NoRecursiveParams` -- a group that cannot show a decrease is
/// not a group the check can clear), while a lone def with none is simply
/// nothing to check.
def check_one_def (d : Def) (names : List String) (in_group : Bool) : List String :=
    let key := def_key d in
    let params := extract_params (def_term d) in
    let body_diags :=
        match check_body (def_term d) key names params List.empty {
            Option.some msg => List.cons msg List.empty,
            Option.none => List.empty,
        } in
    if has_terminating_or_partial (def_attrs d) then List.empty
    else if List.is_empty params then
        if in_group then List.cons (no_params_msg key) List.empty else List.empty
    else body_diags

/// Every def's diagnostics, in declaration order. A def in a mutual group is
/// checked against the WHOLE group, so a call that passes through a sibling is
/// still judged on whether it decreases -- that is what makes a group checkable
/// at all, and why the group's members are reported individually rather than
/// only the first of them.
def check_defs (defs : List Def) (graph : List (Pair String (List String))) (keys : List String) : List String :=
    match defs {
        List.empty => List.empty,
        List.cons d tl =>
            let key := def_key d in
            let group := mutual_class graph key keys in
            let grouped := list_has_two group in
            let names := if grouped then group else List.cons key List.empty in
            strs_append (check_one_def d names grouped) (check_defs tl graph keys),
    }

def def_callees (keys : List String) (d : Def) : Pair String (List String) :=
    Pair.pair (def_key d) (find_callees (def_term d) keys)

def collect_defs (decls : List Decl) : List Def :=
    match decls {
        List.empty => List.empty,
        List.cons d tl =>
            match d {
                Decl.def_d df => List.cons df (collect_defs tl),
                _ => collect_defs tl,
            },
    }

/// The check output's convention, applied here because these messages reach the
/// diagnostic list pre-rendered: `render_type_error`
/// (`lang/src/typecheck/diagnostic.mo`) opens every other diagnostic with
/// `error: `, and the host's own renderer prefixes uniformly, so a termination
/// error that skipped it would be the one diagnostic in the output not shaped
/// like the rest. A termination diagnostic carries no context name and no
/// location -- neither implementation has one to give -- so the prefix is the
/// whole of the rendering, and what follows it is the message body verbatim.
def render_diag (msg : String) : String :=
    String.concat "error: " msg

/// Termination-check a module's own `def`s, returning one diagnostic per failing
/// def. This is the entry point `check_module_with_scope` (`lang/src/module.mo`)
/// calls, which is where the host calls its own `check_termination_all`
/// (`core/src/core_check_module.rs`): once, per checked module, over that
/// module's own top-level defs.
pub def check_termination_all (decls : List Decl) : List String :=
    let defs := collect_defs decls in
    let keys := List.map def_key defs in
    let graph := List.map (def_callees keys) defs in
    List.map render_diag (check_defs defs graph keys)

// ------------------------------------------------------------------ tests
//
// The checker's input is a `Term`, so these build terms directly -- the same
// thing the reference implementation's own unit tests do, and the only way to
// reach shapes the corpus does not contain: a bare self-call, a mutual group
// none of whose members decrease, a leading dictionary binder. They run under
// both runners, so a change to the walk has to keep satisfying them there.

def t_var (s : String) : Term := Term.var (0 - 1) (DebugName.named (Identifier.id s))

def t_lam (s : String) (body : Term) : Term :=
    Term.lam (DebugName.named (Identifier.id s)) Term.hole body

def t_app (f : Term) (a : Term) : Term := Term.app f a

def t_case (name : String) (binders : List String) (body : Term) : MatchCase :=
    MatchCase.mc (Identifier.id name) (List.map Identifier.id binders) body Option.none

def t_match (scrutinee : Term) (cases : List MatchCase) : Term :=
    Term.lit (Literal.match_ scrutinee cases)

/// A top-level `def` decl carrying `term`. The declared type is a hole -- this
/// module reads only a def's `name`, `term` and `attrs`, and the checker never
/// looks at the type at all.
def t_def (name : String) (term : Term) (attrs : List Attribute) : Decl :=
    Decl.def_d (Def.mk (NamePath.npath (List.cons (Identifier.id name) List.empty))
        Term.hole term List.empty attrs Visibility.package_private List.empty)

def t_partial_attr : Attribute := Attribute.mk (Identifier.id "partial") List.empty

#[test]
def test_termination_rejects_a_self_call_that_does_not_decrease : Bool :=
    let d := t_def "spin" (t_lam "n" (t_app (t_var "spin") (t_var "n"))) List.empty in
    match check_termination_all (List.cons d List.empty) {
        List.cons msg _ =>
            if String.contains msg "Termination check failed" then String.contains msg "spin"
            else false,
        List.empty => false,
    }

#[test]
def test_termination_accepts_recursion_on_a_matched_subterm : Bool :=
    let cases := List.cons
        (t_case "nil" List.empty Term.hole)
        (List.cons
            (t_case "cons" (List.cons "head" (List.cons "tail" List.empty))
                (t_app (t_var "len") (t_var "tail")))
            List.empty) in
    let d := t_def "len" (t_lam "xs" (t_match (t_var "xs") cases)) List.empty in
    List.is_empty (check_termination_all (List.cons d List.empty))

/// The transitive case: the call is on a binder of a match on a binder of the
/// outer match, which is a subterm of the same original parameter.
#[test]
def test_termination_accepts_a_transitively_matched_subterm : Bool :=
    let inner := List.cons
        (t_case "nil" List.empty Term.hole)
        (List.cons
            (t_case "cons" (List.cons "b" (List.cons "more" List.empty))
                (t_app (t_var "f") (t_var "more")))
            List.empty) in
    let outer := List.cons
        (t_case "nil" List.empty Term.hole)
        (List.cons
            (t_case "cons" (List.cons "a" (List.cons "rest" List.empty))
                (t_match (t_var "rest") inner))
            List.empty) in
    let d := t_def "f" (t_lam "xs" (t_match (t_var "xs") outer)) List.empty in
    List.is_empty (check_termination_all (List.cons d List.empty))

/// Lexicographic, as in the reference: a position that is merely the SAME
/// argument proves nothing, but does not fail the call either -- a later
/// position can still supply the decrease.
#[test]
def test_termination_accepts_a_decrease_at_a_later_position : Bool :=
    let cases := List.cons
        (t_case "z" List.empty Term.hole)
        (List.cons
            (t_case "s" (List.cons "m2" List.empty)
                (t_app (t_app (t_var "f") (t_var "n")) (t_var "m2")))
            List.empty) in
    let d := t_def "f" (t_lam "n" (t_lam "m" (t_match (t_var "m") cases))) List.empty in
    List.is_empty (check_termination_all (List.cons d List.empty))

#[test]
def test_termination_skips_a_def_marked_partial : Bool :=
    let d := t_def "loop" (t_lam "n" (t_app (t_var "loop") (t_var "n")))
        (List.cons t_partial_attr List.empty) in
    List.is_empty (check_termination_all (List.cons d List.empty))

/// Each member of a group is reported, not just the first: the group as a whole
/// fails, and which of its members was written first is not a meaningful thing
/// to be told. Counted with the checker's own `list_has_two` rather than a
/// nested pattern -- patterns go one constructor level deep.
#[test]
def test_termination_reports_every_member_of_a_mutual_group : Bool :=
    let even := t_def "is_even" (t_lam "n" (t_app (t_var "is_odd") (t_var "n"))) List.empty in
    let odd := t_def "is_odd" (t_lam "n" (t_app (t_var "is_even") (t_var "n"))) List.empty in
    list_has_two (check_termination_all (List.cons even (List.cons odd List.empty)))

/// A lone def with no formal parameters is nothing to check, matching the
/// reference: only a *member of a group* with none is an error there.
#[test]
def test_termination_ignores_a_lone_def_without_parameters : Bool :=
    let d := t_def "g" (t_app (t_var "g") (t_var "x")) List.empty in
    List.is_empty (check_termination_all (List.cons d List.empty))

/// `add_constraint_dict_params` prepends an implicit `__dict_<Class>` binder to
/// a constrained def's term, and no call site passes one. Without the leading
/// strip the parameters would be off by one against the arguments and this
/// would be rejected -- so the test is discriminating, not decorative.
#[test]
def test_termination_ignores_a_leading_dictionary_parameter : Bool :=
    let cases := List.cons
        (t_case "z" List.empty Term.hole)
        (List.cons
            (t_case "s" (List.cons "m" List.empty) (t_app (t_var "f") (t_var "m")))
            List.empty) in
    let term := t_lam "__dict_Show" (t_lam "n" (t_match (t_var "n") cases)) in
    let d := t_def "f" term List.empty in
    List.is_empty (check_termination_all (List.cons d List.empty))
