/// `CodegenCtx` -- the state threaded through term compilation -- and
/// the tables it carries.
///
/// Extracted from `lang/codegen/emit.mo` so that the two consumers of
/// `fresh_temp`/`fresh_label` can be separate modules: without a shared
/// home for the context, `lang.codegen.tco`'s tail-call rewrite and
/// `emit`'s term compiler would each need the other's names and could
/// not be split at all.
///
/// `arities` are keyed by `def_symbol_name`
/// (`lang.codegen.symbols`); `ctor_tags`/`ctor_arities` are keyed in
/// CONSTRUCTOR space, which is a different namespace -- see
/// `constructor_tag` in `emit` for the three key shapes it uses.
use lang.types {
  DebugName, Def, Identifier, Location, ModulePath, Param, Term, param_many,
}
use lang.codegen.ir {DbgLoc, LLVMValue}
use lang.codegen.symbols {def_symbol_name}
use lang.codegen.util {str_map_empty, str_map_insert, str_map_lookup}
use std.map {}

struct LocalBinding {
    name : Identifier,
    val : LLVMValue,
}

struct CodegenCtx {
    locals : List LocalBinding,
    next_temp : I64,
    next_label : I64,
    /// Each top-level def's own known arity (its param count, i.e. the
    /// number of leading `Term.lam`s in its body) keyed by the SAME
    /// `llvm_name` a bare `Term.var` reference to it would compute
    /// (`def_symbol_name` of its module-qualified name) -- built once
    /// per module compile (`build_arity_table`) so `Term.var`'s
    /// value-position case (Phase 0 of the dictionary-passing plan, see
    /// plans/bootstrapping/self-hosted-compiler.md) can tell an arity-0
    /// def (still an eager 0-arg call, unchanged) from an arity>0 def (now
    /// boxed via `alloc_closure` instead of miscompiling as a 0-arg call
    /// to a function that isn't one). A `HashMap` (not a `List`), mirroring
    /// `ctor_tags` -- looked up once per `Term.var` reference across a
    /// whole compile, the same shape that already made `ctor_tags`/
    /// `filter_reachable`'s HashMap conversions decisive wins.
    arities : HashMap String I64,
    ctor_tags : HashMap String I64,
    /// Mirrors `ctor_tags` exactly (same keying, same build site) but
    /// for each user-defined constructor's field count instead of its
    /// tag -- see `constructor_arity`'s own doc comment for why this is
    /// needed.
    ctor_arities : HashMap String I64,
    /// The position in force while compiling a term, set when
    /// `compile_db_term_ir` enters a `Term.ctx` and restored on the way
    /// out. `none` whenever locations are off, and whenever a term
    /// carries none -- a synthesized node, or one under a placement rule
    /// that keeps wrappers away (R1/R2/R3, see `lower_parse.mo`).
    ///
    /// Read at instruction emission, where it becomes a `loc_marker`.
    current_loc : Option DbgLoc,
}

struct CtxStrPair {
    ctx : CodegenCtx,
    str : String,
}

/// `arities` -- see `CodegenCtx`'s own doc comment. Callers with a real
/// `List Def` in scope should build one via `build_arity_table` instead
/// of passing `empty_arities` (an empty table just means every bare
/// global reference falls back to today's eager-0-arg-call behavior --
/// correct only for genuinely 0-arity defs).
#[partial]
def empty_ctx (arities : HashMap String I64) (ctor_tags : HashMap String I64) (ctor_arities : HashMap String I64) : CodegenCtx :=
    { locals := List.empty, next_temp := 0, next_label := 0, arities := arities, ctor_tags := ctor_tags, ctor_arities := ctor_arities, current_loc := Option.none }

/// Convert a captured source position to the minimal
/// `lang.codegen.ir.DbgLoc` shape `LLVMFunction.dbg_loc` expects.
/// (The v1 name-keyed fallback table this used to serve --
/// `dbg_loc_for`/`dbg_loc_for_unqualified`, keyed by bare source name
/// -- is gone: since stage 6 a function's own location is the
/// `Term.ctx` wrapper on its body, so there is no table to miss.)
#[partial]
def dbg_loc_of_location (loc : Location) : Option DbgLoc := match loc {
    Location.mk _offset line column => Option.some (DbgLoc.mk line column),
}

#[partial]
def fresh_temp (c : CodegenCtx) : CtxStrPair :=
    let name := String.concat "t" (I64.to_string c.next_temp) in
    let c2 : CodegenCtx := { c with next_temp := c.next_temp + 1 } in
    CtxStrPair.mk c2 name

#[partial]
def fresh_label (c : CodegenCtx) (prefix : String) : CtxStrPair :=
    let name := String.concat prefix (String.concat "_" (I64.to_string c.next_label)) in
    let c2 : CodegenCtx := { c with next_label := c.next_label + 1 } in
    CtxStrPair.mk c2 name

#[partial]
def ctx_bind_local (c : CodegenCtx) (name : Identifier) (val : LLVMValue) : CodegenCtx :=
    let binding : LocalBinding := LocalBinding.mk name val in
    { c with locals := List.cons binding c.locals }

#[partial]
def ctx_lookup_local (c : CodegenCtx) (name : Identifier) : Option LLVMValue := lookup_binding c.locals name

/// Looks up `name`'s constructor tag from `c`'s own dynamically-built
/// table (`build_constructor_tag_map`) -- the fallback `is_constructor_
/// var_dyn`/`constructor_tag_dyn` use for anything not in the hardcoded
/// builtin list.
#[partial]
def ctx_lookup_ctor_tag (c : CodegenCtx) (name : String) : Option I64 := str_map_lookup name c.ctor_tags

#[partial]
def ctx_lookup_ctor_arity (c : CodegenCtx) (name : String) : Option I64 := str_map_lookup name c.ctor_arities

/// Rebuilds `c` with an EMPTY `locals` list, preserving `next_temp`/
/// `next_label`/`arities`. Used when entering a freshly-lifted
/// function's own body (`compile_db_lam_ir`) -- the OUTER function's
/// locals must not leak through as stale cross-function SSA references
/// (this is the closure-free-variable-capture fix's actual correctness
/// backbone, not just an optimization: `ctx_bind_local` alone only
/// PREPENDS to whatever locals list it's handed, it never resets one --
/// so without this, a lifted function's ctx still carries every binding
/// visible in its ENCLOSING function, and a free-variable reference
/// inside the lifted body would silently "succeed" via `ctx_lookup_local`
/// against a register — `parm_`/`var_` — that belongs to the outer
/// function and doesn't exist in the lifted one at all, which is
/// exactly the `llc: use of undefined value` bug this whole fix exists
/// for). Only the lambda's own param and its explicitly rebuilt
/// captures (`build_get_env_instrs`) should be visible inside.
#[partial]
def ctx_reset_locals (c : CodegenCtx) : CodegenCtx := { c with locals := List.empty }

/// The other half of `ctx_reset_locals`: after compiling a lifted
/// function's own body (`compile_db_lam_ir`) with a reset-and-rebuilt
/// `locals` list (the lambda's own param + its captures ONLY), the ctx
/// handed back to the ENCLOSING function's own ongoing compilation must
/// have its ORIGINAL locals restored -- `outer`'s own `locals`, i.e.
/// whatever was visible right before this lambda was compiled -- while
/// still carrying forward `inner`'s updated `next_temp`/`next_label`
/// counters (so the enclosing function's own subsequent fresh names
/// don't collide with names already used inside the lifted function).
/// Confirmed as a real, distinct bug via a direct repro: without this,
/// a SECOND lifted lambda compiled later in the SAME enclosing
/// function's body (e.g. a do-block's own trailing `pure hole`
/// continuation, itself its own `compile_db_lam_ir` call, compiled
/// right after an EARLIER nested do-block's own lambda already reset
/// the ctx) silently loses every local bound BEFORE that first lambda
/// (a `let n := 5` two statements up) -- its own free-variable capture
/// then finds `n` nowhere in `ctx_lookup_local` at all (not even as a
/// missed-capture bug; the outer LOCAL BINDING itself is gone from the
/// ctx by this point), so `n` gets treated as an unknown GLOBAL name
/// instead and silently miscompiles into a bogus 0-arg call
/// (`call i64 @n()`, `llc: use of undefined value '@n'`).
#[partial]
def ctx_restore_locals (outer : CodegenCtx) (inner : CodegenCtx) : CodegenCtx := { inner with locals := outer.locals }

/// Looks up a global's own known arity by its already-mangled
/// `llvm_name` (see `CodegenCtx.arities`'s doc comment). `Option.none`
/// for any name not in the table -- a name genuinely absent from the
/// compiled module's own def list (shouldn't happen for a real reachable
/// reference) as well as for a module compiled via `empty_ctx
/// empty_arities` (no table built) both fall back safely to the
/// pre-Phase-0 eager-0-arg-call behavior at the one call site that reads
/// this (`compile_db_term_ir`'s `Term.var` value-position case) --
/// correct for 0-arity defs, and no worse than before Phase 0 for
/// anything else. A direct `str_map_lookup` -- this table is built ONCE
/// per module compile and looked up once per `Term.var` reference across
/// the whole compiled program, the same shape `ctor_tags`/
/// `filter_reachable` already measured as a decisive HashMap win over a
/// `List`+linear-scan at this corpus's scale.
#[partial]
def ctx_lookup_arity (c : CodegenCtx) (llvm_name : String) : Option I64 := str_map_lookup llvm_name c.arities

/// Builds the arity table `empty_ctx` needs from a module's own `List
/// Def`, keyed by the exact same `llvm_name` `compile_db_def_ir` gives
/// each def's own compiled LLVM function (`def_symbol_name` of its
/// module-qualified name) -- callers (`compile_db_decls_ir`/
/// `compile_db_module`) always have the full `List Def` in scope before
/// compiling any of them, so this runs once per module compile, not per
/// reference.
#[partial]
def build_arity_table (defs : List Def) : HashMap String I64 := build_arity_table_go defs str_map_empty

#[partial]
def build_arity_table_go (defs : List Def) (acc : HashMap String I64) : HashMap String I64 := match defs {
    List.empty => acc,
    List.cons d rest =>
        match d {
            Def.mk name typ term_ constraints attrs _vis =>
                let llvm_name := def_symbol_name name in
                let arity := List.length (collect_db_params term_) in
                build_arity_table_go rest (str_map_insert llvm_name arity acc),
        },
}

/// (The v1 def-name -> `Location` table built here -- `build_debug_locs`
/// -- is gone: since stage 6 a function's own location is the `Term.ctx`
/// wrapper on its body, which every located def carries by construction,
/// so there is no table to build and no second file read to feed it.)

#[partial]
def lookup_binding (bindings : List LocalBinding) (name : Identifier) : Option LLVMValue := match bindings {
    List.empty => Option.none,
    List.cons b rest =>
        match b {
            { name := lname, val := lval } =>
                if identifier_eq lname name
                then Option.some lval
                else lookup_binding rest name,
        },
}

/// Collect lambda params from a de Bruijn Term body.
/// Strips `Term.lam` prefixes and returns Param for each.
// Peels. This walk derives a compiled function's PARAMETER COUNT by
// counting `Term.lam`s, so a location wrapper interposed between two lams
// truncates the list and emits a function with the wrong arity -- which
// `llc` accepts and the linker does not. Placement rule R2 says a wrapper
// never lands here; this peels anyway, because one call is cheap and the
// failure is not.
#[partial]
def collect_db_params (term_ : Term) : List Param := match term_peel term_ {
    Term.lam dbg typ body =>
        let name : Identifier := match dbg {
            DebugName.named id => id,
            DebugName.unnamed => Identifier.id "x",
        } in
        let param_ := param_many name typ in
        List.cons param_ (collect_db_params body),
    Term.forall dbg kind body => collect_db_params body,
    _ => List.empty,
}