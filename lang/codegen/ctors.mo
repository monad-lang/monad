/// Constructor tags and arities.
///
/// A constructor's runtime tag and field count are keyed in their OWN
/// namespace, not the def-symbol one: `MatchCase` carries only a bare
/// `Identifier` (the parser parses `Slim.mk` and discards the
/// qualifier), so dispatch can never supply more than a bare name.
///
/// Tags are therefore keyed three ways at one build site: the composite
/// `bare#arity`, the owner-qualified `Type.ctor` alias, and the bare
/// name -- the last carrying a `-1` ambiguity sentinel when two types
/// claim it at different arities. Keying by bare name ALONE is what
/// once put 283 constructors on one tag at seven arities and sized
/// allocations wrongly; the builtin tiers are checked for a matching
/// arity for the same reason.
use lang.types {InductConstructor, Inductive}
use lang.codegen.ctx {CodegenCtx, ctx_lookup_ctor_arity, ctx_lookup_ctor_tag}
use lang.codegen.symbols {extract_base_name, module_path_to_str}
use lang.codegen.util {str_map_empty, str_map_insert, str_map_lookup}
use std.map {}

/// The ~16 builtin constructors' tags (0-15), keyed by BOTH their
/// qualified ("IO.io") and base ("io") name forms -- built once, looked
/// up via `str_map_lookup` instead of a hand-rolled `if/else-if` chain.
/// Tags match the runtime's own assignment; left completely unchanged
/// from the original hardcoded chain this replaces -- zero risk to
/// already-working code, purely a readability/dispatch-mechanism change.
#[partial]
def builtin_ctor_tags : HashMap String I64 :=
    let m := str_map_empty in
    let m := str_map_insert "IO.io" 7 m in
    let m := str_map_insert "Unit.unit" 0 m in
    let m := str_map_insert "Bool.true" 1 m in
    let m := str_map_insert "Bool.false" 2 m in
    let m := str_map_insert "Option.none" 3 m in
    let m := str_map_insert "Option.some" 4 m in
    let m := str_map_insert "List.empty" 5 m in
    let m := str_map_insert "List.cons" 6 m in
    let m := str_map_insert "unit" 0 m in
    let m := str_map_insert "true" 1 m in
    let m := str_map_insert "false" 2 m in
    let m := str_map_insert "none" 3 m in
    let m := str_map_insert "some" 4 m in
    let m := str_map_insert "empty" 5 m in
    let m := str_map_insert "cons" 6 m in
    let m := str_map_insert "io" 7 m in
    let m := str_map_insert "trivial" 8 m in
    let m := str_map_insert "refl" 9 m in
    let m := str_map_insert "ok" 10 m in
    let m := str_map_insert "err" 11 m in
    let m := str_map_insert "zero" 12 m in
    let m := str_map_insert "succ" 13 m in
    let m := str_map_insert "nil" 14 m in
    let m := str_map_insert "pair" 15 m in
    // `std/array.mo`'s `Array.mk`/`ArrayBuilder.mk`. A builtin tag,
    // even though the type is declared in `std/` rather than `init/`,
    // because `runtime.c`'s `monad_array_*` ALLOCATE one directly and
    // a C function cannot consult the per-program constructor
    // numbering. The two share a tag deliberately: they are the same
    // representation (`std/array.mo`'s own doc comment), and
    // `array_freeze` converts between them by copying, never by
    // re-tagging.
    //
    // NOTE the arity subtlety: unlike every other entry here, an
    // `Array`'s field count is its LENGTH, not a fixed number, so
    // `builtin_ctor_arities` records 0 -- the arity a bare, unapplied
    // `Array.mk` really has. Only the natives allocate longer ones.
    let m := str_map_insert "Array.mk" 16 m in
    let m := str_map_insert "ArrayBuilder.mk" 16 m in
    m

/// Field counts for the same builtin constructors `builtin_ctor_tags`
/// enumerates -- needed by `constructor_arity` (see its own doc comment
/// for why: a bare, unapplied reference to an arity>0 constructor, e.g.
/// `List.map Option.some xs`, needs to know it must box a real closure,
/// not just allocate a 0-field object).
#[partial]
def builtin_ctor_arities : HashMap String I64 :=
    let m := str_map_empty in
    let m := str_map_insert "IO.io" 1 m in
    let m := str_map_insert "Unit.unit" 0 m in
    let m := str_map_insert "Bool.true" 0 m in
    let m := str_map_insert "Bool.false" 0 m in
    let m := str_map_insert "Option.none" 0 m in
    let m := str_map_insert "Option.some" 1 m in
    let m := str_map_insert "List.empty" 0 m in
    let m := str_map_insert "List.cons" 2 m in
    let m := str_map_insert "unit" 0 m in
    let m := str_map_insert "true" 0 m in
    let m := str_map_insert "false" 0 m in
    let m := str_map_insert "none" 0 m in
    let m := str_map_insert "some" 1 m in
    let m := str_map_insert "empty" 0 m in
    let m := str_map_insert "cons" 2 m in
    let m := str_map_insert "io" 1 m in
    let m := str_map_insert "trivial" 0 m in
    let m := str_map_insert "refl" 0 m in
    let m := str_map_insert "ok" 1 m in
    let m := str_map_insert "err" 1 m in
    let m := str_map_insert "zero" 0 m in
    let m := str_map_insert "succ" 1 m in
    let m := str_map_insert "nil" 0 m in
    let m := str_map_insert "pair" 2 m in
    // See `builtin_ctor_tags`' note: 0 is the arity of a bare
    // `Array.mk`, which is also the empty array. A populated one's
    // field count comes from `alloc_constructor`, not from here.
    let m := str_map_insert "Array.mk" 0 m in
    let m := str_map_insert "ArrayBuilder.mk" 0 m in
    m

/// Falls back to `c`'s own dynamically-built `ctor_tags` table
/// (`build_constructor_tag_map`) for anything not in `builtin_ctor_tags`
/// -- every user-defined inductive's constructor, and any BUILTIN
/// constructor referenced by its full dotted name in a shape
/// `builtin_ctor_tags` doesn't happen to enumerate. The ctx tiers try
/// the name AS WRITTEN first ("Box.mk" -- the map carries an
/// owner-qualified alias per constructor) and then its bare name --
/// which for a bare name claimed at several arities is the -1
/// ambiguity sentinel, answered as 0 by `bare_ctor_tag`. Callers that
/// know the constructor's field count should use `constructor_tag_at`
/// instead: its composite bare#arity key distinguishes the differing-
/// arity colliders this bare-name path cannot.
#[partial]
def constructor_tag (c : CodegenCtx) (name : String) : I64 :=
    let base_name := extract_base_name name in
    match str_map_lookup name builtin_ctor_tags {
        Option.some tag => tag,
        Option.none =>
            match str_map_lookup base_name builtin_ctor_tags {
                Option.some tag => tag,
                Option.none =>
                    match ctx_lookup_ctor_tag c name {
                        Option.some tag => tag,
                        Option.none => bare_ctor_tag c base_name,
                    },
            },
    }

/// Same 3-tier lookup shape as `constructor_tag` just above (hardcoded
/// builtin table, by full name then base name, then `c`'s own
/// dynamically-built table -- name as written, then bare), for a
/// constructor's FIELD COUNT instead of its tag. Needed by
/// `compile_db_term_ir`'s `Term.var` case (a bare, unapplied
/// constructor reference in VALUE position, e.g. `List.map Identifier.id
/// ids` or `List.map Option.some xs`): that case used to
/// unconditionally allocate a 0-field object regardless of the
/// constructor's REAL declared arity, correct only for a genuinely
/// nullary constructor -- confirmed as a real gap via a live self-
/// compiled binary's own SIGSEGV (jumping to a garbage function pointer
/// inside `List.map`'s `apply_closure1`, traced to `ids_to_module_path`'s
/// own `List.map Identifier.id ids`, a 1-field constructor referenced
/// bare). The ctx tiers key `ctor_arities` by the owner-qualified
/// alias first ("Box.mk" -- how such a reference is actually written)
/// and the bare name second; a bare name claimed at several arities
/// records its FIRST-encountered arity there -- an arbitrary but
/// deterministic answer for a shape that is genuinely unresolvable
/// without the owning type (write the reference qualified and the
/// alias tier answers exactly). Falls back to 0 (matching
/// `constructor_tag`'s own "unknown -> 0" fallback) if the name isn't
/// found anywhere -- a name that isn't even a known constructor never
/// reaches this function to begin with (`is_constructor_var` already
/// gated the caller).
#[partial]
def constructor_arity (c : CodegenCtx) (name : String) : I64 :=
    let base_name := extract_base_name name in
    match str_map_lookup name builtin_ctor_arities {
        Option.some arity => arity,
        Option.none =>
            // The owner-qualified ctx alias ("CompileResult.ok") is tried
            // BEFORE the bare-name builtin tier, for the same reason
            // `constructor_tag_at` reorders its own tiers: a user
            // constructor sharing a builtin's bare name would otherwise
            // report the BUILTIN's field count and allocate the wrong
            // size. The full-name builtin tier above still wins for a
            // genuine "Result.ok".
            match ctx_lookup_ctor_arity c name {
                Option.some arity => arity,
                Option.none =>
                    match str_map_lookup base_name builtin_ctor_arities {
                        Option.some arity => arity,
                        Option.none =>
                            match ctx_lookup_ctor_arity c base_name {
                                Option.some arity => arity,
                                Option.none => 0,
                            },
                    },
            },
    }

/// Check if a variable name is a known constructor.
/// Handles both simple names ("unit", "true") and qualified names ("Unit.unit", "IO.io"),
/// falling back to `c`'s own dynamically-built `ctor_tags` table
/// (`build_constructor_tag_map`) for anything not in `builtin_ctor_tags`
/// -- see `constructor_tag`'s own doc comment. A bare name claimed at
/// several arities still has a ctx-table entry (the -1 ambiguity
/// sentinel, see `constructor_tag_at`) -- presence alone answers this
/// question.
#[partial]
def is_constructor_var (c : CodegenCtx) (name : String) : Bool :=
    let base_name := extract_base_name name in
    match str_map_lookup base_name builtin_ctor_tags {
        Option.some _ => true,
        Option.none =>
            match ctx_lookup_ctor_tag c base_name {
                Option.some _ => true,
                Option.none => false,
            },
    }

/// The composite tag-map key: a constructor's BARE name plus its
/// declared field count, joined by `#` ("mk#7", "present#2"). `#` never
/// appears in an identifier, so the composite key can never collide
/// with a qualified "Type.ctor" alias or a bare name. This is the key
/// that makes same-bare-name constructors at DIFFERING arities
/// distinguishable at runtime -- see `build_constructor_tag_map`.
def ctor_composite_key (name : String) (arity : I64) : String :=
    String.concat name (String.concat "#" (I64.to_string arity))

/// The ctx-table's bare entry, answered as a tag. A bare constructor
/// name claimed at exactly ONE arity has a real tag here; one claimed at
/// several arities gets the -1 ambiguity sentinel instead (see
/// `constructor_tag_at`), which this answers as 0 -- the same "unknown"
/// answer a missing entry gets, and unreachable for real shapes, since
/// every caller that knows its arity goes through the composite key
/// first.
#[partial]
def bare_ctor_tag (c : CodegenCtx) (bare : String) : I64 :=
    match ctx_lookup_ctor_tag c bare {
        Option.some tag => if I64.gt tag (-1) then tag else 0,
        Option.none => 0,
    }

/// One constructor "claim" collected from the declared `Inductive`s:
/// the constructor's BARE rendered name (how match dispatch will refer
/// to it), its declared FIELD COUNT (how the composite key
/// disambiguates colliders), and its owner-QUALIFIED name
/// ("TypeName.ctorName" -- how a value-position reference is written).
struct CtorClaim {
    bare : String,
    arity : I64,
    qualified : String,
}

/// Collect every declared constructor's claim, in declaration order.
/// `Inductive.name` is the OWNING type's path -- the qualifier every
/// `mk`-shaped bare name needs to become unique.
#[partial]
def collect_ctor_claims (owner : String) (ctors : List InductConstructor) (acc : List CtorClaim) : List CtorClaim := match ctors {
    List.empty => acc,
    List.cons c rest =>
        match c {
            InductConstructor.mk name params _typ =>
                let claim : CtorClaim := {
                    bare := module_path_to_str name,
                    arity := List.length params,
                    qualified := String.concat owner (String.concat "." (module_path_to_str name)),
                } in
                collect_ctor_claims owner rest (List.cons claim acc),
        },
}

#[partial]
def collect_ctor_claims_inds (inds : List Inductive) (acc : List CtorClaim) : List CtorClaim := match inds {
    List.empty => acc,
    List.cons ind rest =>
        match ind {
            Inductive.mk name _params _typ constructors _attrs _vis =>
                collect_ctor_claims_inds rest (collect_ctor_claims (module_path_to_str name) constructors acc),
        },
}

/// The per-bare-name arity scan every map build starts with: the FIRST
/// arity each bare name was claimed at, and whether it was later
/// claimed at a DIFFERENT arity too (the ambiguity marker -- a bare
/// name with several arities cannot answer an arity-unknown lookup and
/// gets the -1 sentinel in the tag map).
struct BareArityScan {
    first : HashMap String I64,
    multi : HashMap String Bool,
}

#[partial]
def scan_ctor_bare_arities (claims : List CtorClaim) (st : BareArityScan) : BareArityScan := match claims {
    List.empty => st,
    List.cons cl rest =>
        match cl {
            CtorClaim.mk bare arity _qualified =>
                let st2 := match str_map_lookup bare st.first {
                    Option.some first =>
                        if arity == first
                        then st
                        else { st with multi := str_map_insert bare true st.multi },
                    Option.none => { st with first := str_map_insert bare arity st.first },
                } in
                scan_ctor_bare_arities rest st2,
        },
}

struct CtorTagBuildState {
    next_tag : I64,
    tags : HashMap String I64,
}

/// Assign one fresh, globally-unique tag per DISTINCT bare#arity pair,
/// first-encounter order. Duplicate claims (the same pair again, a
/// module loaded twice, another type with the same-named same-arity
/// constructor) reuse the tag -- same-layout claimants are
/// interchangeable at runtime by construction, since alloc and match
/// both key by (name, arity).
#[partial]
def assign_ctor_pair_tags (claims : List CtorClaim) (st : CtorTagBuildState) : CtorTagBuildState := match claims {
    List.empty => st,
    List.cons cl rest =>
        match cl {
            CtorClaim.mk bare arity _qualified =>
                let comp := ctor_composite_key bare arity in
                let st2 := match str_map_lookup comp st.tags {
                    Option.some _ => st,
                    Option.none => { st with tags := str_map_insert comp st.next_tag st.tags, next_tag := st.next_tag + 1 },
                } in
                assign_ctor_pair_tags rest st2,
        },
}

/// Add the two alias keys every claim also gets, on top of the
/// composite keys: the owner-qualified name ("Box.mk" -> Box's own
/// tag -- the tier a value-position reference written qualified hits)
/// and the bare name (real tag when the name is claimed at one single
/// arity, the -1 ambiguity sentinel when claimed at several -- so
/// `is_constructor_var` still sees presence, while arity-unknown tag
/// lookups degrade to 0 rather than silently answering one claimant).
#[partial]
def add_ctor_alias_tags (claims : List CtorClaim) (scan : BareArityScan) (tags : HashMap String I64) : HashMap String I64 := match claims {
    List.empty => tags,
    List.cons cl rest =>
        match cl {
            CtorClaim.mk bare arity qualified =>
                let comp := ctor_composite_key bare arity in
                let tag := match str_map_lookup comp tags {
                    Option.some t => t,
                    Option.none => 0,
                } in
                let bare_entry := match str_map_lookup bare scan.multi {
                    Option.some amb => if amb then (-1) else tag,
                    Option.none => tag,
                } in
                add_ctor_alias_tags rest scan (str_map_insert bare bare_entry (str_map_insert qualified tag tags)),
        },
}

/// Builds `ctor_tags` for every constructor of every declared
/// `Inductive` in the whole program, keyed THREE ways:
///
///   - `bare#arity` (the composite key -- `constructor_tag_at`'s ctx
///     tier): one fresh tag per distinct pair, so constructors sharing
///     a bare name at differing arities -- the 283-way `mk` collision
///     that cost the v29 rung-3 ladder rung -- get DIFFERENT tags and
///     can never be confused at alloc or match dispatch;
///   - `TypeName.ctorName` (the owner-qualified alias --
///     `constructor_tag`/`constructor_arity`'s ctx tier): the shape a
///     value-position reference is actually written in;
///   - the bare name alone (last-resort tier): real tag when claimed
///     at one arity, -1 sentinel when ambiguous.
///
/// Starts at 16 -- past `constructor_tag`'s existing hardcoded 0-15
/// builtin range (`unit, true, false, none, some, empty, cons, io,
/// trivial, refl, ok, err, zero, succ, nil, pair`), which is left
/// completely untouched -- those tiers are consulted BEFORE this map.
/// Matching a bare name with its arity at every alloc/dispatch site is
/// what makes the composite key sufficient without threading the
/// scrutinee's static type into match compilation (`MatchCase` carries
/// only the bare Identifier -- the parser accepts and drops the
/// qualifier -- but it also carries the case's own binder list, which
/// IS the arity; see `build_match_chain`).
/// See `implementations/2026-08-29-user-defined-constructor-codegen-gap.md`
/// for the map's original single-key design.
#[partial]
def build_constructor_tag_map (inds : List Inductive) : HashMap String I64 :=
    let claims := List.reverse (collect_ctor_claims_inds inds List.empty) in
    let scan := scan_ctor_bare_arities claims { first := str_map_empty, multi := str_map_empty } in
    let assigned := assign_ctor_pair_tags claims { next_tag := 16, tags := str_map_empty } in
    add_ctor_alias_tags claims scan assigned.tags

/// Mirrors `build_constructor_tag_map`'s qualified/bare alias keying
/// (built from the same claim scan) but records each constructor's
/// FIELD COUNT instead of its tag -- see `constructor_arity`'s own doc
/// comment for why this is needed. A bare name claimed at several
/// arities records its FIRST-encountered arity under the bare key --
/// arbitrary but deterministic; write such references qualified.
#[partial]
def build_constructor_arity_map (inds : List Inductive) : HashMap String I64 :=
    let claims := List.reverse (collect_ctor_claims_inds inds List.empty) in
    let scan := scan_ctor_bare_arities claims { first := str_map_empty, multi := str_map_empty } in
    add_ctor_arity_keys claims scan str_map_empty

#[partial]
def add_ctor_arity_keys (claims : List CtorClaim) (scan : BareArityScan) (acc : HashMap String I64) : HashMap String I64 := match claims {
    List.empty => acc,
    List.cons cl rest =>
        match cl {
            CtorClaim.mk bare arity qualified =>
                let bare_entry := match str_map_lookup bare scan.multi {
                    Option.some amb =>
                        if amb
                        then match str_map_lookup bare scan.first {
                            Option.some first => first,
                            Option.none => arity,
                        }
                        else arity,
                    Option.none => arity,
                } in
                add_ctor_arity_keys rest scan (str_map_insert bare bare_entry (str_map_insert qualified arity acc)),
        },
}
