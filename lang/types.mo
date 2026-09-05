use std.show {Show}
// `ScopeData.def_refs` below is a `std.map` `HashMap ModulePath ScopeDef`.
// This import is required here (not just at `scope_data_empty`'s own
// call sites in `lang/scope.mo`) — a real, isolated evaluator
// limitation: a nullary class method like `Map.empty` (no argument
// whose runtime constructor tag the interpreter could otherwise
// dispatch on, unlike `Map.insert`/`Map.lookup`) fails at runtime with
// `unresolved global: Map.empty` unless `std.map`'s `Map` instances are
// also in scope in the module that DECLARES the struct field's type,
// even when every call site already imports `std.map` itself. Empty
// import: naming any of `std.map`'s `Map`-class-instance exports
// explicitly hits a separate, pre-existing latent instance/dictionary-
// resolution bug (`std/map_tests.mo`'s own documented workaround).
use std.map {}
use std.list {intercalate}

type Identifier {
    id String
}

/// Compare two identifiers for equality (by string value).
def id_eq (a : Identifier) (b : Identifier) : Bool :=
    match a {
        Identifier.id as => match b {
            Identifier.id bs => String.beq as bs,
        },
    }

instance BEq Identifier {
    def beq (a b : Identifier) : Bool := id_eq a b
}


/// Check if an identifier is in a list of identifiers.
def id_member (id : Identifier) (ids : List Identifier) : Bool :=
    match ids {
        List.cons hd rest => if id_eq id hd then true else id_member id rest,
        List.empty => false,
    }

/// Union two lists of identifiers (deduplicated, left-biased order).
def union_ids (a : List Identifier) (b : List Identifier) : List Identifier :=
    match a {
        List.cons hd rest =>
            if id_member hd b
            then union_ids rest b
            else List.cons hd (union_ids rest b),
        List.empty => b,
    }
/// An argument to a `#[name arg1 arg2 ...]` attribute. Mirrors the Rust
/// reference's `AttrArg` (core/src/term.rs) exactly, including the
/// `named`/`group` shapes (`{name := value}` / `[item, ...]`) even
/// though no real corpus attribute uses either yet — the combinator
/// cost of supporting them now is near-zero and avoids a later
/// breaking retype of `Attribute.args` once one does.
type AttrArg {
    ident (id: Identifier),
    str (value: String),
    num (value: I64),
    named (name: Identifier) (value: AttrArg),
    group (items: List AttrArg),
}

/// A single `#[name arg1 arg2 ...]` declaration/param annotation, e.g.
/// `#[derive BEq BOrd Debug Lens]` — one `Attribute` with FOUR bare-
/// `ident` args (confirmed against the reference grammar: attribute
/// args are whitespace-separated and flattened onto the one attribute,
/// not four stacked attributes). Deliberately has no `source_location`
/// field (unlike the Rust reference's `Attribute`, whose own
/// `PartialEq` ignores that field anyway) — no sibling decl-level type
/// here (`Def`, `Inductive`, ...) carries source-location data, and
/// nothing downstream would read it.
struct Attribute {
    name: Identifier,
    args: List AttrArg,
}

/// The empty attribute list, under both names the corpus already uses
/// for it. Declared here, beside `Attribute` itself, because each was
/// previously declared TWICE -- `empty_attrs` in
/// `lang/typecheck/macro_queue.mo` and `lang/codegen/emit.mo`,
/// `no_attrs` in `lang/codegen/test_driver.mo` and
/// `lang/typecheck/meta_reflect.mo` -- so each was two definitions of
/// one LLVM symbol, of which the emitted binary silently kept one.
/// Both spellings are kept rather than picking a winner: the two names
/// read differently at their call sites (`no_attrs` for a synthesized
/// decl that HAS no attributes, `empty_attrs` for an accumulator's
/// zero) and unifying them is a rename sweep with no correctness value.
def empty_attrs : List Attribute := List.empty

def no_attrs : List Attribute := List.empty

/// Structural equality by name and args.
def attr_eq (a : Attribute) (b : Attribute) : Bool :=
    match a { Attribute.mk an aargs => match b { Attribute.mk bn bargs =>
        id_eq an bn && attr_args_eq aargs bargs,
    } }

def attr_args_eq (a : List AttrArg) (b : List AttrArg) : Bool :=
    match a {
        List.empty => match b { List.empty => true, List.cons _ _ => false },
        List.cons ah arest => match b {
            List.empty => false,
            List.cons bh brest => attr_arg_eq ah bh && attr_args_eq arest brest,
        },
    }

def attr_arg_eq (a : AttrArg) (b : AttrArg) : Bool :=
    match a {
        AttrArg.ident ai => match b { AttrArg.ident bi => id_eq ai bi, _ => false },
        AttrArg.str av => match b { AttrArg.str bv => String.beq av bv, _ => false },
        AttrArg.num av => match b { AttrArg.num bv => I64.beq av bv, _ => false },
        AttrArg.named an av => match b { AttrArg.named bn bv => id_eq an bn && attr_arg_eq av bv, _ => false },
        AttrArg.group aitems => match b { AttrArg.group bitems => attr_args_eq aitems bitems, _ => false },
    }

instance BEq Attribute {
    def beq (a b : Attribute) : Bool := attr_eq a b
}

/// Whether `attrs` contains an attribute named `name`, e.g.
/// `has_attr (Identifier.id "derive_cli") ind_attrs`. Mirrors the Rust
/// reference's `Inductive::has_attr`/`Def::has_test_attr`
/// (core/src/term.rs).
def has_attr (name : Identifier) (attrs : List Attribute) : Bool :=
    match attrs {
        List.cons hd rest =>
            match hd { Attribute.mk n _ => if id_eq n name then true else has_attr name rest },
        List.empty => false,
    }

type Operator {
    operator String
}

type ModulePath {
    mp (List Identifier)
}

def show_identifier (id : Identifier) : String := match id {
    Identifier.id s => s,
}

def show_operator (op : Operator) : String := match op {
    Operator.operator s => s,
}

def show_module_path (mp : ModulePath) : String := match mp {
    ModulePath.mp ids => join_identifiers ids,
}

/// Join a module path's segments with `.` (`[Foo, bar]` -> `Foo.bar`).
/// For the LLVM symbol-name form (`Foo__bar`) see
/// `lang/codegen/emit.mo`'s `mangle_identifiers`.
def join_identifiers (ids : List Identifier) : String :=
    List.intercalate "." (List.map show_identifier ids)


instance Show ModulePath {
    def show (mp : ModulePath) : String := show_module_path mp
}

/// Identifiers can't contain ".", so the dotted-string-join used by
/// show_identifier/show_module_path is collision-free as an ordering key.
instance BOrd Identifier {
    def lt (a b : Identifier) : Bool := BOrd.lt (show_identifier a) (show_identifier b)
    def gt (a b : Identifier) : Bool := BOrd.gt (show_identifier a) (show_identifier b)
}

instance BOrd ModulePath {
    def lt (a b : ModulePath) : Bool := BOrd.lt (show_module_path a) (show_module_path b)
    def gt (a b : ModulePath) : Bool := BOrd.gt (show_module_path a) (show_module_path b)
}

/// Same "collision-free as a string key" property `BOrd`'s own
/// delegation above already relies on — hash the dotted-string join
/// rather than writing a separate combining hash over the segment list.
/// Needed for `lang/scope.mo`'s `ScopeData.def_refs` to use
/// `std.map`'s `HashMap ModulePath ScopeDef` (see
/// `bench/scope_lookup.mo` for why: at realistic sizes, `HashMap`
/// clearly outperforms both `List`+linear-scan and `BTreeMap` for
/// scope's lookup-heavy access pattern).
instance Hashable Identifier {
    def hash (a : Identifier) : U64 := String.hash (show_identifier a)
}

instance Hashable ModulePath {
    def hash (mp : ModulePath) : U64 := String.hash (show_module_path mp)
}

type NameRef {
    nid (Identifier),
    nmp (ModulePath),
    nop (Operator),
}

type Multiplicity {
    zero,
    many,
    linear,
    affine,
}

struct Location {
    offset : I64,
    line : I64,
    column : I64,
}

struct SourceRange {
    start : Location,
    end : Location,
    path : Option String,
}

struct LocatedSpan {
    fragment : String,
    location : Location,
}

// Canonical Param uses de Bruijn Term; `ParseParam` is the parser's.
type Param {
    mk (name: Identifier) (type_: Term) (mult: Multiplicity) (default: Option Term) (attrs: List Attribute)
}

/// Create a canonical Param with multiplicity=Many, no default value, and
/// no attributes.
def parse_param_many (name: Identifier) (type_: ParseTerm) : ParseParam :=
    let none : Option ParseTerm := Option.none in
    let no_attrs : List Attribute := List.empty in
    ParseParam.mk name type_ Multiplicity.many none no_attrs

/// Canonical sibling of `parse_param_many`, for code that already holds
/// a lowered `Term`.
#[partial]
def param_many (name: Identifier) (type_: Term) : Param :=
    let none : Option Term := Option.none in
    let no_attrs : List Attribute := List.empty in
    Param.mk name type_ Multiplicity.many none no_attrs

/// Create a canonical Param with explicit multiplicity, no default
/// value, and no attributes.
pub def mk_param (name: Identifier) (type_: Term) (mult: Multiplicity) : Param :=
    let none : Option Term := Option.none in
    let no_attrs : List Attribute := List.empty in
    Param.mk name type_ mult none no_attrs

/// Create a canonical Param with multiplicity=Many, no default value,
/// and explicit attrs — the one constructor/def-param path that
/// actually needs a non-empty `attrs` list (e.g. `#[arg]`).
pub def param_with_attrs (name: Identifier) (type_: Term) (attrs: List Attribute) : Param :=
    let none : Option Term := Option.none in
    Param.mk name type_ Multiplicity.many none attrs

// Canonical MatchCase uses de Bruijn Term; `ParseMatchCase` is the parser's.
//
// `field_pattern` mirrors the Rust reference's `MatchCase.field_pattern`
// (core/src/term.rs, `plans/implementations/struct-field-destructuring.md`):
// `Option.some` only pre-elaboration, when this case was parsed as a
// `{ x, y } => ...`/`ConsName { x, y } => ...` field-pattern rather than
// the ordinary positional form (`ConsName x y => ...`). `args`/`body` for
// a field-pattern case are indexed in the pattern's WRITTEN field order
// at PARSE time (`match_case_arrow`'s own `lambda_extend_ctx` call,
// `lang/parser.mo` -- this file's canonical `Term` is de Bruijn from the
// parser onward, unlike the Rust reference's separate parse-then-lower
// split, so there is no later "lowering" pass to defer this to the way
// the reference's own `CoreMatchCase.field_pattern` doc comment
// describes). `lang/typecheck/infer.mo`'s `type_check_match_case`
// resolves this once the scrutinee's real constructor is known,
// retargeting `args`/`body` onto the constructor's true declared order
// (`lang/typecheck/subst.mo`'s `term_permute`, mirroring the reference's
// own `core_term::permute_binders`) and clearing this back to
// `Option.none` -- every OTHER consumer (`lang/lower_core_ir.mo`,
// `lang/codegen/emit.mo`, `lang/pretty.mo`'s runtime-facing paths) only
// ever sees `Option.none` here.
type MatchCase {
    mc (name: Identifier) (args: List Identifier) (body: Term) (field_pattern: Option FieldPattern)
}

/// One `{ field, other := binder, .. }` pattern -- mirrors the Rust
/// reference's `FieldPattern` (core/src/term.rs). `fields` is
/// `(field_name, binder)` in the order written; `binder` equals
/// `field_name` when punned (`{ x }`). `rest` is `true` when a trailing
/// `..` is present (unlisted fields are discarded, not brought into
/// scope).
type FieldPattern {
    mk (fields: List FieldPatternEntry) (rest: Bool)
}

/// One `field` or `field := binder` entry inside a `FieldPattern` --
/// a dedicated named-pair type (mirroring `StructLitField`'s own
/// `name`/`value` shape) rather than a generic `Pair`, so this file
/// doesn't need a cross-module dependency on `init/prelude.mo`'s `Pair`
/// for its own canonical AST.
type FieldPatternEntry {
    mk (field: Identifier) (binder: Identifier)
}

/// A single `def` parameter as parsed: either an ordinary explicit param
/// (unchanged), or a destructured one (`({ x, y } : T)`,
/// `plans/implementations/struct-field-destructuring.md`'s Phase 8) --
/// paired with the `FieldPattern` a wrapping `match` needs to actually
/// bind `x`/`y` from the fixed-name `Param` this variant also carries.
/// Mirrors the Rust reference's own `ParsedParam` (`core/src/parser.rs`)
/// exactly, adapted to a fixed binder name (`__struct_param`) instead of
/// a gensym -- `lang/` has no gensym facility (see `lang/cli.mo`'s own
/// header comment for the established precedent of a fixed, prefixed
/// name standing in for one here). Kept as a thin wrapper (rather than
/// adding a pattern slot to `Param` itself) so every OTHER `Param`
/// consumer needs no changes at all -- a `destructured` entry's own
/// `Param` is an ordinary, real binder by the time it reaches any of
/// them; only the `def` parameter chain in `lang/parser.mo` ever
/// inspects the `FieldPattern` half, to wrap the body in one extra
/// `match` per `destructured` param before building the final `Term.lam`
/// chain.
/// A parameter as WRITTEN, before lowering -- parse-stage, so it holds
/// `ParseParam`. Used only by `lang/parser.mo`.
type ParsedParam {
    plain (param: ParseParam),
    destructured (param: ParseParam) (fp: FieldPattern),
}

type NumSuffix {
    i8, i16, i32, i64, u8, u16, u32, u64, f32, f64,
}

// Canonical Literal uses de Bruijn Term; `ParseLiteral` is the parser's.
type Literal {
    str (value: String),
    num (value: I64) (suffix: NumSuffix),
    /// A literal written with a decimal point (`3.0`, `3.14f32`). Kept as
    /// the exact source text rather than a numeric value: self-hosted
    /// Monad code has no native bridge to parse a decimal string into an
    /// actual float bit pattern (unlike the Rust reference's
    /// `Literal::Float { value: F64Wrap, .. }`, core/src/term.rs), so
    /// `text` is the only representation available here — sufficient for
    /// round-tripping through `show_term`/parsing back, though genuine
    /// float codegen (`lang/codegen/emit.mo` has no float `LLVMValue`
    /// variant at all yet) remains a separate, unstarted piece of work.
    flt (text: String) (suffix: NumSuffix),
    if_ (one: Term) (two: Term) (three: Term),
    match_ (value: Term) (cases: List MatchCase),
    /// A struct-literal expression (`{ field := value, ... }`),
    /// optionally self-annotated with which struct it builds
    /// (`{ field := value, ... : StructName }`) — lets the checker
    /// resolve the struct name directly without needing an ambient
    /// expected type from context (a struct literal doesn't always have
    /// one, e.g. passed to a generic function). Mirrors the Rust
    /// reference's `CoreLit::StructLit` (core/src/core_term.rs).
    struct_lit (fields: List StructLitField) (type_name: Option Term),
    /// `{ base with field := value, ... }` — a copy of `base` (an
    /// existing struct VALUE, not a type name) with the listed fields
    /// replaced. `base` is a resolved `Term` (typically `Term.var`) here
    /// rather than a bare `Identifier`, unlike the Rust reference's own
    /// SOURCE-level `term::Literal::StructUpdate` — this checker has no
    /// separate parse-then-lower stage the way the reference's
    /// `Literal` (pre-lowering) vs `CoreLit` (post-lowering,
    /// `base: Box<CoreTerm>`) split does, so the parser resolves `base`
    /// directly, matching every other variable reference elsewhere in
    /// this file (`Term.var`/`variable`). Mirrors the Rust reference's
    /// `CoreLit::StructUpdate`.
    struct_update (base: Term) (fields: List StructLitField),
}

/// A single `name := value` field inside a struct-literal EXPRESSION
/// (`{ x := 1, y := 2 }`) — as distinct from `StructField`'s
/// DECLARATION shape (`x : T := default`). Mirrors one entry of the
/// Rust reference's `CoreLit::StructLit`'s `fields: Map<Identifier,
/// CoreTerm>`; order here doesn't matter (fields are matched by name)
/// — the struct's own declared field order (from its registered
/// `Param` list, see `build_scope_struct`) is what determines the
/// final constructor-argument order once `type_check_lit` resolves
/// this into a `Term.con`.
type StructLitField {
    mk (name: Identifier) (value: Term)
}

type Con {
    mk (name: Identifier) (typ_name: ModulePath) (num_args: I64) (args: List (Option Term))
}

type Native {
    mk (native_name: Identifier) (num_args: I64) (args: List (Option Term))
}

// Optional debug name carried by de Bruijn variables and binders.
// Names are never used for identity or equality — de Bruijn indices
// determine identity. DebugName exists solely for error messages
// and pretty-printing during debugging.
type DebugName {
    named (id: Identifier),
    unnamed,
}

/// Free-variable sentinel de Bruijn index: `>= 0` means bound, `-1`
/// means free/unresolved. The parser emits it for every not-yet-
/// resolved `Term.var`, and `lang.scope`/`lang.typecheck` compare
/// against it to decide whether a variable still needs resolving.
///
/// Declared here, in the module that owns `Term`/`DebugName`, because
/// it is part of that representation's contract rather than any one
/// pass's private constant. It previously existed as five byte-
/// identical copies (`lang/parser.mo`, `lang/elaborate.mo`,
/// `lang/lower_core_ir.mo`, `lang/typecheck/infer.mo`,
/// `lang/typecheck/meta_reflect.mo`); since codegen mangles a top-
/// level def to its BARE name, those five were five definitions of
/// one LLVM symbol `@sentinel`, of which the emitted binary silently
/// kept one -- see `validate_no_colliding_def_symbols`
/// (`lang/codegen/emit.mo`), which now rejects that shape outright.
def sentinel : I64 := -1

/// Visibility of a declaration. Mirrors the Rust reference's
/// `core::term::Visibility` exactly: `priv` is enforced immediately
/// (module boundaries already exist), `pub` vs. the default
/// `package_private` is a no-op until a package system exists. Applies to
/// `def`/`type`/`class`/`struct`/`instance`/`infix` — NOT `use` (which
/// gets its own separate `public: Bool` field directly on `Decl.use_d`,
/// since `priv use` isn't a real form) or `open` (no visibility concept
/// at all).
type Visibility {
    pub_,
    priv_,
    package_private,
}

// --- ParseTerm: the parser's own output, before de Bruijn resolution --
//
// The stage this compiler did not have. `Literal.struct_update`'s own doc
// comment (above) names the gap exactly: "this checker has no separate
// parse-then-lower stage the way the reference's `Literal`
// (pre-lowering) vs `CoreLit` (post-lowering) split does, so the parser
// resolves `base` directly".
//
// Two things distinguish a `ParseTerm` from the canonical `Term` below:
//
//   - **Named, not de Bruijn.** A variable is a `NameRef`, exactly as
//     written. The parser no longer computes de Bruijn indices inline
//     (`var_term`/`find_index`, `lang/parser.mo`) and no longer threads a
//     `ctx : List Identifier` through its grammar; binder structure is
//     recovered during lowering, where `lam`/`forall`/`pi`/`match_` arms
//     say what they bind.
//   - **Located.** Every node carries the source range it was parsed
//     from, which is the only place that information is cheaply
//     available.
//
// The span lives on the wrapper struct rather than being repeated on
// each variant, so a walk matches `.kind` once and a constructor sets
// `span` once. `Term` itself is deliberately NOT given locations: it is
// walked by `elaborate.mo`, `typecheck/subst.mo`, `traverse.mo`'s
// `term_map_children`, `infer.mo` and `emit.mo`, and it sits on the
// measured hot path (AGENTS.md item 27). Lowering emits positions into a
// side table instead.
//
// Replaces the `TermV0`/`ParamV0`/`MatchCaseV0`/`LiteralV0` family, which
// was a vestige: incomplete (no `quote_`, `var_macro`, `struct_lit`,
// `struct_update`), carrying a `ctx (loc) (term)` variant that was an
// abandoned attempt at exactly this feature, and reached only by
// `path_variable` building a `TermV0.var` that `variable_try_path_got`
// destructured straight back into a `Term`.

/// Where a `ParseTerm` came from, recorded as the LENGTH OF THE REMAINING
/// INPUT at the start and end of the construct.
///
/// Not an absolute offset, because no parser def sees the whole file --
/// each one is handed only the unconsumed remainder, and `whole_file`
/// exists nowhere in the grammar except `decls_parser_with_locs`. Both
/// numbers here are available locally and for free: `String.length input`
/// before a parser runs and `String.length rem` after it succeeds, each
/// an O(1) read on the `SharedStr` window the remainder actually is.
/// Recording an absolute offset instead would mean threading the file
/// (or its length) through all ~235 grammar defs -- re-adding exactly
/// the threading that dropping the de Bruijn `ctx` removes.
///
/// Converted to a real `SourceRange` only at the top level, where the
/// file IS known: `offset = total_length - start_rem`, then
/// `lang/parser/position.mo`'s divide-and-conquer scan for line/column.
/// Note the ordering is inverted from an offset -- a LARGER `start_rem`
/// means EARLIER in the file.
struct ParseSpan {
    start_rem : I64,
    end_rem : I64,
}

/// The span of a construct whose position has not been recorded. Distinct
/// from a zero-length span at end-of-input (`0`/`0`), which is a real
/// position.
def parse_span_unknown : ParseSpan := { start_rem := -1, end_rem := -1 }

#[partial]
def parse_span_is_unknown (sp : ParseSpan) : Bool :=
    I64.beq sp.start_rem -1

struct ParseTerm {
    span : ParseSpan,
    kind : ParseTermKind,
}

/// Build a `ParseTerm` whose position has not been recorded yet.
#[partial]
def pt_ (k : ParseTermKind) : ParseTerm :=
    { span := parse_span_unknown, kind := k }

/// Build a located `ParseTerm` from the input it started at and the
/// remainder it left, which is the shape every parser already has in
/// hand at the point it succeeds.
#[partial]
def pt_at (input : String) (rem : String) (k : ParseTermKind) : ParseTerm :=
    { span := { start_rem := String.length input, end_rem := String.length rem }, kind := k }


// Same-arity constructors for each kind, so converting a grammar site is
// a token rename (`Term.app` -> `pt_app`) rather than a wrap that would
// have to re-parenthesise the arguments. Span is the placeholder; a
// later pass swaps these for span-carrying forms.

#[partial]
def pt_var (n : NameRef) : ParseTerm := pt_ (ParseTermKind.var n)

#[partial]
def pt_var_macro (n : NameRef) : ParseTerm := pt_ (ParseTermKind.var_macro n)

#[partial]
def pt_lam (name : Identifier) (typ : ParseTerm) (body : ParseTerm) : ParseTerm :=
    pt_ (ParseTermKind.lam name typ body)

#[partial]
def pt_forall (name : Identifier) (typ : ParseTerm) (body : ParseTerm) : ParseTerm :=
    pt_ (ParseTermKind.forall name typ body)

#[partial]
def pt_pi (arg : ParseTerm) (ret : ParseTerm) : ParseTerm := pt_ (ParseTermKind.pi arg ret)

#[partial]
def pt_app (f : ParseTerm) (a : ParseTerm) : ParseTerm := pt_ (ParseTermKind.app f a)

#[partial]
def pt_lit (l : ParseLiteral) : ParseTerm := pt_ (ParseTermKind.lit l)

#[partial]
def pt_ntv (n : ParseNative) : ParseTerm := pt_ (ParseTermKind.ntv n)

#[partial]
def pt_con (c : ParseCon) : ParseTerm := pt_ (ParseTermKind.con c)

#[partial]
def pt_type_ (u : I64) : ParseTerm := pt_ (ParseTermKind.type_ u)

#[partial]
def pt_quote_ (t : ParseTerm) : ParseTerm := pt_ (ParseTermKind.quote_ t)

#[partial]
def pt_do (stmts : List ParseDoStmt) : ParseTerm := pt_ (ParseTermKind.do_ stmts)

def pt_hole : ParseTerm := pt_ ParseTermKind.hole


// --- The declaration half of the parse stage -------------------------
//
// Each mirrors its canonical twin with every `Term` replaced by
// `ParseTerm`, and mirrors its SHAPE too (a `type` with `mk` where the
// canonical one is a `type`, a `struct` where it is a struct) so that
// converting a grammar construction site is a rename rather than a
// rewrite.
//
// These exist because lowering cannot sit at the decl boundary. An
// earlier attempt assumed it could -- that `Decl`/`Def` keep holding
// `Term` and the change stays inside the expression parsers -- and it
// does not: `DoStmt`, `Param`, `StructField`, `InductConstructor`,
// `ClassDef`, `Def` and `Inductive` all embed `Term` and sit BETWEEN
// expressions and declarations. `ParseDoStmt` is the clearest case: it
// holds a term per statement and its binder context accumulates across
// statements, so there is no point at which one can be lowered without
// already having the `ctx` threading this whole change exists to remove.
//
// Not mirrored, checked rather than assumed: `TypeConstraint` (only a
// `ModulePath` and `Identifier`s), `Attribute`/`AttrArg` (no `Term`
// anywhere), `Operator`, `UseFilter`, `OpenFilter`, `Visibility`.

type ParseParam {
    mk (name: Identifier) (type_: ParseTerm) (mult: Multiplicity) (default: Option ParseTerm) (attrs: List Attribute)
}

/// Parse-stage `DoStmt`. Lowered to the canonical `DoStmt` and then
/// handed to the existing `desugar_do` below -- `DoStmt` is
/// parser-internal (only `desugar_do` and one test consume it), so
/// nothing downstream sees this type.
type ParseDoStmt {
    bind_s (name: Identifier) (typ: ParseTerm) (expr: ParseTerm),
    let_s (name: Identifier) (typ: ParseTerm) (expr: ParseTerm),
    ret_s (expr: ParseTerm),
    expr_s (expr: ParseTerm),
}

type ParseStructField {
    mk (name: Identifier) (typ: ParseTerm) (default: Option ParseTerm) (mult: Multiplicity)
}

type ParseInductConstructor {
    mk (name: ModulePath) (params: List ParseParam) (typ: ParseTerm)
}

type ParseClassDef {
    mk (name: Identifier) (typ: ParseTerm) (default: Option ParseTerm)
}

struct ParseDef {
    name: ModulePath,
    typ: ParseTerm,
    term: ParseTerm,
    constraints: List TypeConstraint,
    attrs: List Attribute,
    vis: Visibility
}

type ParseInductive {
    mk (name: ModulePath) (params: List ParseParam) (typ: ParseTerm) (constructors: List ParseInductConstructor) (attrs: List Attribute) (vis: Visibility)
}

type ParseClass {
    mk (name: Identifier) (params: List ParseParam) (constraints: List TypeConstraint) (methods: List ParseClassDef) (vis: Visibility)
}

type ParseInstance {
    mk (name: Identifier) (cls: ModulePath) (constraints: List TypeConstraint) (args: List ParseTerm) (vis: Visibility) (implicit_params: List ParseParam) (defs: List ParseDef)
}

type ParseStruct {
    mk (name: Identifier) (fields: List ParseStructField) (vis: Visibility)
}

/// A declaration plus the span it was parsed from.
///
/// The span is what collapses the two parallel top-level parsers into
/// one. `decls_parser_with_locs` currently re-derives each declaration's
/// position by measuring the remaining input against the whole file;
/// with a span recorded here that becomes a projection over what the
/// parser already knows -- at the top level the total length IS
/// available, so `offset = total_length - span.start_rem`, then
/// `lang/parser/position.mo`'s scan for line/column. Same arithmetic,
/// one parser instead of two.
struct ParseDecl {
    span : ParseSpan,
    kind : ParseDeclKind,
}

type ParseDeclKind {
    def_d (ParseDef),
    inductive_d (ParseInductive),
    struct_d (ParseStruct),
    class_d (ParseClass),
    instance_d (ParseInstance),
    infix_d (op: Operator) (path: ModulePath) (vis: Visibility),
    use_d (path: ModulePath) (filter: UseFilter) (public: Bool),
    open_d (path: ModulePath) (filter: OpenFilter),
    scoped_open_d (path: ModulePath) (filter: OpenFilter) (decl: ParseDecl),
    def_macro_d (ParseDef),
    decl_gen_d (name: ModulePath) (params: List ParseParam) (decl_list: List ParseDecl) (attrs: List Attribute),
    macro_call_d (name: Identifier) (args: List ParseTerm),
}

/// Build a `ParseDecl` whose position has not been recorded yet.
#[partial]
def pd_ (k : ParseDeclKind) : ParseDecl :=
    { span := parse_span_unknown, kind := k }

/// Build a located `ParseDecl` from the input it started at and the
/// remainder it left.
#[partial]
def pd_at (input : String) (rem : String) (k : ParseDeclKind) : ParseDecl :=
    { span := { start_rem := String.length input, end_rem := String.length rem }, kind := k }


// Same-arity constructors per declaration kind, for the same reason the
// `pt_*` family exists: a grammar site converts by renaming
// `Decl.def_d` -> `pd_def_d` rather than by a wrap that would have to
// re-parenthesise its argument. Span is the placeholder.

#[partial]
def pd_def_d (d : ParseDef) : ParseDecl := pd_ (ParseDeclKind.def_d d)

#[partial]
def pd_inductive_d (i : ParseInductive) : ParseDecl := pd_ (ParseDeclKind.inductive_d i)

#[partial]
def pd_struct_d (s : ParseStruct) : ParseDecl := pd_ (ParseDeclKind.struct_d s)

#[partial]
def pd_class_d (c : ParseClass) : ParseDecl := pd_ (ParseDeclKind.class_d c)

#[partial]
def pd_instance_d (i : ParseInstance) : ParseDecl := pd_ (ParseDeclKind.instance_d i)

#[partial]
def pd_infix_d (op : Operator) (path : ModulePath) (vis : Visibility) : ParseDecl :=
    pd_ (ParseDeclKind.infix_d op path vis)

#[partial]
def pd_use_d (path : ModulePath) (filter : UseFilter) (public : Bool) : ParseDecl :=
    pd_ (ParseDeclKind.use_d path filter public)

#[partial]
def pd_open_d (path : ModulePath) (filter : OpenFilter) : ParseDecl :=
    pd_ (ParseDeclKind.open_d path filter)

#[partial]
def pd_scoped_open_d (path : ModulePath) (filter : OpenFilter) (inner : ParseDecl) : ParseDecl :=
    pd_ (ParseDeclKind.scoped_open_d path filter inner)

#[partial]
def pd_def_macro_d (d : ParseDef) : ParseDecl := pd_ (ParseDeclKind.def_macro_d d)

#[partial]
def pd_decl_gen_d (name : ModulePath) (params : List ParseParam) (decl_list : List ParseDecl) (attrs : List Attribute) : ParseDecl :=
    pd_ (ParseDeclKind.decl_gen_d name params decl_list attrs)

#[partial]
def pd_macro_call_d (name : Identifier) (args : List ParseTerm) : ParseDecl :=
    pd_ (ParseDeclKind.macro_call_d name args)

type ParseTermKind {
    var (name: NameRef),
    /// Term-position `name!`. Kept a separate variant rather than a
    /// tagged `var` for the same reason `Term.var_macro` is (see its own
    /// doc comment): macro names resolve in a separate namespace.
    var_macro (name: NameRef),
    lam (name: Identifier) (typ: ParseTerm) (body: ParseTerm),
    forall (name: Identifier) (typ: ParseTerm) (body: ParseTerm),
    pi (arg: ParseTerm) (ret: ParseTerm),
    app (fun: ParseTerm) (arg: ParseTerm),
    lit (value: ParseLiteral),
    ntv (native: ParseNative),
    con (c: ParseCon),
    type_ (universe: I64),
    quote_ (term: ParseTerm),
    /// A `do { }` block, kept as STATEMENTS rather than desugared during
    /// parsing. Do-notation is syntax, so it belongs in the parse AST;
    /// `lower_parse_do` runs the existing `desugar_do` once the binder
    /// context is known. The grammar used to desugar inline, which is
    /// only possible while it also threads `ctx`.
    do_ (stmts: List ParseDoStmt),
    hole,
}

struct ParseMatchCase {
    name : Identifier,
    args : List Identifier,
    body : ParseTerm,
    field_pattern : Option FieldPattern,
}

type ParseLiteral {
    str (value: String),
    num (value: I64) (suffix: NumSuffix),
    flt (text: String) (suffix: NumSuffix),
    if_ (one: ParseTerm) (two: ParseTerm) (three: ParseTerm),
    match_ (value: ParseTerm) (cases: List ParseMatchCase),
    struct_lit (fields: List ParseStructLitField) (type_name: Option ParseTerm),
    /// `base` is a `ParseTerm` here for the same reason it is a `Term`
    /// in `Literal` -- it is an expression, not a name -- but at THIS
    /// stage it is still the unresolved one the source wrote.
    struct_update (base: ParseTerm) (fields: List ParseStructLitField),
}

struct ParseStructLitField {
    name : Identifier,
    value : ParseTerm,
}

type ParseCon {
    mk (name: Identifier) (typ_name: ModulePath) (num_args: I64) (args: List (Option ParseTerm))
}

type ParseNative {
    mk (native_name: Identifier) (num_args: I64) (args: List (Option ParseTerm))
}

// The canonical de Bruijn term IR — what everything after the parser
// works on. `ParseTerm` above is lowered into this.
//
// De Bruijn convention: index 0 = most recently bound variable.
// Free variables use sentinel index (I64.max) and are resolved
// by the type checker or module resolver.
type Term {
    var (idx: I64) (dbg: DebugName),
    lam (dbg: DebugName) (typ: Term) (body: Term),
    forall (dbg: DebugName) (kind: Term) (body: Term),
    pi (arg: Term) (ret: Term),
    app (fun: Term) (arg: Term),
    lit (value: Literal),
    ntv (native: Native),
    con (c: Con),
    type_ (universe: I64),
    hole,
    /// `quote { <term> }` -- syntax as data. Mirrors the Rust reference's
    /// `Term::Quote { term: Box<Term> }` (core/src/term.rs). Named
    /// `quote_`, not `quote` -- `quote` is a reserved keyword in the
    /// self-hosted grammar's own identifier parser too (same reason
    /// `type_`/`if_`/`match_` above are suffixed, not bare). Parsing/
    /// representation only in this codebase so far -- no expansion pass
    /// exists yet to resolve `unquote`/`,(expr)` inside the quoted body
    /// (see plans/bootstrapping/self-hosted-compiler.md); `unquote`
    /// itself needs no special grammar at all, since it's just an
    /// ordinary identifier at parse time (recognized as magic only at
    /// expansion time, mirroring the reference exactly).
    quote_ (term: Term),
    /// Term-position `name!` (`foo!`, `foo! 1 2`). Structurally
    /// identical to `Term.var` (`idx`/`dbg`) -- `idx` is always
    /// `sentinel` in practice, since macro names are resolved in a
    /// separate namespace at expansion time, never via de Bruijn lookup
    /// against a local `ctx` the way an ordinary bound variable is.
    /// A separate sibling variant, not a tagged `Term.var`, because
    /// self-hosted has no `NameRef` at the canonical term level to add
    /// a `Macro` case to the way the Rust reference's
    /// `Term::Var{name: NameRef::Macro(_)}` does (a qualified/dotted
    /// name here is just one joined `Identifier` string, not a
    /// structured `NameRef`) -- see
    /// plans/bootstrapping/self-hosted-compiler.md for the alternatives
    /// considered and rejected (baking `!` into the identifier string;
    /// a 3rd `DebugName` variant, ruled out as live-regression-risky
    /// since `DebugName` is matched exhaustively in several real
    /// hot-path files).
    var_macro (idx: I64) (dbg: DebugName),
}

/// Canonical TypeError uses de Bruijn Term. TypeErrorV0 is the legacy V0 variant.
type TypeError {
    mismatch (expected: Term) (actual: Term),
    unknown_var (name: NameRef),
    unknown_type (name: NameRef),
    unknown_constructor (name: NameRef),
    not_a_function (term: Term),
    not_a_type (term: Term),
    infinite_type (term: Term),
    custom (msg: String),
}

/// Canonical EvalError uses de Bruijn Term. EvalErrorV0 is the legacy V0 variant.
type EvalError {
    undefined_var (name: NameRef),
    not_a_function (term: Term),
    match_failure (term: Term),
    custom (msg: String),
}

type TypeConstraint {
    mk (cls: ModulePath) (vars: List Identifier)
}

/// Canonical Def uses de Bruijn Term. DefV0 is the legacy V0 variant.
struct Def {
    name: ModulePath,
    typ: Term,
    term: Term,
    constraints: List TypeConstraint,
    attrs: List Attribute,
    vis: Visibility
}

def Def.name (d : Def) : ModulePath := d.name

// Canonical InductConstructor uses de Bruijn Term. InductConstructorV0 is the legacy V0 variant.
type InductConstructor {
    mk (name: ModulePath) (params: List Param) (typ: Term)
}

// Canonical Inductive uses de Bruijn Term. InductiveV0 is the legacy V0 variant.
type Inductive {
    mk (name: ModulePath) (params: List Param) (typ: Term) (constructors: List InductConstructor) (attrs: List Attribute) (vis: Visibility)
}

// Canonical ClassDef uses de Bruijn Term. ClassDefV0 is the legacy V0 variant.
type ClassDef {
    mk (name: Identifier) (typ: Term) (default: Option Term)
}

// Canonical Class uses de Bruijn Term. ClassV0 is the legacy V0 variant.
type Class {
    mk (name: Identifier) (params: List Param) (constraints: List TypeConstraint) (methods: List ClassDef) (vis: Visibility)
}

// Canonical StructField uses de Bruijn Term. StructFieldV0 is the legacy V0 variant.
type StructField {
    /// `mult` mirrors the Rust reference's `StructField.mult`
    /// (core/src/term.rs): `!name : T` (Linear, must be consumed exactly
    /// once), `?name : T` (Affine, at most once), `%name : T` (Zero /
    /// Erased), or no prefix at all (Many, the default — the common
    /// case). See examples/structs.mo's `Buffer.data` for a live `!` use.
    mk (name: Identifier) (typ: Term) (default: Option Term) (mult: Multiplicity)
}


// Canonical Struct uses de Bruijn Term. StructV0 is the legacy V0 variant.
type Struct {
    mk (name: Identifier) (fields: List StructField) (vis: Visibility)
}

/// A single item inside a `use Module { ... }` brace filter. Mirrors the
/// Rust host's `UseItem` (core/src/term.rs).
type UseItem {
    use_name (name: Identifier),
    use_rename (name: Identifier) (alias: Identifier),
    use_glob,
    use_sub (name: Identifier) (items: List UseItem),
    use_sub_rename (name: Identifier) (alias: Identifier) (items: List UseItem),
}

/// What names a `use` declaration imports. Bare `use Module` (no braces)
/// is deprecated but still parses. Mirrors Rust's `UseFilter`.
type UseFilter {
    use_bare,
    use_items (items: List UseItem),
}

/// What names an `open` declaration makes unqualified. Mirrors Rust's
/// `OpenFilter`.
type OpenFilter {
    open_all,
    open_only (names: List Identifier),
}

// Canonical Decl uses de Bruijn Term. DeclV0 is the legacy variant.
type Decl {
    def_d (Def),
    inductive_d (Inductive),
    struct_d (Struct),
    class_d (Class),
    instance_d (Instance),
    infix_d (op: Operator) (path: ModulePath) (vis: Visibility),
    use_d (path: ModulePath) (filter: UseFilter) (public: Bool),
    open_d (path: ModulePath) (filter: OpenFilter),
    /// `open ModulePath [{filter}] in <decl>` — the module is opened only
    /// for the scope of the wrapped declaration (def/type/struct/class/
    /// instance). Mirrors Rust's `Decl::ScopedOpen`.
    scoped_open_d (path: ModulePath) (filter: OpenFilter) (decl: Decl),
    /// `defmacro name params := <term>` — mirrors the Rust reference's
    /// `Decl::DefMacro(Def)` (core/src/term.rs): literally reuses `Def`
    /// (`typ` forced to `Term.hole`, `term` wrapped in one lambda per
    /// param when `params` is non-empty via the existing `lam_params`
    /// helper, lang/parser.mo — no new lambda-building logic needed).
    /// Parsing/representation only — nothing expands or invokes this
    /// yet (see plans/bootstrapping/self-hosted-compiler.md).
    def_macro_d (Def),
    /// `defmacro name params := decls { ... }` — the sibling
    /// declaration-generating form. Mirrors the Rust reference's
    /// `Decl::DeclGen(DeclGenDef)`, but with `DeclGenDef`'s fields
    /// inlined directly here (matching this type's own `infix_d`/
    /// `scoped_open_d` convention of inline fields over a separate
    /// wrapper struct) rather than introduced as its own named type.
    /// `decl_list` is the literal, unexpanded list of declarations parsed
    /// out of the `decls { ... }` body.
    decl_gen_d (name: ModulePath) (params: List Param) (decl_list: List Decl) (attrs: List Attribute),
    /// Declaration-position `name! arg1 arg2 ...` (e.g. `derive_beq!
    /// Point`, `reflect_type_info! T some_meta`). `name` is a bare
    /// `Identifier`, NOT a `ModulePath` — differs from `defmacro`'s own
    /// name shape, mirroring the Rust reference's `Decl::MacroCall`
    /// exactly (core/src/term.rs). `args` are whitespace-separated
    /// terms, not a comma/paren-delimited call.
    macro_call_d (name: Identifier) (args: List Term),
}

def Decl.to_name (d : Decl) : ModulePath :=
    match d {
        def_d def_ => Def.name def_,
        _ => ModulePath.mp []
    }

// Canonical Instance uses de Bruijn Term. InstanceV0 is the legacy V0 variant.
type Instance {
    /// `implicit_params` holds any `{Name : Type}` binders written right
    /// after `instance` (before the optional `[constraints]` and the class
    /// name), e.g. `instance {A : Type} Show A { ... }`. Mirrors the Rust
    /// reference's `Instance.params` (core/src/term.rs) — load-bearing for
    /// instance resolution there (substitution-based matching against a
    /// lookup key's args), not just documentation. Empty for the common
    /// case of a fully-concrete instance like `instance Show Bool { ... }`.
    ///
    /// `defs` holds the instance's own concrete method `Def`s (`def m :=
    /// ...` entries inside the `instance ... { }` body) — mirrors the
    /// Rust reference's `Instance.impls_map: Map<Identifier, Def>`
    /// (core/src/term.rs), and mirrors this very module's own `Class`
    /// type, which already retains its method defs the same way
    /// (`Class.mk`'s `methods` field). Until this field existed,
    /// `instance_parser`/`instance_close` (lang/parser.mo) fully parsed
    /// an instance's own methods and then discarded them outright —
    /// `resolve_class_method`/`derive_instance_key`
    /// (lang/typecheck/infer.mo) could find a matching `Instance` but
    /// never its concrete implementation, always falling back to the
    /// class method's own abstract signature. See
    /// plans/bootstrapping/self-hosted-compiler.md's dictionary-passing
    /// plan (Phase 1) for the full context.
    mk (name: Identifier) (cls: ModulePath) (constraints: List TypeConstraint) (args: List Term) (vis: Visibility) (implicit_params: List Param) (defs: List Def)
}

// --- Do-notation desugaring ---

// --- Do-notation desugaring ---
// Canonical DoStmt uses de Bruijn Term. DoStmtV0 is the legacy V0 variant.


// `bind_s`/`let_s` carry the statement's own declared type (`Term.hole`
// when unannotated, e.g. `let x <- expr;`/`let x := expr;`) -- without
// it, `desugar_do_inner` had no way to give the desugared binder a real
// type even when the source explicitly wrote one (`let x : T <- expr;`),
// which broke downstream typecheck precision for that binding (e.g.
// match-case validation on a do-block-bound value whose real type WAS
// written down, just never threaded through -- see
// plans/bootstrapping/self-hosted-compiler.md's changelog for the
// lang/main.mo `main` repro this was found from).
type DoStmt {
    bind_s (name: Identifier) (typ: Term) (expr: Term),
    let_s (name: Identifier) (typ: Term) (expr: Term),
    ret_s (expr: Term),
    expr_s (expr: Term),
}

// Named (not `DebugName.unnamed`) so this flows through the SAME
// class-method-call resolution `lang/scope.mo`'s `resolve_class_call_term`
// already gives every other class method (`Show.show`, `I64.add`, ...) --
// that function's own `DebugName.unnamed` arm deliberately leaves an
// unnamed call head untouched (it has no name to resolve a class/instance
// from), so an unnamed bind/pure sentinel reached codegen unresolved,
// producing a bogus `void`-typed call argument (`compile_db_term_ir`'s
// `Term.var`/`DebugName.unnamed` case has nothing better to emit).
// Mirrors the Rust reference's own `desugar_do_statements`
// (core/parser.rs), which desugars to `pvar(vec!["Monad", "bind"])`/
// `pvar(vec!["Monad", "pure"])` -- a real, dotted, class-qualified
// identifier -- rather than a free/unnamed variable.
def monad_bind_term : Term :=
    Term.var (-1) (DebugName.named (Identifier.id "Monad.bind"))

def monad_pure_term : Term :=
    Term.var (-1) (DebugName.named (Identifier.id "Monad.pure"))

// Fold in SOURCE order (first statement outermost), mirroring the
// Rust reference's `desugar_do_statements` (`core/parser.rs`): each
// statement wraps the desugaring of the statements that FOLLOW it, so
// the first `let x <- e1` becomes the outermost `bind`, the last
// statement sits innermost (its continuation is the trailing
// `pure hole`). `desugar_do_inner`'s head is the outermost wrap, so the
// list MUST be passed in source order -- reversing it (an earlier bug)
// put the LAST statement outermost, which both inverted monadic
// evaluation order AND, because de Bruijn indices are assigned at parse
// time relative to the do-block's binder context (innermost/last-bound
// = lowest index), placed a later statement's reference to an earlier
// `bind_s` variable OUTSIDE that variable's binder -- a spurious
// out-of-range `bound_var` (the `test_do_bind_with_match` self-hosted-
// check gap). `ret_s` discards `ss`/`rest`, matching the reference's
// `Return` (which replaces the accumulated continuation).
def desugar_do (stmts : List DoStmt) : Term :=
    desugar_do_inner stmts (Term.app monad_pure_term Term.hole)

def desugar_do_inner (stmts : List DoStmt) (rest : Term) : Term :=
    match stmts {
        List.cons s ss =>
            match s {
                bind_s name typ expr =>
                    Term.app (Term.app monad_bind_term expr)
                        (Term.lam (DebugName.named name) typ (desugar_do_inner ss rest)),
                let_s name typ expr =>
                    Term.app (Term.lam (DebugName.named name) typ (desugar_do_inner ss rest)) expr,
                ret_s expr => Term.app monad_pure_term expr,
                // A bare-expression statement with nothing following it
                // (`ss` empty) IS the do-block's own final value -- used
                // DIRECTLY, exactly like `ret_s` already does, not bound
                // via `Monad.bind` to a discarding continuation (which
                // silently replaces its real value with the block's own
                // default `rest`, `Monad.pure ()`). Mirrors the Rust
                // reference's own `desugar_do_statements` (core/src/
                // parser.rs): `DoStatement::Expr { value } => value` when
                // it's the LAST statement (processed first, iterating in
                // reverse) -- no bind at all. This self-hosted port never
                // special-cased that. Confirmed as a real, previously-
                // masked bug via the full `lang/main.mo` self-compile: a
                // do-block whose only/last statement is a bare `match`/
                // `if` containing its own internal `return`s (`do { let
                // xs := ...; match xs { ... => return x, ... } }`) had
                // its real value silently discarded and replaced with
                // Unit -- masked until now by a DIFFERENT, now-fixed
                // codegen bug (a branching case body's own deepest block
                // used to `ret` directly instead of continuing to this
                // bind at all, `retarget_terminal_ret`), which
                // accidentally bypassed this one.
                expr_s expr =>
                    match ss {
                        List.empty => expr,
                        List.cons _ _ =>
                            Term.app (Term.app monad_bind_term expr)
                                (Term.lam (DebugName.unnamed) Term.hole (desugar_do_inner ss rest)),
                    }
            },
        List.empty => rest
    }

def list_rev_loop {A : Type} (xs : List A) (acc : List A) : List A :=
    match xs {
        List.cons x rest => list_rev_loop rest (List.cons x acc),
        List.empty => acc
    }

def list_reverse {A : Type} (xs : List A) : List A :=
    list_rev_loop xs List.empty

// --- Similar class for structural comparison ---

class Similar A {
    def similar (a : A) (b : A) : Bool
}

instance Similar Identifier {
    def similar (a : Identifier) (b : Identifier) : Bool :=
        match a {
            id s1 => match b {
                id s2 => String.beq s1 s2
            }
        }
}

instance Similar Operator {
    def similar (a : Operator) (b : Operator) : Bool :=
        match a {
            operator s1 => match b {
                operator s2 => String.beq s1 s2
            }
        }
}

// List helpers (avoid generic constrained instance due to solver limitation)
def id_list_similar (a : List Identifier) (b : List Identifier) : Bool :=
    match a {
        List.cons x xs => match b {
            List.cons y ys => Similar.similar x y && id_list_similar xs ys,
            List.empty => false,
            _ => false
        },
        List.empty => match b {
            List.empty => true,
            List.cons _ _ => false,
            _ => false
        },
        _ => false
    }

def mc_list_similar (a : List MatchCase) (b : List MatchCase) : Bool :=
    match a {
        List.cons x xs => match b {
            List.cons y ys => Similar.similar x y && mc_list_similar xs ys,
            List.empty => false
        },
        List.empty => match b {
            List.empty => true,
            List.cons _ _ => false
        }
    }

def param_list_similar (a : List Param) (b : List Param) : Bool :=
    match a {
        List.cons x xs => match b {
            List.cons y ys => Similar.similar x y && param_list_similar xs ys,
            List.empty => false
        },
        List.empty => match b {
            List.cons y ys => false,
            List.empty => true
        }
    }

def opt_db_term_similar (a : Option Term) (b : Option Term) : Bool :=
    match a {
        Option.some x => match b {
            Option.some y => Similar.similar x y,
            Option.none => false
        },
        Option.none => match b {
            Option.none => true,
            Option.some _ => false
        }
    }

def opt_db_term_list_similar (a : List (Option Term)) (b : List (Option Term)) : Bool :=
    match a {
        List.cons x xs => match b {
            List.cons y ys => opt_db_term_similar x y && opt_db_term_list_similar xs ys,
            List.empty => false
        },
        List.empty => match b {
            List.empty => true,
            List.cons _ _ => false
        }
    }

instance Similar ModulePath {
    def similar (a : ModulePath) (b : ModulePath) : Bool :=
        match a {
            ModulePath.mp ids1 => match b {
                ModulePath.mp ids2 => id_list_similar ids1 ids2,
                _ => false
            },
            _ => false
        }
}

instance Similar NameRef {
    def similar (a : NameRef) (b : NameRef) : Bool :=
        match a {
            NameRef.nid id1 => match b {
                NameRef.nid id2 => Similar.similar id1 id2,
                NameRef.nmp _ => false,
                NameRef.nop _ => false
            },
            NameRef.nmp mp1 => match b {
                NameRef.nmp mp2 => Similar.similar mp1 mp2,
                NameRef.nid _ => false,
                NameRef.nop _ => false
            },
            NameRef.nop op1 => match b {
                NameRef.nop op2 => Similar.similar op1 op2,
                NameRef.nid _ => false,
                NameRef.nmp _ => false
            }
        }
}

instance Similar NumSuffix {
    def similar (a : NumSuffix) (b : NumSuffix) : Bool :=
        match a {
            i8 => match b {
                i8 => true, i16 => false, i32 => false, i64 => false,
                u8 => false, u16 => false, u32 => false, u64 => false,
                f32 => false, f64 => false
            },
            i16 => match b {
                i8 => false, i16 => true, i32 => false, i64 => false,
                u8 => false, u16 => false, u32 => false, u64 => false,
                f32 => false, f64 => false
            },
            i32 => match b {
                i8 => false, i16 => false, i32 => true, i64 => false,
                u8 => false, u16 => false, u32 => false, u64 => false,
                f32 => false, f64 => false
            },
            i64 => match b {
                i8 => false, i16 => false, i32 => false, i64 => true,
                u8 => false, u16 => false, u32 => false, u64 => false,
                f32 => false, f64 => false
            },
            u8 => match b {
                i8 => false, i16 => false, i32 => false, i64 => false,
                u8 => true, u16 => false, u32 => false, u64 => false,
                f32 => false, f64 => false
            },
            u16 => match b {
                i8 => false, i16 => false, i32 => false, i64 => false,
                u8 => false, u16 => true, u32 => false, u64 => false,
                f32 => false, f64 => false
            },
            u32 => match b {
                i8 => false, i16 => false, i32 => false, i64 => false,
                u8 => false, u16 => false, u32 => true, u64 => false,
                f32 => false, f64 => false
            },
            u64 => match b {
                i8 => false, i16 => false, i32 => false, i64 => false,
                u8 => false, u16 => false, u32 => false, u64 => true,
                f32 => false, f64 => false
            },
            f32 => match b {
                i8 => false, i16 => false, i32 => false, i64 => false,
                u8 => false, u16 => false, u32 => false, u64 => false,
                f32 => true, f64 => false
            },
            f64 => match b {
                i8 => false, i16 => false, i32 => false, i64 => false,
                u8 => false, u16 => false, u32 => false, u64 => false,
                f32 => false, f64 => true
            }
        }
}

instance Similar Con {
    def similar (a : Con) (b : Con) : Bool :=
        match a {
            mk name1 typ1 nargs1 args1 => match b {
                mk name2 typ2 nargs2 args2 =>
                    Similar.similar name1 name2 && Similar.similar typ1 typ2 && I64.beq nargs1 nargs2 && opt_db_term_list_similar args1 args2
            }
        }
}

instance Similar Native {
    def similar (a : Native) (b : Native) : Bool :=
        match a {
            mk name1 nargs1 args1 => match b {
                mk name2 nargs2 args2 =>
                    Similar.similar name1 name2 && I64.beq nargs1 nargs2 && opt_db_term_list_similar args1 args2
            }
        }
}

instance Similar MatchCase {
    def similar (a : MatchCase) (b : MatchCase) : Bool :=
        match a {
            mc name1 args1 body1 => match b {
                mc name2 args2 body2 =>
                    Similar.similar name1 name2 && id_list_similar args1 args2 && Similar.similar body1 body2
            }
        }
}

instance Similar Multiplicity {
    def similar (a : Multiplicity) (b : Multiplicity) : Bool :=
        match a {
            zero => match b { zero => true, many => false, linear => false, affine => false },
            many => match b { zero => false, many => true, linear => false, affine => false },
            linear => match b { zero => false, many => false, linear => true, affine => false },
            affine => match b { zero => false, many => false, linear => false, affine => true }
        }
}

instance Similar Param {
    def similar (a : Param) (b : Param) : Bool :=
        match a {
            mk name1 typ1 mult1 def1 _attrs1 => match b {
                mk name2 typ2 mult2 def2 _attrs2 =>
                    Similar.similar name1 name2 && Similar.similar typ1 typ2
                    && Similar.similar mult1 mult2 && opt_db_term_similar def1 def2
            }
        }
}

instance Similar Location {
    def similar (a : Location) (b : Location) : Bool :=
        match a {
            mk off1 line1 col1 => match b {
                mk off2 line2 col2 =>
                    I64.beq off1 off2 && I64.beq line1 line2 && I64.beq col1 col2
            }
        }
}

def opt_str_similar (a : Option String) (b : Option String) : Bool :=
    match a {
        Option.some x => match b {
            Option.some y => String.beq x y,
            Option.none => false
        },
        Option.none => match b {
            Option.none => true,
            Option.some _ => false
        }
    }

instance Similar SourceRange {
    def similar (a : SourceRange) (b : SourceRange) : Bool :=
        match a {
            mk start1 end1 path1 => match b {
                mk start2 end2 path2 =>
                    Similar.similar start1 start2 && Similar.similar end1 end2 && opt_str_similar path1 path2
            }
        }
}

instance Similar Literal {
    def similar (a : Literal) (b : Literal) : Bool :=
        match a {
            str s1 => match b {
                str s2 => String.beq s1 s2,
                num _ _ => false, if_ _ _ _ => false, match_ _ _ => false
            },
            num v1 s1 => match b {
                num v2 s2 => I64.beq v1 v2 && Similar.similar s1 s2,
                str _ => false, if_ _ _ _ => false, match_ _ _ => false
            },
            if_ o1 t1 th1 => match b {
                if_ o2 t2 th2 => Similar.similar o1 o2 && Similar.similar t1 t2 && Similar.similar th1 th2,
                str _ => false, num _ _ => false, match_ _ _ => false
            },
            match_ v1 cs1 => match b {
                match_ v2 cs2 => Similar.similar v1 v2 && mc_list_similar cs1 cs2,
                str _ => false, num _ _ => false, if_ _ _ _ => false
            }
        }
}


// --- Similar instances for de Bruijn types (Phase 0) ---

instance Similar DebugName {
    def similar (a : DebugName) (b : DebugName) : Bool :=
        match a {
            named id1 => match b {
                named id2 => Similar.similar id1 id2,
                unnamed => false
            },
            unnamed => match b {
                unnamed => true,
                named _ => false
            }
        }
}

instance Similar Term {
    def similar (a : Term) (b : Term) : Bool :=
        match a {
            var i1 d1 => match b {
                var i2 d2 => I64.beq i1 i2 && Similar.similar d1 d2,
                lam _ _ _ => false, forall _ _ _ => false, pi _ _ => false,
                app _ _ => false, lit _ => false, ntv _ => false,
                con _ => false, type_ _ => false, hole => false
            },
            lam d1 t1 bd1 => match b {
                lam d2 t2 bd2 => Similar.similar d1 d2 && Similar.similar t1 t2 && Similar.similar bd1 bd2,
                var _ _ => false, forall _ _ _ => false, pi _ _ => false,
                app _ _ => false, lit _ => false, ntv _ => false,
                con _ => false, type_ _ => false, hole => false
            },
            forall d1 k1 bd1 => match b {
                forall d2 k2 bd2 => Similar.similar d1 d2 && Similar.similar k1 k2 && Similar.similar bd1 bd2,
                var _ _ => false, lam _ _ _ => false, pi _ _ => false,
                app _ _ => false, lit _ => false, ntv _ => false,
                con _ => false, type_ _ => false, hole => false
            },
            pi a1 r1 => match b {
                pi a2 r2 => Similar.similar a1 a2 && Similar.similar r1 r2,
                var _ _ => false, lam _ _ _ => false, forall _ _ _ => false,
                app _ _ => false, lit _ => false, ntv _ => false,
                con _ => false, type_ _ => false, hole => false
            },
            app f1 a1 => match b {
                app f2 a2 => Similar.similar f1 f2 && Similar.similar a1 a2,
                var _ _ => false, lam _ _ _ => false, forall _ _ _ => false,
                pi _ _ => false, lit _ => false, ntv _ => false,
                con _ => false, type_ _ => false, hole => false
            },
            lit v1 => match b {
                lit v2 => Similar.similar v1 v2,
                var _ _ => false, lam _ _ _ => false, forall _ _ _ => false,
                pi _ _ => false, app _ _ => false, ntv _ => false,
                con _ => false, type_ _ => false, hole => false
            },
            ntv n1 => match b {
                ntv n2 => Similar.similar n1 n2,
                var _ _ => false, lam _ _ _ => false, forall _ _ _ => false,
                pi _ _ => false, app _ _ => false, lit _ => false,
                con _ => false, type_ _ => false, hole => false
            },
            con c1 => match b {
                con c2 => Similar.similar c1 c2,
                var _ _ => false, lam _ _ _ => false, forall _ _ _ => false,
                pi _ _ => false, app _ _ => false, lit _ => false,
                ntv _ => false, type_ _ => false, hole => false
            },
            type_ u1 => match b {
                type_ u2 => I64.beq u1 u2,
                var _ _ => false, lam _ _ _ => false, forall _ _ _ => false,
                pi _ _ => false, app _ _ => false, lit _ => false,
                ntv _ => false, con _ => false, hole => false
            },
            hole => match b {
                hole => true,
                var _ _ => false, lam _ _ _ => false, forall _ _ _ => false,
                pi _ _ => false, app _ _ => false, lit _ => false,
                ntv _ => false, con _ => false, type_ _ => false
            }
        }
}

// ─── Term construction tests (Phase 0) ─────────────────────────────

#[test]
def test_term_var : Bool :=
    let v : Term := Term.var 0 (DebugName.named (Identifier.id "x")) in
    true

#[test]
def test_term_lam : Bool :=
    let body : Term := Term.var 0 (DebugName.unnamed) in
    let l : Term := Term.lam DebugName.unnamed body body in
    true

#[test]
def test_term_forall : Bool :=
    let body : Term := Term.var 0 (DebugName.unnamed) in
    let f : Term := Term.forall DebugName.unnamed body body in
    true

#[test]
def test_term_pi : Bool :=
    let arg : Term := Term.type_ 1 in
    let ret : Term := Term.type_ 1 in
    let p : Term := Term.pi arg ret in
    true

#[test]
def test_term_dep_pi : Bool :=
    // Dependent pi: pi Nat (var 0 "n") — ret references arg at index 0
    let arg : Term := Term.type_ 0 in
    let ret : Term := Term.var 0 (DebugName.named (Identifier.id "n")) in
    let p : Term := Term.pi arg ret in
    true

#[test]
def test_term_app : Bool :=
    let f : Term := Term.var 0 (DebugName.unnamed) in
    let a : Term := Term.var 1 (DebugName.unnamed) in
    let app : Term := Term.app f a in
    true

#[test]
def test_term_lit : Bool :=
    let l : Term := Term.lit (Literal.str "hello") in
    true

#[test]
def test_term_ntv : Bool :=
    // Work around Native.mk forall-inference bug with List.empty
    // by using a non-empty list of args
    let none_opt : Option Term := Option.none in
    let args : List (Option Term) := List.cons none_opt List.empty in
    let ntv_val : Native := Native.mk (Identifier.id "foo") 0 args in
    let n : Term := Term.ntv ntv_val in
    true

#[test]
def test_term_con : Bool :=
    // Work around Con.mk/ModulePath.mp forall-inference bugs with List.empty
    // by using non-empty lists
    let none_opt : Option Term := Option.none in
    let args : List (Option Term) := List.cons none_opt List.empty in
    let mod_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Test") List.empty) in
    let con_val : Con := Con.mk (Identifier.id "Bar") mod_path 0 args in
    let c : Term := Term.con con_val in
    true

#[test]
def test_term_type : Bool :=
    let t : Term := Term.type_ 0 in
    true

#[test]
def test_term_hole : Bool :=
    let h : Term := Term.hole in
    true

// --- Phase 2: Scope types ---

// Infix operator binding. Maps an operator symbol to a definition path.
struct Infix {
    operator : Operator,
    name : ModulePath,
}

// Instance lookup key.
struct InstanceKey {
    cls : ModulePath,
    constraints : List TypeConstraint,
    args : List Param,
}

// A resolved definition entry in scope.
struct ScopeDef {
    name : ModulePath,
    module : ModulePath,
    sig : Term,
    body : Term,
}

// A class method entry in scope.
struct ScopeClassDef {
    class_name : ModulePath,
    full_name : ModulePath,
    name : Identifier,
    sig : Term,
}

// Instance entries grouped by class name.
struct ScopeInstance {
    class_name : ModulePath,
    instances : List Instance,
}

// Conflicting name resolution entry.
struct ScopeConflict {
    name : ModulePath,
    candidates : List ModulePath,
}

// Local variable in the scope chain.
struct LocalVar {
    name : Identifier,
    typ : Term,
    multiplicity : Multiplicity,
}

// All resolved entries for a single scope level.
//
// `def_params`: a def's own declared parameter (name, type) list, in
// order -- see `plans/implementations/named-field-construction.md`'s
// Phase 6. Deliberately a SEPARATE side-table from `def_refs`, not a
// change to `ScopeDef.sig`/`.body`: that field's `Term.hole` sentinel
// (set unconditionally by `build_scope_def`) is load-bearing for dozens
// of existing call sites across the checker, which changing would risk
// wide-reaching regressions -- named-call resolution only ever needs a
// def's param NAMES (to match a call's own field names) and TYPES (to
// check each field's value against), never its full body/signature, so
// this narrower table is both safer and sufficient. Has a `:=` default
// (`Map.empty`) so every EXISTING `{ def_refs := .., .. }` struct-literal
// construction site continues to build correctly unchanged (the checker
// fills a missing field from its own declared default, same as any other
// struct literal) -- only POSITIONAL `mk`/pattern-match destructuring
// sites need updating for the new arity.
struct ScopeData {
    def_refs : HashMap ModulePath ScopeDef,
    class_defs : List ScopeClassDef,
    instances : List ScopeInstance,
    // `HashMap`, not `List` -- mirrors `def_refs` (see bench/scope_lookup.mo):
    // every consumer looks this up by name (`scope_find_inductive`), never
    // iterates it, so a linear scan over every inductive in the merged
    // scope (~218+ corpus-wide) on every match-case/struct-literal check
    // was pure waste. `classes`, the sibling field just below, stays a
    // `List` (by-name lookup is now `scope_find_class`, lower corpus
    // cardinality than inductives, no measured need for a HashMap yet).
    inductives : HashMap ModulePath Inductive,
    // Full `Class` values (params/constraints/ordered methods), not a
    // synthetic zero-method `Inductive` stand-in -- `build_scope_class`
    // used to throw the real `Class` away and register a `dummy_ind`
    // instead, which is why `resolve_class_method`'s own class lookup
    // (`lang/typecheck/infer.mo`) could never actually resolve a class's
    // own declared params/methods. `scope_find_class`/`scope_data_classes`
    // (below) are the real by-name reader this field never had before.
    classes : List Class,
    infixes : List Infix,
    conflicts : List ScopeConflict,
    // `HashMap.map HashMap.empty_buckets` directly, not `Map.empty`: the
    // latter is a CLASS method (`instance [Hashable K, BOrd K] Map
    // HashMap`, `std/map.mo`) needing type-directed dispatch that a
    // struct field's default-value expression doesn't get the same way
    // an ordinary call site does (confirmed: `Map.empty` here fails at
    // evaluation with "unresolved global: Map.empty") -- `HashMap.map`/
    // `.empty_buckets` are ordinary functions, no dispatch needed.
    def_params : HashMap ModulePath (List (Pair Identifier Term)) := HashMap.map HashMap.empty_buckets,
    // A def's own DECLARED return type (the final non-`Pi`/`Forall` type
    // at the end of its signature's own Pi-chain, `Def.typ` -- NOT its
    // body's inferred type, and NOT `ScopeDef.sig`, which stays
    // unconditionally `Term.hole` by its own load-bearing design, see
    // `build_scope_def`'s doc comment). Lets `find_inductive_for_cases`
    // (`lang/typecheck/infer.mo`) resolve a match's scrutinee type when
    // it's a bare call to a known def (`match fresh_temp c { ... }`) --
    // pure INFER-mode type-checking a call otherwise can't recover a
    // return type at all (`ScopeDef.sig` is hole), so it fell through to
    // an ambiguous constructor-NAME-only scan across every inductive in
    // scope; every `struct`'s auto-generated constructor is named `mk`
    // (`build_scope_struct`), so that scan is ambiguous between ANY two
    // structs the moment either is matched directly on a call result --
    // confirmed to silently return the WRONG field's value, not just
    // fail loudly. Mirrors `def_params`'s own precedent exactly (added
    // for the analogous "recover param types without touching the
    // load-bearing `sig`/`body` hole sentinel" need).
    def_return_types : HashMap ModulePath Term := HashMap.map HashMap.empty_buckets,
    // A def's own FULL declared signature (`Def.typ` itself, e.g.
    // `forall V. Pi (xs : List V) (Option V)` for `def get_first {V :
    // Type} ...`) -- unlike `def_return_types` just above (the Pi-chain
    // STRIPPED final return type) this keeps the implicit-binder and
    // parameter types too, so a call site can check each argument
    // against the parameter's real declared type and solve the
    // signature's type variables from the arguments' actual types.
    // Same side-table pattern (and same never-touch-the-load-bearing-
    // `sig`-hole rule) as `def_params`/`def_return_types`; populated by
    // `build_scope_def`, consumed by `type_check_app`'s signature-driven
    // path (`lang/typecheck/infer.mo`).
    def_sigs : HashMap ModulePath Term := HashMap.map HashMap.empty_buckets,
}

// A scope node in the linked list.
struct Scope {
    module_id : ModulePath,
    scope : ScopeData,
    parent : Option Scope,
}

// Compiled or loaded module entry.
struct Module {
    path : ModulePath,
    inductives : List Inductive,
    defs : List ScopeDef,
    infixs : List Infix,
    instances : List ScopeInstance,
}

// A flat registry of loaded modules, keyed positionally by the list.
//
// Named `ModuleRegistry`, NOT `LoadedModules`, deliberately: `lang/
// module.mo` declares its own, DIFFERENT `LoadedModules`
// (`{main_module : ModuleInfo, all_modules : List ModuleInfo}`) which is
// the one the real pipeline uses (`load_file_modules` ->
// `elaborate_loaded_modules` -> codegen). Since this compiler's global
// name table is not module-scoped, two same-named top-level types across
// files silently collide -- whichever registers last wins for every
// caller project-wide. `lang/main.mo` imported BOTH (one from
// `lang.types`, one from `lang.module`), so the collision was live.
// Renaming this one -- the narrower of the two, reached only by
// `build_scope_from_modules` -- resolves it. See AGENTS.md item 18 for
// the broader ~862-name duplicate-name sweep this is one instance of.
struct ModuleRegistry {
    modules : List Module,
}

// Scope for local bindings (let expressions, case arms, lambda vars).
struct LocalScope {
    vars : List LocalVar,
    parent : Option LocalScope,
}

// Error type for scope resolution failures.
type ScopeError {
    name_not_found (name : NameRef),
    ambiguous_name (name : NameRef) (candidates : List ModulePath),
    inductive_not_found (name : ModulePath),
    instance_not_found (key : InstanceKey),
    class_not_found (name : ModulePath),
    linear_used_twice (name : Identifier),
    affine_used_multiple (name : Identifier),
}

/// Returns true if the Result is ok, false if err.
def result_is_ok {E A : Type} (r : Result E A) : Bool :=
    match r {
        Result.ok _ => true,
        Result.err _ => false,
    }
