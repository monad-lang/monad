/// The v1 rule set: naming conventions and the single-constructor `type`
/// counter.
///
/// WHY THESE RULES READ `ParseDecl`, NOT `Decl`. Every rule here needs
/// `#[...]` attributes and a declaration's written name, and the LOWERED
/// `Decl` has neither for the kinds that matter:
///
///   * `lower_parse_decl_kind` maps `ParseDeclKind.attrs_d _attrs inner =>
///     lower_parse_decl ctx inner`, so the `#[...]` attributes on a
///     `use`/`open` are DISCARDED at lowering. A rule reading `Decl` could
///     never see `#[allow]`, `#[deprecated]` or anything else on an import.
///   * `Decl.use_d`/`open_d` carry no attribute slot at all.
///
/// So the rules walk the parser's own tree. That is also what makes a
/// FUTURE `#[allow]` implementable: the attribute is still there at this
/// point in the pipeline, which it is not one stage later.
///
/// The cost is that a rule cannot see anything macro expansion generated.
/// For a naming rule that is exactly right -- the user writes the name being
/// checked, and flagging a generated one would be flagging the macro.

use lang::types {
    Attribute, Identifier, ParseClass, ParseDecl, ParseDeclKind, ParseDef,
    ParseInductConstructor, ParseInductive, ParseInstance, ParseParam, ParseStruct,
    ParseTerm, ParseTermKind,
    has_attr, show_identifier, show_name_path,
}

// ─── Character classes ──────────────────────────────────────────────────
//
// ASCII only, and that is a limitation worth stating rather than hiding: a
// name starting with a multi-byte character starts with a byte >= 0x80,
// which is neither class, so it reports as misnamed. The corpus is ASCII
// and `Identifier` is a byte string, so this is exact today; a UTF-8-aware
// version would need a decode step this module has no reason to carry yet.

def is_upper_start (c : I64) : Bool :=
    Bool.not (I64.lt c 65) && Bool.not (I64.gt c 90)

def is_lower_start (c : I64) : Bool :=
    Bool.not (I64.lt c 97) && Bool.not (I64.gt c 122)

def is_lower_or_underscore (c : I64) : Bool :=
    is_lower_start c || I64.beq c 95

/// Whether `s` starts with a byte satisfying `pred`. An empty name is NOT
/// well-named: `Identifier.id ""` is a placeholder, not a convention.
pub def starts_with_class (pred : I64 -> Bool) (s : String) : Bool :=
    match String.to_list s {
        List.empty => false,
        List.cons b _ => pred (U8.to_i64 b),
    }

pub def is_upper_camel (s : String) : Bool := starts_with_class is_upper_start s

pub def is_lower_snake (s : String) : Bool := starts_with_class is_lower_or_underscore s

// ─── Rule names ────────────────────────────────────────────────────────
//
// One def each rather than a string literal at every site: `--deny` names
// these, and a typo in a rule name is silent (an unknown name in `--deny`
// simply never matches).

pub def rule_name_type_name_case : String := "type_name_case"

pub def rule_name_def_name_case : String := "def_name_case"

pub def rule_name_ctor_name_case : String := "ctor_name_case"

pub def rule_name_type_var_case : String := "type_var_case"

pub def rule_name_single_ctor_type : String := "single_ctor_type"

// ─── The findings, as string lists ─────────────────────────────────────
//
// Each rule answers the names it rejects, and the driver turns a name into a
// located diagnostic. Keeping the rules stateful-free this way is what lets
// them be `#[test]`-ed against a source string with no files or IO.

/// A declared `type`/`struct`/`class` name must be UpperCamelCase.
pub def type_name_findings (kind : ParseDeclKind) : List String :=
    match kind {
        ParseDeclKind.inductive_d pi =>
            match pi {
                ParseInductive.mk { name, .. } => classify_type_name (show_name_path name),
            },
        ParseDeclKind.struct_d ps =>
            match ps { ParseStruct.mk { name, .. } => classify_type_name (show_identifier name) },
        ParseDeclKind.class_d pc =>
            match pc { ParseClass.mk { name, .. } => classify_type_name (show_identifier name) },
        _ => List.empty,
    }

def classify_type_name (n : String) : List String :=
    if is_upper_camel n then List.empty else List.cons n List.empty

/// A `def`/method name must be lower_snake. The LAST SEGMENT is what is
/// checked: a dotted def name (`def List.length`) is a lower_snake name
/// bound into `List`, and flagging `List` because it is capitalised would
/// reject the whole dotted-def convention.
///
/// `#[native]`/`#[extern]` defs are skipped: their names come from the C
/// side (`monad_file_exists`, `getenv`), so the convention is not the
/// author's to keep. The tuple return lets the caller report the full
/// written name while the rule judges the tail.
pub def def_name_findings (kind : ParseDeclKind) : List String :=
    match kind {
        ParseDeclKind.def_d pd => match pd {
            ParseDef.mk { name, attrs, .. } =>
                if foreign_named attrs then List.empty
                else classify_def_name (show_name_path name),
        },
        ParseDeclKind.def_macro_d pd => match pd {
            ParseDef.mk { name, .. } => classify_def_name (show_name_path name),
        },
        _ => List.empty,
    }

/// `#[native]` and `#[extern ...]` take their name from the other side of
/// the FFI boundary.
def foreign_named (attrs : List Attribute) : Bool :=
    has_attr (Identifier.id "native") attrs || has_attr_extern attrs

/// `attrs` is affine, so the second question is asked by a def that takes it
/// afresh rather than by a second read of the caller's binder.
def has_attr_extern (attrs : List Attribute) : Bool :=
    has_attr (Identifier.id "extern") attrs

def classify_def_name (written : String) : List String :=
    if is_lower_snake (last_segment written) then List.empty
    else List.cons written List.empty

/// The last `.`-separated segment of a written name. `npath_last` would do
/// this if the name were already a `NamePath`; the parser hands a dotted def
/// name over as ONE flat identifier, so the split has to happen here.
def last_segment (written : String) : String :=
    match last_dot (written) {
        Option.none => written,
        Option.some i => String.drop (I64.add i 1) written,
    }

/// The index of the LAST `.`, or `none`.
#[terminating]
def last_dot_go (s : String) (i : I64) (found : Option I64) : Option I64 :=
    if I64.lt i 0 then found
    else if String.beq (String.slice s i 1) "."
        then last_dot_go s (I64.sub i 1) (Option.some i)
        else last_dot_go s (I64.sub i 1) found

def last_dot (s : String) : Option I64 := last_dot_go s (I64.sub (String.length s) 1) Option.none

/// An inductive's constructors must be lower_snake (`some`, `none`, `ok`).
/// A `#[native]`/`#[extern]` carrier is skipped for the same reason a def
/// is; a primitive-like type whose constructors mirror C names keeps them.
pub def ctor_name_findings (kind : ParseDeclKind) : List String :=
    match kind {
        ParseDeclKind.inductive_d pi =>
            match pi {
                ParseInductive.mk { constructors, attrs, .. } =>
                    if foreign_named attrs then List.empty
                    else ctor_findings constructors List.empty,
            },
        _ => List.empty,
    }

#[partial]
def ctor_findings (cs : List ParseInductConstructor) (acc : List String) : List String :=
    match cs {
        List.empty => acc,
        List.cons c rest =>
            match c {
                ParseInductConstructor.mk n _ps _t =>
                    let tail : String := show_name_path n in
                    if is_lower_snake tail
                    then ctor_findings rest acc
                    else ctor_findings rest (List.append acc (List.cons tail List.empty)),
            },
    }

/// A type variable must be UpperCamelCase (`M I J A`). This is the
/// `AGENTS.md` rule and the most-violated one in the corpus.
///
/// `#[native]`-annotated params are skipped: a native's parameter names are
/// its C signature's.
pub def type_var_findings (kind : ParseDeclKind) : List String :=
    match kind {
        ParseDeclKind.inductive_d pi =>
            match pi { ParseInductive.mk { params, attrs, .. } =>
                if foreign_named attrs then List.empty else param_findings params List.empty },
        ParseDeclKind.class_d pc =>
            match pc { ParseClass.mk { params, .. } => param_findings params List.empty },
        ParseDeclKind.struct_d _ => List.empty,
        ParseDeclKind.def_d pd =>
            match pd { ParseDef.mk { params, attrs, .. } =>
                if foreign_named attrs then List.empty else param_findings params List.empty },
        _ => List.empty,
    }

#[partial]
def param_findings (ps : List ParseParam) (acc : List String) : List String :=
    match ps {
        List.empty => acc,
        List.cons p rest =>
            match p {
                ParseParam.mk { name, type_, attrs, .. } =>
                    param_findings rest (param_one_finding name type_ attrs acc),
            },
    }

/// A param is a TYPE VARIABLE only when its declared type is a sort
/// (`A : Type`, `M : Type -> Type`, `u : Sort 1`). `(x : I64)` and
/// `(f : A -> B)` are VALUE parameters, and judging those by the type-variable
/// convention reports every ordinary lowercase argument binder in the corpus
/// -- which is the false positive that made this rule unusable on its first
/// end-to-end run.
///
/// Not recursive: it answers one parameter, and the walk over the list is
/// `param_findings`'s. The `#[partial]` it used to carry was a copy of the
/// neighbour's, and the metric counts it (`partial_attr_no_self_call`) --
/// which is a real finding, not a false positive.
def param_one_finding
    (n : Identifier) (t : ParseTerm) (attrs : List Attribute) (acc : List String)
    : List String :=
    if foreign_named attrs then acc
    else if Bool.not (is_sort_type t) then acc
    else if is_upper_camel (show_identifier n) then acc
    else List.append acc (List.cons (show_identifier n) List.empty)

/// Whether a parameter's declared type is a sort, i.e. the parameter is a
/// type variable. `Type`/`Prop`/`Sort n` are head sorts; an arrow whose
/// tail is a sort (`Type -> Type`, kinds) counts too, because that is how a
/// higher-kinded variable is written.
def is_sort_type (t : ParseTerm) : Bool :=
    match correspondent_sort t {
        Option.some is_sort => is_sort,
        Option.none => false,
    }

/// The sort-ness of `t`, or `none` when it is not a sort at all. An arrow
/// recurses into its CODOMAIN, so a kind (`Type -> Type`, the shape a
/// higher-kinded variable is written with) counts. There is no `ctx` arm:
/// `ParseTermKind` has no location wrapper -- `Term.ctx` is introduced by
/// lowering, one stage after this tree.
/// `#[terminating]`: the recursion descends into `pi`'s codomain, which is a
/// field of the record inside the `ParseTermKind` variant -- structurally
/// smaller, but not a shape the checker follows through the variant, so it
/// needs to be told.
#[terminating]
def correspondent_sort (t : ParseTerm) : Option Bool :=
    match t.kind {
        ParseTermKind.sort _ => Option.some true,
        ParseTermKind.pi _ _ ret => Option.some (is_sort_type ret),
        _ => Option.none,
    }

/// A `type` with exactly ONE constructor is a `struct` candidate -- the
/// `AGENTS.md` "style rule 1" TODO. Metric only: converting is a separate,
/// risky refactor (the `MatchTraversalMismatch` hazard
/// `code-style-and-lint-enforcement.md` Phase 7 documents), so this reports
/// and never rewrites.
///
/// The name is reported, not converted, and the counter deliberately counts
/// what `scripts/style-metrics.py`'s `single_ctor_type` counts, so the two
/// independent measurements can be compared.
pub def single_ctor_type_findings (kind : ParseDeclKind) : List String :=
    match kind {
        ParseDeclKind.inductive_d pi =>
            match pi {
                ParseInductive.mk { name, constructors, .. } =>
                    if I64.beq (List.length constructors) 1
                    then List.cons (show_name_path name) List.empty
                    else List.empty,
            },
        _ => List.empty,
    }
