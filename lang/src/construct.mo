// Constructors and a surface-form printer for code generators.
//
// `Term`, `Def` and `Param` are `pub`, but the payload types a builder has
// to spell -- `Literal`, `NumSuffix`, `Multiplicity`, `Visibility`,
// `MatchCase`, `AttrArg` (`lang/src/types.mo`) -- are package-private, so a
// generator living in another mote cannot write `Term.lit (Literal.str
// "x")` at all. Everything here takes plain strings and integers and hides
// the private halves. Nothing in this module is used by the compiler
// itself: it exists so `motes/gen` can emit Monad source (see
// `plans/library-ideas/codegen.md`).

use lang::types {
    AttrArg, Attribute, Con, DebugName, Def, FieldPattern, Identifier,
    Literal, MatchCase, Multiplicity, NamePath, NumSuffix, Param, Term,
    Visibility, binder_explicit, mk_param, sentinel, show_identifier,
    show_name_path, term_peel,
}
use lib::pretty {escape_string, show_term}
use std::list {List.length}

// --- Terms ---

/// A string literal.
pub def str (s : String) : Term := Term.lit (Literal.str s)

/// An `I64` literal, printed with its `i64` suffix.
pub def i64 (n : I64) : Term := Term.lit (Literal.num n NumSuffix.i64)

pub def u32 (n : I64) : Term := Term.lit (Literal.num n NumSuffix.u32)

pub def u8 (n : I64) : Term := Term.lit (Literal.num n NumSuffix.u8)

/// `if cond then then_ else else_`, which is the surface spelling the
/// printer writes back.
pub def if_ (cond : Term) (then_ : Term) (else_ : Term) : Term :=
    Term.lit (Literal.if_ cond then_ else_)

/// One positional `match` arm: `ctor args => body`.
pub def case (ctor : String) (args : List String) (body : Term) : MatchCase :=
    let no_field_pattern : Option FieldPattern := Option.none in
    let no_type_name : Option NamePath := Option.none in
    MatchCase.mk (Identifier.id ctor) (id_list args) body no_field_pattern no_type_name

/// `match scrutinee { cases }`.
pub def match_ (scrutinee : Term) (cases : List MatchCase) : Term :=
    Term.lit (Literal.match_ scrutinee cases)

/// A bound variable: `idx` is the de Bruijn index, `name` only what gets
/// printed. Use `Gen` `Env` (motes/gen) rather than computing an index.
pub def var (idx : I64) (name : String) : Term :=
    Term.var idx (DebugName.named (Identifier.id name))

/// A reference to a top-level name (`U32.lt`, `Option.none`): free, hence
/// the `sentinel` index, printed exactly as written. A constructor prints
/// with its type prefix (`show_con`), so a nullary one reads
/// `Option.none` either way.
pub def global (name : String) : Term :=
    Term.var sentinel (DebugName.named (Identifier.id name))

/// `fn (name : type_) => body`.
pub def lam (name : String) (type_ : Term) (body : Term) : Term :=
    Term.lam (binder_explicit (DebugName.named (Identifier.id name))) type_ body

pub def app (fun : Term) (arg : Term) : Term := Term.app fun arg

#[partial]
pub def apps (fun : Term) (args : List Term) : Term :=
    match args {
        List.empty => fun,
        List.cons hd tl => apps (Term.app fun hd) tl,
    }

/// A nullary constructor: `con "Option" "none"` prints as `Option.none`.
pub def con (typ : String) (ctor : String) : Term :=
    let args : List (Option Term) := List.empty in
    Term.con (Con.mk (Identifier.id ctor) (name_path typ) 0 args)

/// The same, applied: `con_app "Option" "some" [x]`.
pub def con_app (typ : String) (ctor : String) (args : List Term) : Term :=
    Term.con (Con.mk (Identifier.id ctor) (name_path typ) (List.length args) (slot_list args))

// --- Declarations ---

/// Declaration visibility. `Visibility` is package-private, so a
/// generator names one of these instead.
pub type Vis {
    vis_public,
    vis_private,
    vis_package,
}

/// An ordinary `(name : type)` parameter.
pub def param (name : String) (type_ : Term) : Param :=
    mk_param (Identifier.id name) type_ Multiplicity.many

/// An attribute with no arguments, e.g. `attr "partial"` for `#[partial]`.
pub def attr (name : String) : Attribute :=
    let no_args : List AttrArg := List.empty in
    Attribute.mk (Identifier.id name) no_args

/// One declaration in the surface form a human writes:
///
///     #[partial]
///     pub def probe (cp : U32) : Bool :=
///         if U32.lt cp 10u32 then true else false
///
/// `params` is the parameter list and `body` the body with those
/// parameters already peeled, which is `Def.params`' shape -- not the
/// Pi/lambda chain `Def.typ`/`Def.term` carry. `def_of_text` renders a
/// parsed `Def` this way.
pub def def_text (attrs : List Attribute) (vis : Vis) (name : String)
    (params : List Param) (ret : Term) (body : Term) : String :=
    let prefix := String.concat (vis_prefix vis) (String.concat "def " name) in
    let head := String.concat (String.concat prefix (param_texts params))
        (String.concat " : " (String.concat (show_term ret) " :=")) in
    let line := String.concat head (String.concat "\n    " (show_term body)) in
    String.concat (attr_texts attrs) (String.concat line "\n")

/// The same, for a `Def` a parser built: its params, and the result type
/// and body recovered by peeling the Pi/lambda chain it folded them into.
pub def def_of_text (d : Def) : String :=
    let count := List.length d.params in
    def_text d.attrs (vis_of d.vis) (show_name_path d.name) d.params
        (peel_pis count d.typ) (peel_lams count d.term)

/// One `#[name args]` per line, each ending in a newline; empty for none.
#[partial]
def attr_texts (attrs : List Attribute) : String :=
    match attrs {
        List.empty => "",
        List.cons a tl => String.concat (attr_text a) (attr_texts tl),
    }

def attr_text (a : Attribute) : String :=
    String.concat "#[" (String.concat (show_identifier a.name)
        (String.concat (attr_arg_texts a.args) "]\n"))

/// Arguments are space-separated and prefixed with one space each, so the
/// arg-less case needs no separator logic.
#[partial]
def attr_arg_texts (args : List AttrArg) : String :=
    match args {
        List.empty => "",
        List.cons hd tl => String.concat (String.concat " " (attr_arg_text hd)) (attr_arg_texts tl),
    }

#[partial]
def attr_arg_text (arg : AttrArg) : String :=
    match arg {
        AttrArg.ident id => show_identifier id,
        AttrArg.str value =>
            String.concat "\"" (String.concat (escape_string value) "\""),
        AttrArg.num value => I64.to_string value,
        // `name := value` -- the spelling `attr_arg_named_one` reads.
        AttrArg.named name value =>
            String.concat (show_identifier name)
                (String.concat " := " (attr_arg_text value)),
        AttrArg.group items => String.concat "[" (String.concat (attr_arg_texts items) "]"),
    }

/// Each parameter prefixed with a space, so `def name` needs no separator
/// logic and an empty list writes nothing.
#[partial]
def param_texts (ps : List Param) : String :=
    match ps {
        List.empty => "",
        List.cons p tl => String.concat (String.concat " " (param_text p)) (param_texts tl),
    }

def param_text (p : Param) : String :=
    let named := String.concat (mult_prefix p.mult) (show_identifier p.name) in
    let core := String.concat named (String.concat " : " (show_term p.type_)) in
    String.concat "(" (String.concat (param_default_text core p.default) ")")

def param_default_text (core : String) (default : Option Term) : String :=
    match default {
        Option.some value => String.concat core (String.concat " := " (show_term value)),
        Option.none => core,
    }

/// Source spelling of a parameter's multiplicity prefix -- the parseable
/// one (`%`/`!`/`?`), not `show_multiplicity`'s diagnostic spelling.
def mult_prefix (mult : Multiplicity) : String := match mult {
    Multiplicity.zero => "%",
    Multiplicity.linear => "!",
    Multiplicity.affine => "?",
    Multiplicity.many => "",
}

def vis_prefix (vis : Vis) : String := match vis {
    Vis.vis_public => "pub ",
    Vis.vis_private => "priv ",
    Vis.vis_package => "",
}

def vis_of (vis : Visibility) : Vis := match vis {
    Visibility.pub_ => Vis.vis_public,
    Visibility.priv_ => Vis.vis_private,
    Visibility.package_private => Vis.vis_package,
}

/// Peel the `params`-many Pi layers a parsed def folded its parameter list
/// into, leaving the declared result type.
#[partial]
def peel_pis (count : I64) (t : Term) : Term :=
    if I64.lt count 1
    then t
    else
        match term_peel t {
            Term.pi _ _ ret => peel_pis (I64.sub count 1) ret,
            _ => t,
        }

/// The matching lambda layers, leaving the body as written.
#[partial]
def peel_lams (count : I64) (t : Term) : Term :=
    if I64.lt count 1
    then t
    else
        match term_peel t {
            Term.lam _ _ body => peel_lams (I64.sub count 1) body,
            _ => t,
        }

// --- Helpers ---

/// A dotted name as one `NamePath` segment: `show_name_path` joins
/// segments with `.`, so the spelling is the same either way.
def name_path (dotted : String) : NamePath := NamePath.mk [Identifier.id dotted]

#[partial]
def id_list (names : List String) : List Identifier :=
    match names {
        List.empty => List.empty,
        List.cons hd tl => List.cons (Identifier.id hd) (id_list tl),
    }

#[partial]
def slot_list (args : List Term) : List (Option Term) :=
    match args {
        List.empty => List.empty,
        List.cons hd tl => List.cons (Option.some hd) (slot_list tl),
    }
