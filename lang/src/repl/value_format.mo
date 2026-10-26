/// Human-readable rendering for the browser REPL's result line.
///
/// The interpreter's own `show_value_debug` prints raw tags
/// (`v_con#1/2`), which is honest but unreadable. This module is
/// TYPE-DIRECTED instead: the inferred type of the evaluated expression
/// selects the constructor names, so `some 3`, `[1, 2]`, `ok "x"` and a
/// user `Point { .. }` all print as source-shaped values. It lives in
/// `lang` because `scope_find_inductive` is package-private here.
///
/// Budgets: depth 64, 200 list elements, 8 KiB of output -- the web
/// import scratch buffer is 64 KiB, and a runaway `List I64` would
/// otherwise fill it.

use lang::core_ir {IrLit}
use lang::core_value {Value}
use lang::pretty {show_term}
use lang::scope {scope_data_empty, scope_find_inductive}
use lang::typecheck::infer {empty_locals, last_dotted_segment}
use lang::typecheck::whnf {whnf}
use lang::types {
  DebugName, Identifier, ModulePath, NamePath, NumSuffix, Param, Scope, Term,
  show_name_path
}

pub def max_depth : I64 := 64

pub def max_elements : I64 := 200

/// The `: Type` half. `show_term` renders source-shaped types; the outer
/// parentheses it puts on an application are left alone (v1).
pub def format_type (scope : Scope) (typ : Term) : String :=
    show_term (whnf scope empty_locals typ)

pub def format_value (scope : Scope) (typ : Term) (v : Value) : String :=
    format_at scope (whnf scope empty_locals typ) v 0

#[terminating]
def format_at (scope : Scope) (typ : Term) (v : Value) (depth : I64) : String :=
    if I64.gt depth max_depth
    then "…"
    else format_value_case scope typ v depth

#[terminating]
def format_value_case (scope : Scope) (typ : Term) (v : Value) (depth : I64) : String :=
    match v {
        Value.v_lit l => format_literal typ l,
        Value.v_closure _ _ => "<function>",
        Value.v_partial_ntv _ _ => "<native>",
        Value.v_con tag args => format_constructor scope typ tag args depth,
    }

// ─── Literals ─────────────────────────────────────────────────────────

def format_literal (typ : Term) (l : IrLit) : String :=
    match l {
        IrLit.ir_str s => String.concat "\"" (String.concat (escape_string s) "\""),
        IrLit.ir_num n suffix => format_number typ n suffix,
        IrLit.ir_char _ => "<char>",
        IrLit.ir_float _ _ => "<float>",
        IrLit.ir_sort level => String.concat "Sort " (I64.to_string level),
    }

/// The *type* decides signedness/width, not the literal's suffix: an
/// `I64`-typed value can carry a literal parsed as any suffix.
def format_number (typ : Term) (n : I64) (suffix : NumSuffix) : String :=
    let name : String := type_name typ
    in
    if String.beq name "U8" then I64.to_string (wrap 256 n)
    else if String.beq name "U16" then I64.to_string (wrap 65536 n)
    else if String.beq name "U32" then I64.to_string (wrap 4294967296 n)
    else if String.beq name "U64" then U64.to_string (I64.to_u64 n)
    else if String.beq name "I8" then I64.to_string (sign_extend 256 127 n)
    else if String.beq name "I16" then I64.to_string (sign_extend 65536 32767 n)
    else if String.beq name "I32" then I64.to_string (sign_extend 4294967296 2147483647 n)
    else if String.beq name "" then format_by_suffix n suffix
    else I64.to_string n

def type_name (typ : Term) : String :=
    match type_head typ {
        Option.some s => s,
        Option.none => "",
    }

def format_by_suffix (n : I64) (suffix : NumSuffix) : String :=
    match suffix {
        NumSuffix.u8 => I64.to_string (wrap 256 n),
        NumSuffix.u16 => I64.to_string (wrap 65536 n),
        NumSuffix.u32 => I64.to_string (wrap 4294967296 n),
        NumSuffix.u64 => U64.to_string (I64.to_u64 n),
        _ => I64.to_string n,
    }

def wrap (width : I64) (x : I64) : I64 :=
    let q : I64 := I64.div x width
    in
    let r : I64 := I64.sub x (I64.mul q width)
    in
    if I64.lt r 0 then I64.add r width else r

def sign_extend (width : I64) (half : I64) (x : I64) : I64 :=
    let m : I64 := wrap width x
    in
    if I64.gt m half then I64.sub m width else m

// ─── Constructors ─────────────────────────────────────────────────────

#[terminating]
def format_constructor (scope : Scope) (typ : Term) (tag : I64) (args : List Value) (depth : I64) : String :=
    let name : String := type_name typ
    in
    if String.beq name "List" then format_list scope (type_arg 0 typ) args depth
    else if String.beq name "Option" then format_option scope (type_arg 0 typ) tag args depth
    else if String.beq name "Bool" then (if I64.beq tag 0 then "true" else "false")
    else if String.beq name "Unit" then "unit"
    else if String.beq name "Pair" then format_pair scope typ tag args depth
    else if String.beq name "Result" then format_result scope typ tag args depth
    else if String.beq name "" then format_raw tag args depth
    else format_inductive_value scope typ tag args depth

#[terminating]
def format_list (scope : Scope) (elem : Term) (args : List Value) (depth : I64) : String :=
    format_list_go scope elem args depth List.empty 0

/// `args` is the constructor's own field list at each level: `cons head
/// tail` carries [head, tail]; `empty` carries none.
#[terminating]
def format_list_go (scope : Scope) (elem : Term) (args : List Value) (depth : I64)
    (acc : List String) (count : I64) : String :=
    match args {
        List.empty => String.concat "[" (String.concat (join_with ", " (List.reverse acc)) "]"),
        List.cons head rest =>
            match rest {
                List.empty =>
                    String.concat "["
                        (String.concat
                            (join_with ", " (List.reverse (List.cons (format_at scope elem head (depth + 1)) acc)))
                            "]"),
                List.cons tail _ =>
                    if Bool.not (I64.lt count max_elements)
                    then String.concat "[" (String.concat (join_with ", " (List.reverse acc)) ", …]")
                    else format_list_go scope elem (list_value_tail tail) depth
                            (List.cons (format_at scope elem head (depth + 1)) acc) (count + 1),
            },
    }

/// Peel one `cons` cell. A malformed tail prints as an opaque tag.
def list_value_tail (v : Value) : List Value :=
    match v {
        Value.v_con tag args => if I64.beq tag 0 then List.empty else args,
        _ => List.empty,
    }

#[terminating]
def format_option (scope : Scope) (elem : Term) (tag : I64) (args : List Value) (depth : I64) : String :=
    if I64.beq tag 1
    then "none"
    else match args {
        List.cons head _ => String.concat "some " (format_at scope elem head (depth + 1)),
        List.empty => "some _",
    }

#[terminating]
def format_pair (scope : Scope) (typ : Term) (tag : I64) (args : List Value) (depth : I64) : String :=
    match args {
        List.cons a rest =>
            match rest {
                List.cons b _ =>
                    String.concat "(" (String.concat (format_at scope (type_arg 0 typ) a (depth + 1))
                        (String.concat ", " (String.concat (format_at scope (type_arg 1 typ) b (depth + 1)) ")"))),
                List.empty => format_raw tag args depth,
            },
        List.empty => format_raw tag args depth,
    }

#[terminating]
def format_result (scope : Scope) (typ : Term) (tag : I64) (args : List Value) (depth : I64) : String :=
    match args {
        List.cons head _ =>
            if I64.beq tag 0
            then String.concat "ok " (format_at scope (type_arg 1 typ) head (depth + 1))
            else String.concat "err " (format_at scope (type_arg 0 typ) head (depth + 1)),
        List.empty => if I64.beq tag 0 then "ok _" else "err _",
    }

/// A user inductive/struct: constructor names come from the inductive's
/// DECLARATION order, which is the tag order the lowerer uses (per
/// inductive, 0-based -- not the compiled backend's global tags).
#[terminating]
def format_inductive_value (scope : Scope) (typ : Term) (tag : I64) (args : List Value) (depth : I64) : String :=
    match type_inductive_name typ {
        Option.none => format_raw tag args depth,
        Option.some np =>
            match scope_find_inductive np scope {
                Result.err _ => format_raw tag args depth,
                Result.ok ind =>
                    match List.get tag ind.constructors {
                        Option.none => format_raw tag args depth,
                        Option.some ctor =>
                            let name : String := last_dotted_segment (show_name_path ctor.name)
                            in
                            match args {
                                List.empty => name,
                                List.cons _ _ =>
                                    String.concat name
                                        (String.concat " "
                                            (format_typed_args scope depth ctor.params args)),
                            },
                    },
            },
    }

#[terminating]
def format_raw (tag : I64) (args : List Value) (depth : I64) : String :=
    String.concat "#" (String.concat (I64.to_string tag)
        (String.concat "(" (String.concat (format_args raw_scope depth args) ")")))

/// Like `format_args`, but each field is rendered against the constructor's
/// DECLARED parameter type, so a user type's `Option`/`List` field prints
/// `some 3` rather than `#0(3)`. Falls back to a hole when the two lists
/// have different lengths (a malformed value, which `format_raw` covers).
#[terminating]
def format_typed_args (scope : Scope) (depth : I64) (params : List Param)
    (args : List Value) : String :=
    match args {
        List.empty => "",
        List.cons a rest =>
            let field_typ : Term :=
                match params {
                    List.cons p _ => p.type_,
                    List.empty => Term.hole,
                }
            in
            match rest {
                List.empty => format_at scope field_typ a (depth + 1),
                List.cons _ _ =>
                    String.concat (format_at scope field_typ a (depth + 1))
                        (String.concat ", " (format_typed_args scope depth (drop_first_param params) rest)),
            },
    }

def drop_first_param (params : List Param) : List Param :=
    match params {
        List.empty => List.empty,
        List.cons _ rest => rest,
    }

/// Named rather than a capturing lambda in `List.map`: the compiled
/// backends have a known closure-in-constructor trap with
/// dictionary-capturing closures, so value formatting stays lambda-free.
#[terminating]
def format_args (scope : Scope) (depth : I64) (args : List Value) : String :=
    match args {
        List.empty => "",
        List.cons a rest =>
            match rest {
                List.empty => format_at scope Term.hole a (depth + 1),
                List.cons _ _ => String.concat (format_at scope Term.hole a (depth + 1))
                        (String.concat ", " (format_args scope depth rest)),
            },
    }

/// `format_raw` has no type to work from; an empty scope is enough because
/// its recursive calls print literals/closures only.
def raw_scope : Scope :=
    { module_id := ModulePath.mk List.empty,
      scope := scope_data_empty,
      parent := Option.none,
      incomplete_match_ok := false }

// ─── Type inspection ──────────────────────────────────────────────────

/// The head name of a type: `I64`, `List`, a user inductive. Built-in
/// types are `Term.var` with a named `DebugName`; inductives are
/// `Term.con` (whose `typ_name` is the inductive). Applications peel.
def type_head (t : Term) : Option String :=
    match t {
        Term.var _ dbg =>
            match dbg {
                DebugName.named id =>
                    match id { Identifier.id s => Option.some (last_dotted_segment s) },
                DebugName.unnamed => Option.none,
            },
        Term.con c => Option.some (last_dotted_segment (show_name_path c.typ_name)),
        Term.app f _ => type_head f,
        _ => Option.none,
    }

def type_inductive_name (t : Term) : Option NamePath :=
    match t {
        Term.con c => Option.some c.typ_name,
        // A user inductive named in source can still be a `var` at this
        // stage (the parser's named reference, before elaboration rewrites
        // it), so the one-segment path is a legitimate lookup.
        Term.var _ dbg =>
            match dbg {
                DebugName.named id => Option.some (NamePath.mk (List.cons id List.empty)),
                DebugName.unnamed => Option.none,
            },
        Term.app f _ => type_inductive_name f,
        _ => Option.none,
    }

/// The `i`-th argument of an applied type (`List I64` -> `I64`).
def type_arg (i : I64) (t : Term) : Term :=
    match List.get i (app_args t) {
        Option.some a => a,
        Option.none => Term.hole,
    }

def app_args (t : Term) : List Term :=
    match t {
        Term.app f a => List.append (app_args f) (List.cons a List.empty),
        _ => List.empty,
    }

// ─── Strings ──────────────────────────────────────────────────────────

def escape_string (s : String) : String :=
    String.from_list (List.reverse (escape_bytes (String.to_list s) List.empty))

#[terminating]
def escape_bytes (bs : List U8) (acc : List U8) : List U8 :=
    match bs {
        List.empty => acc,
        List.cons b rest =>
            if U8.beq b 92u8 then escape_bytes rest (List.cons 92u8 (List.cons 92u8 acc))
            else if U8.beq b 34u8 then escape_bytes rest (List.cons 34u8 (List.cons 92u8 acc))
            else if U8.beq b 10u8 then escape_bytes rest (List.cons 110u8 (List.cons 92u8 acc))
            else if U8.beq b 13u8 then escape_bytes rest (List.cons 114u8 (List.cons 92u8 acc))
            else if U8.beq b 9u8 then escape_bytes rest (List.cons 116u8 (List.cons 92u8 acc))
            else escape_bytes rest (List.cons b acc),
    }

def join_with (sep : String) (xs : List String) : String :=
    match xs {
        List.empty => "",
        List.cons x rest =>
            match rest {
                List.empty => x,
                List.cons _ _ => String.concat x (String.concat sep (join_with sep rest)),
            },
    }
