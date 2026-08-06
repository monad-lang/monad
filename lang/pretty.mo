use lang.types {
  Class, ClassDef, Con, DebugName, Decl, Def, Identifier, InductConstructor,
  Inductive, Instance, Literal, MatchCase, ModulePath, Multiplicity, Native,
  NumSuffix, OpenFilter, Operator, Param, Struct, StructField, Term,
  TypeConstraint, UseFilter, UseItem, affine, app, class_d, con, def_d, f32, f64,
  forall, hole, i16, i32, i64, i8, id, if_, inductive_d, infix_d, instance_d, lam,
  linear, lit, many, match_, mc, mk, mp, name, named, ntv, num, open_all, open_d,
  open_only, operator, pi, scoped_open_d, show_identifier, show_module_path,
  show_operator, str, struct_d, type_, u16, u32, u64, u8, unnamed, use_bare,
  use_d, use_glob, use_items, use_name, use_rename, use_sub, use_sub_rename, var,
  zero,
}

open Term {app, con, forall, hole, lam, lit, ntv, pi, type_, var}
open Literal {if_, match_, num, str}
open Decl {
  class_d, def_d, inductive_d, infix_d, instance_d, open_d, scoped_open_d,
  struct_d, use_d,
}
open Multiplicity {affine, linear, many, zero}
open DebugName {named, unnamed}
open NumSuffix {f32, f64, i16, i32, i64, i8, u16, u32, u64, u8}

def show_num_suffix (suf : NumSuffix) : String := match suf {
    i8 => "i8",
    i16 => "i16",
    i32 => "i32",
    i64 => "i64",
    u8 => "u8",
    u16 => "u16",
    u32 => "u32",
    u64 => "u64",
    f32 => "f32",
    f64 => "f64",
}

def show_debug_name (dbg : DebugName) : String := match dbg {
    named id => show_identifier id,
    unnamed => "_",
}

def show_multiplicity (mult : Multiplicity) : String := match mult {
    zero => "0",
    many => "",
    linear => "!",
    affine => "?",
}

def show_universe (level : I64) : String :=
    if level == 0 then "Prop"
    else if level == 1 then "Type"
    else String.concat "Type " (I64.to_string (level - 1))

#[partial]
def show_param (p : Param) : String := match p {
    Param.mk name type_ mult default =>
        let mult_str := show_multiplicity mult in
        let name_str := show_identifier name in
        let type_str := show_term type_ in
        let colon_type := String.concat " : " type_str in
        let base := String.concat mult_str (String.concat name_str colon_type) in
        match default {
            Option.some def_val =>
                let def_str := show_term def_val in
                let eq_def := String.concat " := " def_str in
                String.concat base eq_def,
            Option.none => base,
        },
}

#[partial]
def show_term (t : Term) : String := match t {
    var idx dbg => show_debug_name dbg,
    lam dbg typ body =>
        let name_str := show_debug_name dbg in
        let type_str := show_term typ in
        let body_str := show_term body in
        let fn_name := String.concat "(fn " name_str in
        let fn_type := String.concat " : " type_str in
        let lhs := String.concat fn_name fn_type in
        let rhs := String.concat " => " body_str in
        let inner := String.concat lhs rhs in
        String.concat inner ")",
    forall dbg kind body =>
        let name_str := show_debug_name dbg in
        let kind_str := show_term kind in
        let body_str := show_term body in
        let lhs := String.concat "{" name_str in
        let lt := String.concat " : " kind_str in
        let mid := String.concat lhs lt in
        let rt := String.concat "} -> " body_str in
        String.concat mid rt,
    pi arg ret =>
        let arg_str := show_term arg in
        let ret_str := show_term ret in
        let lhs := String.concat "(" arg_str in
        let arrow := String.concat " -> " ret_str in
        let inner := String.concat lhs arrow in
        String.concat inner ")",
    app fun arg =>
        let fun_str := show_term fun in
        let arg_str := show_term arg in
        let lhs := String.concat "(" fun_str in
        let sp := String.concat " " arg_str in
        let inner := String.concat lhs sp in
        String.concat inner ")",
    lit value => show_literal value,
    ntv native => show_native native,
    con c => show_con c,
    type_ universe => show_universe universe,
    hole => "_",
}

#[partial]
def show_literal (lit : Literal) : String := match lit {
    str value =>
        let lhs := String.concat "\"" value in
        String.concat lhs "\"",
    num value suffix =>
        let num_str := I64.to_string value in
        let suf_str := show_num_suffix suffix in
        String.concat num_str suf_str,
    if_ cond then_ else_ =>
        let cond_str := show_term cond in
        let then_str := show_term then_ in
        let else_str := show_term else_ in
        let lhs := String.concat "if " cond_str in
        let mt := String.concat " then " then_str in
        let mid := String.concat lhs mt in
        let rt := String.concat " else " else_str in
        String.concat mid rt,
    match_ scrutinee cases =>
        let scr_str := show_term scrutinee in
        let cases_str := show_match_cases cases in
        let lhs := String.concat "match " scr_str in
        let br := String.concat " {\n " cases_str in
        let inner := String.concat lhs br in
        String.concat inner "\n}",
}

def show_match_cases (cases : List MatchCase) : String := match cases {
    List.empty => "",
    List.cons first rest => show_match_cases_rest first rest,
}

#[partial]
def show_match_cases_rest (first : MatchCase) (rest : List MatchCase) : String :=
    match rest {
        List.empty => show_match_case first,
        List.cons x y =>
            let first_str := show_match_case first in
            let rest_str := show_match_cases_rest x y in
            let sep := String.concat first_str ",\n " in
            String.concat sep rest_str,
    }

#[partial]
def show_match_case (c : MatchCase) : String := match c {
    MatchCase.mc name args body =>
        let name_str := show_identifier name in
        let body_str := show_term body in
        match args {
            List.empty =>
                let lhs := String.concat name_str " => " in
                String.concat lhs body_str,
            List.cons hd tl =>
                let args_str := show_id_list args in
                let lhs := String.concat name_str " " in
                let mid := String.concat lhs args_str in
                let rt := String.concat " => " body_str in
                String.concat mid rt,
        },
}

def show_id_list (ids : List Identifier) : String := match ids {
    List.empty => "",
    List.cons hd rest => show_id_list_rest hd rest,
}

def show_id_list_rest (hd : Identifier) (rest : List Identifier) : String :=
    match rest {
        List.empty => show_identifier hd,
        List.cons x y =>
            let hd_str := show_identifier hd in
            let rest_str := show_id_list_rest x y in
            let sp := String.concat hd_str " " in
            String.concat sp rest_str,
    }

#[partial]
def show_native (n : Native) : String := match n {
    Native.mk name num_args args => "native",
}

#[partial]
def show_con (c : Con) : String := match c {
    Con.mk name typ_name num_args args =>
        let typ_str := show_module_path typ_name in
        let name_str := show_identifier name in
        let dot := String.concat typ_str "." in
        let qualified := String.concat dot name_str in
        match args {
            List.empty => qualified,
            List.cons x y =>
                let args_str := show_opt_term_list args in
                let lp := String.concat "(" qualified in
                let sp := String.concat " " args_str in
                let inner := String.concat lp sp in
                String.concat inner ")",
        },
}

#[partial]
def show_opt_term_list (args : List (Option Term)) : String := match args {
    List.empty => "",
    List.cons hd rest => show_opt_term_rest hd rest,
}

#[partial]
def show_opt_term_rest (hd : Option Term) (rest : List (Option Term)) : String :=
    let head_str := match hd {
        Option.some t => show_term t,
        Option.none => "_",
    } in
    match rest {
        List.empty => head_str,
        List.cons x y =>
            let rest_str := show_opt_term_rest x y in
            let sp := String.concat head_str " " in
            String.concat sp rest_str,
    }

#[partial]
def show_type_constraint (tc : TypeConstraint) : String := match tc {
    TypeConstraint.mk cls vars =>
        let cls_str := show_module_path cls in
        let vars_str := show_id_list vars in
        let lb := String.concat "[" cls_str in
        let sp := String.concat " " vars_str in
        let inner := String.concat lb sp in
        String.concat inner "]",
}

#[partial]
def show_def (d : Def) : String := match d {
    Def.mk name typ term constraints attrs =>
        let name_str := show_module_path name in
        let type_str := show_term typ in
        let term_str := show_term term in
        let prefix := String.concat "def " name_str in
        let colon_type := String.concat " : " type_str in
        let with_type := String.concat prefix colon_type in
        let eq_body := String.concat " := " term_str in
        String.concat with_type eq_body,
}

#[partial]
def show_inductive (ind : Inductive) : String := match ind {
    Inductive.mk name params typ constructors attrs =>
        let name_str := show_module_path name in
        let header := String.concat "type " name_str in
        let with_params := if list_param_is_empty params then header
                           else String.concat header (String.concat " " (show_params params)) in
        let ctors_str := show_induct_constructors constructors in
        let ob := String.concat with_params " {\n  " in
        let inner := String.concat ob ctors_str in
        String.concat inner "\n}",
}

def list_param_is_empty (ps : List Param) : Bool := match ps {
    List.empty => true,
    List.cons x y => false,
}

#[partial]
def show_params (ps : List Param) : String := match ps {
    List.empty => "",
    List.cons hd rest => show_params_rest hd rest,
}

#[partial]
def show_params_rest (hd : Param) (rest : List Param) : String :=
    match rest {
        List.empty => show_param hd,
        List.cons x y =>
            let hd_str := show_param hd in
            let rest_str := show_params_rest x y in
            let sp := String.concat hd_str " " in
            String.concat sp rest_str,
    }

def show_induct_constructors (ctors : List InductConstructor) : String := match ctors {
    List.empty => "",
    List.cons hd rest => show_induct_ctors_rest hd rest,
}

#[partial]
def show_induct_ctors_rest (hd : InductConstructor) (rest : List InductConstructor) : String :=
    match rest {
        List.empty => show_induct_constructor hd,
        List.cons x y =>
            let hd_str := show_induct_constructor hd in
            let rest_str := show_induct_ctors_rest x y in
            let sep := String.concat hd_str ",\n  " in
            String.concat sep rest_str,
    }

#[partial]
def show_induct_constructor (c : InductConstructor) : String := match c {
    InductConstructor.mk name params typ =>
        let name_str := show_module_path name in
        let with_params := match params {
            List.empty => name_str,
            List.cons x y =>
                let params_str := show_induct_ctor_params params in
                let lp := String.concat " (" params_str in
                let rp := String.concat lp ")" in
                String.concat name_str rp,
        } in
        with_params,
}

#[partial]
def show_induct_ctor_params (ps : List Param) : String := match ps {
    List.empty => "",
    List.cons hd rest => show_induct_ctor_params_rest hd rest,
}

#[partial]
def show_induct_ctor_params_rest (hd : Param) (rest : List Param) : String :=
    let name_str := show_identifier (param_name hd) in
    let type_str := show_term (param_type hd) in
    let colon_type := String.concat " : " type_str in
    let prefix := String.concat name_str colon_type in
    match rest {
        List.empty => prefix,
        List.cons x y =>
            let rest_str := show_induct_ctor_params_rest x y in
            let sep := String.concat prefix ", " in
            String.concat sep rest_str,
    }

def param_name (p : Param) : Identifier := match p {
    Param.mk name type_ mult default => name,
}

def param_type (p : Param) : Term := match p {
    Param.mk name type_ mult default => type_,
}

#[partial]
def show_struct (s : Struct) : String := match s {
    Struct.mk name fields =>
        let name_str := show_identifier name in
        let header := String.concat "struct " name_str in
        let fields_str := show_struct_fields fields in
        let ob := String.concat header " {\n  " in
        let inner := String.concat ob fields_str in
        String.concat inner "\n}",
}

def show_struct_fields (fs : List StructField) : String := match fs {
    List.empty => "",
    List.cons hd rest => show_struct_fields_rest hd rest,
}

#[partial]
def show_struct_fields_rest (hd : StructField) (rest : List StructField) : String :=
    match rest {
        List.empty => show_struct_field hd,
        List.cons x y =>
            let hd_str := show_struct_field hd in
            let rest_str := show_struct_fields_rest x y in
            let sep := String.concat hd_str ",\n  " in
            String.concat sep rest_str,
    }

#[partial]
def show_struct_field (f : StructField) : String := match f {
    StructField.mk name typ default =>
        let name_str := show_identifier name in
        let type_str := show_term typ in
        let colon_type := String.concat " : " type_str in
        let base := String.concat name_str colon_type in
        match default {
            Option.some def_val =>
                let def_str := show_term def_val in
                let eq_def := String.concat " := " def_str in
                String.concat base eq_def,
            Option.none => base,
        },
}

#[partial]
def show_class (cls : Class) : String := match cls {
    Class.mk name params constraints methods =>
        let name_str := show_identifier name in
        let header := String.concat "class " name_str in
        let with_params := match params {
            List.empty => header,
            List.cons x y =>
                let params_str := show_class_params params in
                let sp := String.concat " " params_str in
                String.concat header sp,
        } in
        let methods_str := show_class_defs methods in
        let ob := String.concat with_params " {\n  " in
        let inner := String.concat ob methods_str in
        String.concat inner "\n}",
}

def show_class_params (ps : List Param) : String := match ps {
    List.empty => "",
    List.cons hd rest => show_class_params_rest hd rest,
}

#[partial]
def show_class_params_rest (hd : Param) (rest : List Param) : String :=
    let prefix := String.concat "(" (show_param hd) in
    match rest {
        List.empty => String.concat prefix ")",
        List.cons x y =>
            let rest_str := show_class_params_rest x y in
            let rp := String.concat prefix ") " in
            String.concat rp rest_str,
    }

def show_class_defs (ms : List ClassDef) : String := match ms {
    List.empty => "",
    List.cons hd rest => show_class_defs_rest hd rest,
}

#[partial]
def show_class_defs_rest (hd : ClassDef) (rest : List ClassDef) : String :=
    match rest {
        List.empty => show_class_def hd,
        List.cons x y =>
            let hd_str := show_class_def hd in
            let rest_str := show_class_defs_rest x y in
            let sep := String.concat hd_str ",\n  " in
            String.concat sep rest_str,
    }

#[partial]
def show_class_def (m : ClassDef) : String := match m {
    ClassDef.mk name typ default =>
        let name_str := show_identifier name in
        let type_str := show_term typ in
        let def_name := String.concat "def " name_str in
        let colon_type := String.concat " : " type_str in
        let base := String.concat def_name colon_type in
        match default {
            Option.some def_val =>
                let def_str := show_term def_val in
                let eq_def := String.concat " := " def_str in
                String.concat base eq_def,
            Option.none => base,
        },
}

def show_instance (ins : Instance) : String := match ins {
    Instance.mk name cls constraints args =>
        let cls_str := show_module_path cls in
        String.concat "instance " cls_str,
}

#[partial]
def show_infix_decl (op : Operator) (path : ModulePath) : String :=
    let op_str := show_operator op in
    let path_str := show_module_path path in
    let op_part := String.concat "infix: " op_str in
    let eq_part := String.concat " := " path_str in
    String.concat op_part eq_part

#[partial]
def show_decl (d : Decl) : String := match d {
    def_d def_ => show_def def_,
    inductive_d ind => show_inductive ind,
    struct_d s => show_struct s,
    class_d cls => show_class cls,
    instance_d ins => show_instance ins,
    infix_d op path => show_infix_decl op path,
    use_d path filter =>
        let path_str := show_module_path path in
        String.concat (String.concat "use " path_str) (show_use_filter filter),
    open_d path filter =>
        let path_str := show_module_path path in
        String.concat (String.concat "open " path_str) (show_open_filter filter),
    scoped_open_d path filter inner =>
        let path_str := show_module_path path in
        let header := String.concat (String.concat "open " path_str) (show_open_filter filter) in
        String.concat (String.concat header " in ") (show_decl inner),
}

/// A single item inside a `use Module { ... }` brace filter. Mirrors
/// Rust's `Display for UseItem` (core/src/term.rs).
#[partial]
def show_use_item (item : UseItem) : String := match item {
    UseItem.use_name name => show_identifier name,
    UseItem.use_rename name alias =>
        String.concat (String.concat (show_identifier name) " as ") (show_identifier alias),
    UseItem.use_glob => "*",
    UseItem.use_sub name items =>
        String.concat (String.concat (show_identifier name) " ") (show_use_items_braced items),
    UseItem.use_sub_rename name alias items =>
        let header := String.concat (String.concat (show_identifier name) " as ") (show_identifier alias) in
        String.concat (String.concat header " ") (show_use_items_braced items),
}

#[partial]
def show_use_items_joined (items : List UseItem) : String := match items {
    List.empty => "",
    List.cons hd rest => show_use_items_joined_rest hd rest,
}

#[partial]
def show_use_items_joined_rest (hd : UseItem) (rest : List UseItem) : String :=
    match rest {
        List.empty => show_use_item hd,
        List.cons x y =>
            let sep := String.concat (show_use_item hd) ", " in
            String.concat sep (show_use_items_joined rest),
    }

#[partial]
def show_use_items_braced (items : List UseItem) : String :=
    String.concat (String.concat "{" (show_use_items_joined items)) "}"

/// What a `use` declaration imports. Bare `use Module` (deprecated)
/// renders as no suffix at all.
def show_use_filter (filter : UseFilter) : String := match filter {
    UseFilter.use_bare => "",
    UseFilter.use_items items => String.concat " " (show_use_items_braced items),
}

#[partial]
def show_identifier_list_joined (names : List Identifier) : String := match names {
    List.empty => "",
    List.cons hd rest => show_identifier_list_joined_rest hd rest,
}

#[partial]
def show_identifier_list_joined_rest (hd : Identifier) (rest : List Identifier) : String :=
    match rest {
        List.empty => show_identifier hd,
        List.cons x y =>
            let sep := String.concat (show_identifier hd) ", " in
            String.concat sep (show_identifier_list_joined rest),
    }

/// What an `open` declaration makes unqualified. `open_all` (no braces)
/// renders as no suffix at all.
def show_open_filter (filter : OpenFilter) : String := match filter {
    OpenFilter.open_all => "",
    OpenFilter.open_only names =>
        String.concat (String.concat " {" (show_identifier_list_joined names)) "}",
}

/// Tests

#[test]
def test_show_var_named : Bool :=
    let id := Identifier.id "x" in
    let dbg := DebugName.named id in
    let t := Term.var 0 dbg in
    show_term t == "x"

#[test]
def test_show_var_unnamed : Bool :=
    let dbg := DebugName.unnamed in
    let t := Term.var 1 dbg in
    show_term t == "_"

#[test]
def test_show_lam_unnamed : Bool :=
    let dbg := DebugName.unnamed in
    let body := Term.var 0 DebugName.unnamed in
    let t := Term.lam dbg Term.hole body in
    show_term t == "(fn _ : _ => _)"

#[test]
def test_show_lam_named : Bool :=
    let id := Identifier.id "x" in
    let dbg := DebugName.named id in
    let body := Term.var 0 dbg in
    let t := Term.lam dbg (Term.type_ 1) body in
    show_term t == "(fn x : Type => x)"

#[test]
def test_show_forall_named : Bool :=
    let id := Identifier.id "A" in
    let dbg := DebugName.named id in
    let body := Term.type_ 1 in
    let t := Term.forall dbg (Term.type_ 1) body in
    show_term t == "{A : Type} -> Type"

#[test]
def test_show_forall_unnamed : Bool :=
    let dbg := DebugName.unnamed in
    let body := Term.type_ 1 in
    let t := Term.forall dbg (Term.type_ 1) body in
    show_term t == "{_ : Type} -> Type"

#[test]
def test_show_pi : Bool :=
    let arg := Term.type_ 1 in
    let ret := Term.type_ 1 in
    let t := Term.pi arg ret in
    show_term t == "(Type -> Type)"

#[test]
def test_show_app : Bool :=
    let fun_id := Identifier.id "f" in
    let arg_id := Identifier.id "x" in
    let fun_ := Term.var 0 (DebugName.named fun_id) in
    let arg := Term.var 1 (DebugName.named arg_id) in
    let t := Term.app fun_ arg in
    show_term t == "(f x)"

#[test]
def test_show_lit_str : Bool :=
    let t := Term.lit (Literal.str "hello") in
    show_term t == "\"hello\""

#[test]
def test_show_lit_num : Bool :=
    let t := Term.lit (Literal.num 42 NumSuffix.i64) in
    show_term t == "42i64"

#[test]
def test_show_ntv : Bool :=
    let ntv := Native.mk (Identifier.id "add") (0i64) List.empty in
    let t := Term.ntv ntv in
    show_term t == "native"

#[test]
def test_show_con_named_args : Bool :=
    let args := List.cons (Option.some (Term.var 0 DebugName.unnamed))
                         List.empty in
    let con := Con.mk (Identifier.id "some")
                      (ModulePath.mp (List.cons (Identifier.id "Option") List.empty))
                      (1i64)
                      args in
    let t := Term.con con in
    show_term t == "(Option.some _)"

#[test]
def test_show_con_no_args : Bool :=
    let con := Con.mk (Identifier.id "true_")
                      (ModulePath.mp (List.cons (Identifier.id "Bool") List.empty))
                      (0i64)
                      List.empty in
    let t := Term.con con in
    show_term t == "Bool.true_"

#[test]
def test_show_type_prop : Bool :=
    show_term (Term.type_ 0) == "Prop"

#[test]
def test_show_type_type : Bool :=
    show_term (Term.type_ 1) == "Type"

#[test]
def test_show_type_type1 : Bool :=
    show_term (Term.type_ 2) == "Type 1"

#[test]
def test_show_type_type2 : Bool :=
    show_term (Term.type_ 3) == "Type 2"

#[test]
def test_show_hole : Bool :=
    show_term Term.hole == "_"

#[test]
def test_show_literal_if : Bool :=
    let cond := Term.var 0 (DebugName.named (Identifier.id "x")) in
    let then_ := Term.lit (Literal.num 1 NumSuffix.i64) in
    let else_ := Term.lit (Literal.num 0 NumSuffix.i64) in
    let t := Term.lit (Literal.if_ cond then_ else_) in
    show_term t == "if x then 1i64 else 0i64"

#[test]
def test_show_literal_match : Bool :=
    let scrutinee := Term.var 0 (DebugName.named (Identifier.id "x")) in
    let case_name := Identifier.id "some" in
    let case_arg := Identifier.id "v" in
    let case_args := List.cons case_arg List.empty in
    let case_body := Term.var 0 (DebugName.named (Identifier.id "v")) in
    let mc := MatchCase.mc case_name case_args case_body in
    let cases := List.cons mc List.empty in
    let t := Term.lit (Literal.match_ scrutinee cases) in
    show_term t == "match x {\n some v => v\n}"

#[test]
def test_show_identifier : Bool :=
    show_identifier (Identifier.id "foo") == "foo"

#[test]
def test_show_operator : Bool :=
    show_operator (Operator.operator ">>=") == ">>="

#[test]
def test_show_module_path_single : Bool :=
    show_module_path (ModulePath.mp (List.cons (Identifier.id "List") List.empty)) == "List"

#[test]
def test_show_module_path_multi : Bool :=
    let ids := List.cons (Identifier.id "List") (List.cons (Identifier.id "append") List.empty) in
    show_module_path (ModulePath.mp ids) == "List.append"

#[test]
def test_show_num_suffix_i8 : Bool :=
    show_num_suffix NumSuffix.i8 == "i8"

#[test]
def test_show_num_suffix_i64 : Bool :=
    show_num_suffix NumSuffix.i64 == "i64"

#[test]
def test_show_num_suffix_f64 : Bool :=
    show_num_suffix NumSuffix.f64 == "f64"

#[test]
def test_show_multiplicity_zero : Bool :=
    show_multiplicity Multiplicity.zero == "0"

#[test]
def test_show_multiplicity_many : Bool :=
    show_multiplicity Multiplicity.many == ""

#[test]
def test_show_multiplicity_linear : Bool :=
    show_multiplicity Multiplicity.linear == "!"

#[test]
def test_show_multiplicity_affine : Bool :=
    show_multiplicity Multiplicity.affine == "?"

#[test]
def test_show_param_simple : Bool :=
    let id := Identifier.id "x" in
    let typ := Term.type_ 1 in
    let p := Param.mk id typ Multiplicity.many Option.none in
    show_param p == "x : Type"

#[test]
def test_show_param_with_default : Bool :=
    let id := Identifier.id "x" in
    let typ := Term.type_ 1 in
    let dflt := Term.type_ 1 in
    let p := Param.mk id typ Multiplicity.many (Option.some dflt) in
    show_param p == "x : Type := Type"

#[test]
def test_show_param_linear : Bool :=
    let id := Identifier.id "x" in
    let typ := Term.type_ 1 in
    let p := Param.mk id typ Multiplicity.linear Option.none in
    show_param p == "!x : Type"

#[test]
def test_show_universe_prop : Bool :=
    show_universe 0 == "Prop"

#[test]
def test_show_universe_type : Bool :=
    show_universe 1 == "Type"

#[test]
def test_show_universe_type1 : Bool :=
    show_universe 2 == "Type 1"

#[test]
def test_show_debug_name_named : Bool :=
    show_debug_name (DebugName.named (Identifier.id "x")) == "x"

#[test]
def test_show_debug_name_unnamed : Bool :=
    show_debug_name DebugName.unnamed == "_"

#[test]
def test_show_decl_use : Bool :=
    let d := Decl.use_d (ModulePath.mp (List.cons (Identifier.id "prelude") List.empty)) UseFilter.use_bare in
    show_decl d == "use prelude"

#[test]
def test_show_decl_open : Bool :=
    let d := Decl.open_d (ModulePath.mp (List.cons (Identifier.id "IO") List.empty)) OpenFilter.open_all in
    show_decl d == "open IO"

#[test]
def test_show_decl_use_glob : Bool :=
    let items := List.cons UseItem.use_glob List.empty in
    let d := Decl.use_d (ModulePath.mp (List.cons (Identifier.id "io") List.empty)) (UseFilter.use_items items) in
    show_decl d == "use io {*}"

#[test]
def test_show_decl_open_filtered : Bool :=
    let names := List.cons (Identifier.id "println") List.empty in
    let d := Decl.open_d (ModulePath.mp (List.cons (Identifier.id "IO") List.empty)) (OpenFilter.open_only names) in
    show_decl d == "open IO {println}"

#[test]
def test_show_decl_scoped_open : Bool :=
    let inner := Decl.def_d (Def.mk (ModulePath.mp (List.cons (Identifier.id "z") List.empty)) Term.hole Term.hole List.empty List.empty) in
    let d := Decl.scoped_open_d (ModulePath.mp (List.cons (Identifier.id "Nat") List.empty)) OpenFilter.open_all inner in
    show_decl d == "open Nat in def z : _ := _"

#[test]
def test_show_decl_infix : Bool :=
    let d := Decl.infix_d (Operator.operator ">>=") (ModulePath.mp (List.cons (Identifier.id "Monad") (List.cons (Identifier.id "bind") List.empty))) in
    show_decl d == "infix: >>= := Monad.bind"

#[test]
def test_show_decl_def : Bool :=
    let name := ModulePath.mp (List.cons (Identifier.id "id") List.empty) in
    let path := Identifier.id "x" in
    let var_t := Term.var 0 (DebugName.named path) in
    let lam := Term.lam (DebugName.named path) (Term.type_ 1) var_t in
    let d := Def.mk name (Term.type_ 1) lam List.empty List.empty in
    let decl := Decl.def_d d in
    show_decl decl == "def id : Type := (fn x : Type => x)"

#[test]
def test_show_decl_class : Bool :=
    let name := Identifier.id "Show" in
    let show_name := Identifier.id "show" in
    let cd := ClassDef.mk show_name (Term.type_ 1) Option.none in
    let methods := List.cons cd List.empty in
    let cls := Class.mk name List.empty List.empty methods in
    let decl := Decl.class_d cls in
    show_decl decl == "class Show {\n  def show : Type\n}"

#[test]
def test_show_decl_struct : Bool :=
    let name := Identifier.id "Point" in
    let field := StructField.mk (Identifier.id "x") (Term.lit (Literal.num 0 NumSuffix.i64)) Option.none in
    let decl := Decl.struct_d (Struct.mk name (List.cons field List.empty)) in
    show_decl decl == "struct Point {\n  x : 0i64\n}"

#[test]
def test_show_decl_inductive : Bool :=
    let name := ModulePath.mp (List.cons (Identifier.id "Bool") List.empty) in
    let ct1 := InductConstructor.mk (ModulePath.mp (List.cons (Identifier.id "true") List.empty)) List.empty (Term.type_ 1) in
    let ct2 := InductConstructor.mk (ModulePath.mp (List.cons (Identifier.id "false") List.empty)) List.empty (Term.type_ 1) in
    let decl := Decl.inductive_d (Inductive.mk name List.empty (Term.type_ 1) (List.cons ct1 (List.cons ct2 List.empty)) List.empty) in
    show_decl decl == "type Bool {\n  true,\n  false\n}"


