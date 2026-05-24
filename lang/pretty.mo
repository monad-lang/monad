use lang.types

open Term
open Literal
open Decl
open Multiplicity
open DebugName
open NumSuffix

def show_identifier (id : Identifier) : String := match id {
    Identifier.id s => s,
}

def show_operator (op : Operator) : String := match op {
    Operator.operator s => s,
}

def show_module_path (mp : ModulePath) : String := match mp {
    ModulePath.mp ids => join_identifiers ids,
}

def join_identifiers (ids : List Identifier) : String := match ids {
    List.empty => "",
    List.cons hd rest => join_id_rest hd rest,
}

def join_id_rest (hd : Identifier) (rest : List Identifier) : String :=
    match rest {
        List.empty => show_identifier hd,
        List.cons x y =>
            let dot := String.concat (show_identifier hd) "." in
            let rest_str := join_id_rest x y in
            String.concat dot rest_str,
    }

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

@[partial]
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

@[partial]
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

@[partial]
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

@[partial]
def show_match_cases_rest (first : MatchCase) (rest : List MatchCase) : String :=
    match rest {
        List.empty => show_match_case first,
        List.cons x y =>
            let first_str := show_match_case first in
            let rest_str := show_match_cases_rest x y in
            let sep := String.concat first_str ",\n " in
            String.concat sep rest_str,
    }

@[partial]
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

@[partial]
def show_native (n : Native) : String := match n {
    Native.mk name num_args args => "native",
}

@[partial]
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

@[partial]
def show_opt_term_list (args : List (Option Term)) : String := match args {
    List.empty => "",
    List.cons hd rest => show_opt_term_rest hd rest,
}

@[partial]
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

@[partial]
def show_type_constraint (tc : TypeConstraint) : String := match tc {
    TypeConstraint.mk cls vars =>
        let cls_str := show_module_path cls in
        let vars_str := show_id_list vars in
        let lb := String.concat "[" cls_str in
        let sp := String.concat " " vars_str in
        let inner := String.concat lb sp in
        String.concat inner "]",
}

@[partial]
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

@[partial]
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

@[partial]
def show_params (ps : List Param) : String := match ps {
    List.empty => "",
    List.cons hd rest => show_params_rest hd rest,
}

@[partial]
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

@[partial]
def show_induct_ctors_rest (hd : InductConstructor) (rest : List InductConstructor) : String :=
    match rest {
        List.empty => show_induct_constructor hd,
        List.cons x y =>
            let hd_str := show_induct_constructor hd in
            let rest_str := show_induct_ctors_rest x y in
            let sep := String.concat hd_str ",\n  " in
            String.concat sep rest_str,
    }

@[partial]
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

@[partial]
def show_induct_ctor_params (ps : List Param) : String := match ps {
    List.empty => "",
    List.cons hd rest => show_induct_ctor_params_rest hd rest,
}

@[partial]
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

@[partial]
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

@[partial]
def show_struct_fields_rest (hd : StructField) (rest : List StructField) : String :=
    match rest {
        List.empty => show_struct_field hd,
        List.cons x y =>
            let hd_str := show_struct_field hd in
            let rest_str := show_struct_fields_rest x y in
            let sep := String.concat hd_str ",\n  " in
            String.concat sep rest_str,
    }

@[partial]
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

@[partial]
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

@[partial]
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

@[partial]
def show_class_defs_rest (hd : ClassDef) (rest : List ClassDef) : String :=
    match rest {
        List.empty => show_class_def hd,
        List.cons x y =>
            let hd_str := show_class_def hd in
            let rest_str := show_class_defs_rest x y in
            let sep := String.concat hd_str ",\n  " in
            String.concat sep rest_str,
    }

@[partial]
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

@[partial]
def show_infix_decl (op : Operator) (path : ModulePath) : String :=
    let op_str := show_operator op in
    let path_str := show_module_path path in
    let op_part := String.concat "infix: " op_str in
    let eq_part := String.concat " := " path_str in
    String.concat op_part eq_part

@[partial]
def show_decl (d : Decl) : String := match d {
    def_d def_ => show_def def_,
    inductive_d ind => show_inductive ind,
    struct_d s => show_struct s,
    class_d cls => show_class cls,
    instance_d ins => show_instance ins,
    infix_d op path => show_infix_decl op path,
    use_d path =>
        let path_str := show_module_path path in
        String.concat "use " path_str,
    open_d path =>
        let path_str := show_module_path path in
        String.concat "open " path_str,
}


