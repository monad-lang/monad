use lang.types
open types
use lang.pretty

open Term
open Literal
open Decl
open DebugName
open Identifier
open ModulePath
open NumSuffix
open Multiplicity

// --- Helper definitions (typed to avoid forall inference issues) ---

def test_id_x : Identifier := Identifier.id "x"

def test_id_y : Identifier := Identifier.id "y"

def test_id_s : Identifier := Identifier.id "s"

def test_id_A : Identifier := Identifier.id "A"

def empty_id_list : List Identifier := List.empty

def empty_match_cases : List MatchCase := List.empty

def empty_params : List Param := List.empty

def empty_constraints : List TypeConstraint := List.empty

def empty_attrs : List String := List.empty

def empty_opt_terms : List (Option Term) := List.empty

def empty_ctors : List InductConstructor := List.empty

def empty_fields : List StructField := List.empty

def empty_class_defs : List ClassDef := List.empty

def none_term : Option Term := Option.none

// --- show_identifier tests ---

@[test]
def test_show_identifier : Bool :=
    let result : String := show_identifier test_id_x in
    String.beq result "x"

// --- show_module_path tests ---

@[test]
def test_show_module_path_single : Bool :=
    let path : ModulePath := ModulePath.mp (List.cons test_id_A List.empty) in
    let result : String := show_module_path path in
    String.beq result "A"

@[test]
def test_show_module_path_dotted : Bool :=
    let path : ModulePath := ModulePath.mp (List.cons test_id_A (List.cons test_id_x List.empty)) in
    let result : String := show_module_path path in
    String.beq result "A.x"

// --- show_num_suffix tests ---

@[test]
def test_show_num_suffix_i64 : Bool :=
    let result : String := show_num_suffix NumSuffix.i64 in
    String.beq result "i64"

@[test]
def test_show_num_suffix_i8 : Bool :=
    let result : String := show_num_suffix NumSuffix.i8 in
    String.beq result "i8"

@[test]
def test_show_num_suffix_u32 : Bool :=
    let result : String := show_num_suffix NumSuffix.u32 in
    String.beq result "u32"

@[test]
def test_show_num_suffix_f64 : Bool :=
    let result : String := show_num_suffix NumSuffix.f64 in
    String.beq result "f64"

// --- show_multiplicity tests ---

@[test]
def test_show_mult_zero : Bool :=
    let result : String := show_multiplicity Multiplicity.zero in
    String.beq result "0"

@[test]
def test_show_mult_many : Bool :=
    let result : String := show_multiplicity Multiplicity.many in
    String.beq result ""

@[test]
def test_show_mult_linear : Bool :=
    let result : String := show_multiplicity Multiplicity.linear in
    String.beq result "!"

@[test]
def test_show_mult_affine : Bool :=
    let result : String := show_multiplicity Multiplicity.affine in
    String.beq result "?"

// --- show_universe tests ---

@[test]
def test_show_universe_prop : Bool :=
    let result : String := show_universe 0 in
    String.beq result "Prop"

@[test]
def test_show_universe_type : Bool :=
    let result : String := show_universe 1 in
    String.beq result "Type"

@[test]
def test_show_universe_type_2 : Bool :=
    let result : String := show_universe 2 in
    String.beq result "Type 1"

@[test]
def test_show_universe_type_5 : Bool :=
    let result : String := show_universe 5 in
    String.beq result "Type 4"

// --- show_term tests ---

@[test]
def test_show_term_var : Bool :=
    let term : Term := Term.var 0 (DebugName.named test_id_x) in
    let result : String := show_term term in
    String.beq result "x"

@[test]
def test_show_term_var_unnamed : Bool :=
    let term : Term := Term.var 0 DebugName.unnamed in
    let result : String := show_term term in
    String.beq result "_"

@[test]
def test_show_term_hole : Bool :=
    let result : String := show_term Term.hole in
    String.beq result "_"

@[test]
def test_show_term_sort_prop : Bool :=
    let term : Term := Term.type_ 0 in
    let result : String := show_term term in
    String.beq result "Prop"

@[test]
def test_show_term_sort_type : Bool :=
    let term : Term := Term.type_ 1 in
    let result : String := show_term term in
    String.beq result "Type"

@[test]
def test_show_term_lam_simple : Bool :=
    let body : Term := Term.var 0 (DebugName.named test_id_x) in
    let lam : Term := Term.lam (DebugName.named test_id_x) (Term.type_ 1) body in
    let result : String := show_term lam in
    String.beq result "(fn x : Type => x)"

@[test]
def test_show_term_app_simple : Bool :=
    let fun : Term := Term.var 0 (DebugName.named (Identifier.id "f")) in
    let arg : Term := Term.var 1 (DebugName.named test_id_x) in
    let app : Term := Term.app fun arg in
    let result : String := show_term app in
    String.beq result "(f x)"

@[test]
def test_show_term_pi_simple : Bool :=
    let arg : Term := Term.type_ 1 in
    let ret : Term := Term.type_ 1 in
    let pi : Term := Term.pi arg ret in
    let result : String := show_term pi in
    String.beq result "(Type -> Type)"

@[test]
def test_show_term_forall_simple : Bool :=
    let kind : Term := Term.type_ 1 in
    let body : Term := Term.var 0 (DebugName.named test_id_A) in
    let forall : Term := Term.forall (DebugName.named test_id_A) kind body in
    let result : String := show_term forall in
    String.beq result "{A : Type} -> A"

// --- show_literal tests ---

@[test]
def test_show_literal_str : Bool :=
    let lit : Literal := Literal.str "hello" in
    let term : Term := Term.lit lit in
    let result : String := show_term term in
    String.beq result "\"hello\""

@[test]
def test_show_literal_num_i64 : Bool :=
    let lit : Literal := Literal.num 42 NumSuffix.i64 in
    let term : Term := Term.lit lit in
    let result : String := show_term term in
    String.beq result "42i64"

@[test]
def test_show_literal_num_i32 : Bool :=
    let lit : Literal := Literal.num 10 NumSuffix.i32 in
    let term : Term := Term.lit lit in
    let result : String := show_term term in
    String.beq result "10i32"

@[test]
def test_show_literal_if : Bool :=
    let cond : Term := Term.lit (Literal.str "x") in
    let then_ : Term := Term.lit (Literal.num 1 NumSuffix.i64) in
    let else_ : Term := Term.lit (Literal.num 0 NumSuffix.i64) in
    let lit : Literal := Literal.if_ cond then_ else_ in
    let term : Term := Term.lit lit in
    let result : String := show_term term in
    String.beq result "if \"x\" then 1i64 else 0i64"

@[test]
def test_show_literal_match_simple : Bool :=
    let scrut : Term := Term.lit (Literal.num 5 NumSuffix.i64) in
    let case_none : MatchCase := MatchCase.mc (Identifier.id "none") empty_id_list (Term.lit (Literal.num 0 NumSuffix.i64)) in
    let case_some : MatchCase := MatchCase.mc (Identifier.id "some") (List.cons test_id_x List.empty) (Term.var 0 (DebugName.named test_id_x)) in
    let cases : List MatchCase := List.cons case_none (List.cons case_some List.empty) in
    let lit : Literal := Literal.match_ scrut cases in
    let term : Term := Term.lit lit in
    let result : String := show_term term in
    String.beq result "match 5i64 {\n none => 0i64,\n some x => x\n}"

// --- show_native tests ---

@[test]
def test_show_term_native : Bool :=
    let ntv : Native := Native.mk test_id_s 0 empty_opt_terms in
    let term : Term := Term.ntv ntv in
    let result : String := show_term term in
    String.beq result "native"

// --- show_con tests ---

@[test]
def test_show_term_con_no_args : Bool :=
    let typ_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Option") List.empty) in
    let con : Con := Con.mk (Identifier.id "none") typ_path 0 empty_opt_terms in
    let term : Term := Term.con con in
    let result : String := show_term term in
    String.beq result "Option.none"

@[test]
def test_show_term_con_with_args : Bool :=
    let typ_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Option") List.empty) in
    let arg1 : Option Term := Option.some (Term.lit (Literal.num 42 NumSuffix.i64)) in
    let args : List (Option Term) := List.cons arg1 empty_opt_terms in
    let con : Con := Con.mk (Identifier.id "some") typ_path 1 args in
    let term : Term := Term.con con in
    let result : String := show_term term in
    String.beq result "(Option.some 42i64)"

// --- show_decl tests ---

@[test]
def test_show_decl_def : Bool :=
    let name : ModulePath := ModulePath.mp (List.cons (Identifier.id "id") List.empty) in
    let typ : Term := Term.pi (Term.type_ 1) (Term.pi (Term.var 2 (DebugName.named test_id_A)) (Term.var 0 (DebugName.named test_id_A))) in
    let body : Term := Term.lam (DebugName.named test_id_x) (Term.var 1 (DebugName.named test_id_A)) (Term.var 0 (DebugName.named test_id_x)) in
    let def_ : Def := Def.mk name typ body empty_constraints empty_attrs in
    let decl : Decl := Decl.def_d def_ in
    let result : String := show_decl decl in
    String.beq result "def id : (Type -> (A -> A)) := (fn x : A => x)"

@[test]
def test_show_decl_inductive : Bool :=
    let type_name : ModulePath := ModulePath.mp (List.cons (Identifier.id "Bool") List.empty) in
    let true_cn : InductConstructor := InductConstructor.mk
        (ModulePath.mp (List.cons (Identifier.id "true") List.empty))
        empty_params (Term.type_ 1) in
    let false_cn : InductConstructor := InductConstructor.mk
        (ModulePath.mp (List.cons (Identifier.id "false") List.empty))
        empty_params (Term.type_ 1) in
    let ctors : List InductConstructor := List.cons true_cn (List.cons false_cn List.empty) in
    let ind : Inductive := Inductive.mk type_name empty_params (Term.type_ 1) ctors empty_attrs in
    let decl : Decl := Decl.inductive_d ind in
    let result : String := show_decl decl in
    String.beq result "type Bool {\n  true,\n  false\n}"

@[test]
def test_show_decl_struct : Bool :=
    let field_x : StructField := StructField.mk (Identifier.id "x") (Term.type_ 1) none_term in
    let field_y : StructField := StructField.mk (Identifier.id "y") (Term.type_ 1) none_term in
    let fields : List StructField := List.cons field_x (List.cons field_y List.empty) in
    let s : Struct := Struct.mk (Identifier.id "Point") fields in
    let decl : Decl := Decl.struct_d s in
    let result : String := show_decl decl in
    String.beq result "struct Point {\n  x : Type,\n  y : Type\n}"

@[test]
def test_show_decl_class_simple : Bool :=
    let meth_typ : Term := Term.pi (Term.var 1 (DebugName.named test_id_A)) (Term.pi (Term.var 0 (DebugName.named test_id_A)) (Term.type_ 0)) in
    let meth : ClassDef := ClassDef.mk (Identifier.id "eq") meth_typ none_term in
    let param_ : Param := Param.mk test_id_A (Term.type_ 1) Multiplicity.many none_term in
    let params : List Param := List.cons param_ empty_params in
    let methods : List ClassDef := List.cons meth empty_class_defs in
    let cls : Class := Class.mk (Identifier.id "Eq") params empty_constraints methods in
    let decl : Decl := Decl.class_d cls in
    let result : String := show_decl decl in
    String.beq result "class Eq (A : Type) {\n  def eq : (A -> (A -> Prop))\n}"

@[test]
def test_show_decl_infix : Bool :=
    let op : Operator := Operator.operator "++" in
    let path : ModulePath := ModulePath.mp (List.cons (Identifier.id "append") List.empty) in
    let decl : Decl := Decl.infix_d op path in
    let result : String := show_decl decl in
    String.beq result "infix: ++ := append"

@[test]
def test_show_decl_use : Bool :=
    let path : ModulePath := ModulePath.mp (List.cons (Identifier.id "prelude") List.empty) in
    let decl : Decl := Decl.use_d path UseFilter.use_bare in
    let result : String := show_decl decl in
    String.beq result "use prelude"

@[test]
def test_show_decl_open : Bool :=
    let path : ModulePath := ModulePath.mp (List.cons (Identifier.id "IO") List.empty) in
    let decl : Decl := Decl.open_d path OpenFilter.open_all in
    let result : String := show_decl decl in
    String.beq result "open IO"

// --- show_instance tests ---

@[test]
def test_show_instance : Bool :=
    let cls_path : ModulePath := ModulePath.mp (List.cons (Identifier.id "Show") List.empty) in
    let args : List Term := List.cons (Term.type_ 1) List.empty in
    let ins : Instance := Instance.mk (Identifier.id "inst") cls_path empty_constraints args in
    let result : String := show_instance ins in
    String.beq result "instance Show"

// --- show_match_case tests ---

@[test]
def test_show_match_case_no_args : Bool :=
    let body : Term := Term.lit (Literal.num 0 NumSuffix.i64) in
    let mc : MatchCase := MatchCase.mc (Identifier.id "none") empty_id_list body in
    let result : String := show_match_case mc in
    String.beq result "none => 0i64"

@[test]
def test_show_match_case_with_args : Bool :=
    let body : Term := Term.var 0 (DebugName.named test_id_x) in
    let args : List Identifier := List.cons test_id_x (List.cons test_id_y List.empty) in
    let mc : MatchCase := MatchCase.mc (Identifier.id "some") args body in
    let result : String := show_match_case mc in
    String.beq result "some x y => x"
