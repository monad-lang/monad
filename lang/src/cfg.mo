/// `#[cfg ...]` predicates over mote features. Mirrors `rust/core/src/cfg.rs`.
///
/// `#[cfg P1 P2 ...]` is an implicit `all`; each `P` is a flag (`test`), a
/// key/value block (`{feature := "sys"}`) or a combinator group (`[not P]`,
/// `[all P...]`, `[any P...]`). Unknown flags and keys are false.
///
/// `test` is decided by the test-mode filters, so `CfgEnv.keep` drops a
/// declaration only when its predicate is false with and without `test`.

use lang::types {AttrArg, Attribute, Identifier}
use std::list {List.length}

pub type CfgPred {
    flag (name : String),
    key_value (key : String) (value : String),
    negate (p : CfgPred),
    all_of (ps : List CfgPred),
    any_of (ps : List CfgPred),
}

/// The features enabled for the mote that owns the file being parsed.
pub struct CfgEnv {
    features : List String,
}

pub def CfgEnv.empty : CfgEnv :=
    let e : CfgEnv := { features := List.empty } in
    e

def cfg_mem (x : String) (xs : List String) : Bool :=
    match xs {
        List.empty => false,
        List.cons y rest => String.beq x y || cfg_mem x rest,
    }

def cfg_id (i : Identifier) : String :=
    match i {
        Identifier.id s => s,
    }

/// The predicate of one `#[cfg ...]` attribute's args; `none` if malformed.
pub def CfgPred.parse (args : List AttrArg) : Option CfgPred :=
    match cfg_parse_list args {
        Option.some ps => Option.some (cfg_all_or_single ps),
        Option.none => Option.none,
    }

def cfg_all_or_single (ps : List CfgPred) : CfgPred :=
    if I64.beq (List.length ps) 1 then cfg_head_or ps (CfgPred.all_of List.empty) else CfgPred.all_of ps

def cfg_head_or (ps : List CfgPred) (d : CfgPred) : CfgPred :=
    match ps {
        List.cons p _ => p,
        List.empty => d,
    }

def cfg_parse_list (args : List AttrArg) : Option (List CfgPred) :=
    match args {
        List.empty => Option.some List.empty,
        List.cons a rest => cfg_cons (cfg_parse_one a) (cfg_parse_list rest),
    }

def cfg_cons (h : Option CfgPred) (t : Option (List CfgPred)) : Option (List CfgPred) :=
    match h {
        Option.some p => match t {
            Option.some ps => Option.some (List.cons p ps),
            Option.none => Option.none,
        },
        Option.none => Option.none,
    }

def cfg_parse_one (a : AttrArg) : Option CfgPred :=
    match a {
        AttrArg.ident i => Option.some (CfgPred.flag (cfg_id i)),
        AttrArg.named k v => cfg_parse_named (cfg_id k) v,
        AttrArg.group items => cfg_parse_group items,
        AttrArg.str _ => Option.none,
        AttrArg.num _ => Option.none,
    }

def cfg_parse_named (k : String) (v : AttrArg) : Option CfgPred :=
    match v {
        AttrArg.str s => Option.some (CfgPred.key_value k s),
        _ => Option.none,
    }

def cfg_parse_group (items : List AttrArg) : Option CfgPred :=
    match items {
        List.cons h rest => cfg_group_ident h rest,
        List.empty => Option.none,
    }

#[terminating]
def cfg_group_ident (h : AttrArg) (rest : List AttrArg) : Option CfgPred :=
    match h {
        AttrArg.ident head => cfg_group_head (cfg_id head) (cfg_parse_list rest),
        _ => Option.none,
    }

def cfg_group_head (head : String) (rest : Option (List CfgPred)) : Option CfgPred :=
    match rest {
        Option.none => Option.none,
        Option.some ps =>
            if String.beq head "not" then cfg_not ps
            else if String.beq head "all" then Option.some (CfgPred.all_of ps)
            else if String.beq head "any" then Option.some (CfgPred.any_of ps)
            else Option.none,
    }

def cfg_not (ps : List CfgPred) : Option CfgPred :=
    if I64.beq (List.length ps) 1
    then Option.some (CfgPred.negate (cfg_head_or ps (CfgPred.all_of List.empty)))
    else Option.none

pub def CfgPred.eval (p : CfgPred) (env : CfgEnv) (test : Bool) : Bool :=
    match p {
        CfgPred.flag f => test && String.beq f "test",
        CfgPred.key_value k v => String.beq k "feature" && cfg_mem v env.features,
        CfgPred.negate q => Bool.not (CfgPred.eval q env test),
        CfgPred.all_of ps => cfg_eval_all ps env test,
        CfgPred.any_of ps => cfg_eval_any ps env test,
    }

def cfg_eval_all (ps : List CfgPred) (env : CfgEnv) (test : Bool) : Bool :=
    match ps {
        List.empty => true,
        List.cons p rest => CfgPred.eval p env test && cfg_eval_all rest env test,
    }

def cfg_eval_any (ps : List CfgPred) (env : CfgEnv) (test : Bool) : Bool :=
    match ps {
        List.empty => false,
        List.cons p rest => CfgPred.eval p env test || cfg_eval_any rest env test,
    }

/// Keep a declaration unless one of its `#[cfg]`s is false both with and
/// without `test`. A malformed predicate keeps the declaration.
pub def CfgEnv.keep (env : CfgEnv) (attrs : List Attribute) : Bool :=
    match attrs {
        List.empty => true,
        List.cons a rest => cfg_keep_one env a && CfgEnv.keep env rest,
    }

def cfg_keep_one (env : CfgEnv) (a : Attribute) : Bool :=
    match a {
        { name, args } =>
            if String.beq (cfg_id name) "cfg" then cfg_keep_pred env (CfgPred.parse args) else true,
    }

def cfg_keep_pred (env : CfgEnv) (p : Option CfgPred) : Bool :=
    match p {
        Option.none => true,
        Option.some q => CfgPred.eval q env true || CfgPred.eval q env false,
    }
