/// Tests for `#[cfg ...]` feature predicates (`lang/src/cfg.mo`) and the
/// parser's load-time filter (`decls_parser_located_cfg`). The Rust host's
/// mirror is `rust/core/src/cfg.rs`; the fixture text matches its `SRC`.

use std::list {List.intercalate}
use lang::types {AttrArg, Decl, Identifier, show_module_path, show_name_path}
use lang::cfg {CfgEnv, CfgEnv.empty, CfgEnv.for_mote, CfgEnv.keep, CfgPred, CfgPred.eval, CfgPred.parse}
use lang::parser {decls_parser_located, decls_parser_located_cfg}
use parsec::core {ParseResult}

def src : String :=
    "#[cfg {feature := \"x\"}]\ndef a : I64 := 1\n\n"
    ++ "#[cfg [not {feature := \"x\"}]]\ndef b : I64 := 2\n\n"
    ++ "#[cfg test]\ndef c : I64 := 3\n\n"
    ++ "#[cfg [any {feature := \"x\"} {feature := \"y\"}]]\ndef d : I64 := 4\n\n"
    ++ "#[cfg [all {feature := \"x\"} {feature := \"y\"}]]\ndef e : I64 := 5\n\n"
    ++ "#[cfg {feature := \"x\"}]\nuse std::io {}\n\n"
    ++ "def f : I64 := 6\n"

def label (d : Decl) : String :=
    match d {
        Decl.def_d df => show_name_path df.name,
        Decl.use_d path _f _p => "use " ++ show_module_path path,
        _ => "?",
    }

def labels (r : ParseResult (List Decl)) : String :=
    match r {
        ParseResult.success _ ds => List.intercalate "," (List.map label ds),
        ParseResult.fail _ => "<fail>",
    }

def env (fs : List String) : CfgEnv :=
    let e : CfgEnv := { features := fs } in
    e

#[test]
def test_cfg_filter_feature_off : Bool :=
    String.beq (labels (decls_parser_located_cfg CfgEnv.empty src)) "b,c,f"

#[test]
def test_cfg_filter_feature_on : Bool :=
    String.beq (labels (decls_parser_located_cfg (env ["x"]) src)) "a,c,d,use std.io,f"

#[test]
def test_cfg_filter_other_feature : Bool :=
    String.beq (labels (decls_parser_located_cfg (env ["y"]) src)) "b,c,d,f"

/// The plain entry point is the feature-off filter.
#[test]
def test_cfg_default_entry_point_is_off : Bool :=
    String.beq (labels (decls_parser_located src)) "b,c,f"

/// An attributed `open` parses and survives when its cfg holds.
#[test]
def test_cfg_attributed_open : Bool :=
    String.beq (labels (decls_parser_located_cfg (env ["x"]) "#[cfg {feature := \"x\"}]\nopen IO {println}\ndef g : I64 := 1\n")) "?,g"

#[test]
def test_cfg_malformed_keeps : Bool :=
    let bad : AttrArg := AttrArg.group [AttrArg.ident (Identifier.id "maybe"), AttrArg.ident (Identifier.id "test")] in
    match CfgPred.parse [bad] {
        Option.none => true,
        Option.some _ => false,
    }

#[test]
def test_cfg_implicit_all : Bool :=
    let x : AttrArg := AttrArg.named (Identifier.id "feature") (AttrArg.str "x") in
    let y : AttrArg := AttrArg.named (Identifier.id "feature") (AttrArg.str "y") in
    match CfgPred.parse [x, y] {
        Option.some p => Bool.not (CfgPred.eval p (env ["x"]) false),
        Option.none => false,
    }

def table : List (Pair String (List String)) :=
    [Pair.pair "default" ["y"], Pair.pair "y" ["x", "dep:z"], Pair.pair "x" List.empty, Pair.pair "w" List.empty]

def features_of (e : CfgEnv) : String := List.intercalate "," e.features

/// `default` is on and closes over the plain features it lists; `dep:`
/// items are not features of this mote. Mirrors the Rust host's
/// `cfg_manifest_defaults_expand`.
#[test]
def test_cfg_for_mote_defaults : Bool :=
    String.beq (features_of (CfgEnv.for_mote "m" table Option.none)) "default,y,x"

/// `MONAD_FEATURES` adds only this mote's `mote/feature` items.
#[test]
def test_cfg_for_mote_spec : Bool :=
    String.beq (features_of (CfgEnv.for_mote "m" table (Option.some "other/q, m/w m/x"))) "default,y,x,w"

#[test]
def test_cfg_for_mote_no_table : Bool :=
    String.beq (features_of (CfgEnv.for_mote "m" List.empty (Option.some "m/a,"))) "a"
