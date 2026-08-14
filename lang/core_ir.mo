use lang.types {Identifier, ModulePath, NumSuffix, id_eq, show_module_path}

/// `CoreIr` — the compiled, evaluator-facing IR this evaluator reduces,
/// mirroring `core/src/core_ir.rs`'s `CoreIr` (Rust). See that file's own
/// doc comment for the full design rationale; the short version: this is
/// the IR the closure-based `lang/core_eval.mo` evaluates, produced by
/// `lang/lower_core_ir.mo` lowering the checked, de-Bruijn `Term`
/// (`lang/types.mo`). It deliberately does NOT carry forward the old
/// `EvalTerm`'s (`lang/eval_term.mo`) substitution-based design, nor its
/// dead `Region`/`BorrowKind`/`eproj`/`eproj_field`/`Multiplicity`
/// machinery (confirmed unused/pass-through by the evaluator that used to
/// interpret it, `lang/eval.mo`) — same exclusions `core_ir.rs`'s own doc
/// comment documents. `if` is not a separate variant: it compiles through
/// `match_` against `Bool`'s two constructor tags, one dispatch mechanism
/// for both, exactly like the Rust design.

/// A scalar literal — mirrors `core_ir::IrLit`.
type IrLit {
  ir_str (value: String),
  ir_char (value: Char),
  ir_num (value: I64) (suffix: NumSuffix),
  ir_float (value: F64) (suffix: NumSuffix),
  /// A type universe used as an ordinary runtime value (e.g. `get_sort
  /// Type`) — opaque and structurally inert, mirroring `IrLit::Sort`.
  ir_sort (level: I64),
}

/// One arm of a `match_`. `bind_count` is how many fields the matched
/// constructor carries (and thus how many entries the evaluator must push
/// onto its `Env` before evaluating `body`) — mirrors `core_ir::MatchArm`.
type MatchArm {
  arm (bind_count: I64) (body: CoreIr),
}

type CoreIr {
  /// De Bruijn index into the *runtime* environment (an `Env`, built by
  /// the evaluator as it descends into `lam`/`match_` bodies) — same
  /// numbering convention as `Term.var`'s de Bruijn index (0 = innermost/
  /// most-recently-bound), carried through lowering unchanged.
  local (idx: I64),

  /// Reference to a whole-program global slot — resolved at lowering
  /// time from a free `Term.var` occurrence (see `lang/lower_core_ir.mo`),
  /// interned into this flat index. Covers ordinary def references as
  /// well as constructor/native references used point-free.
  global (idx: I64),

  /// A single-argument lambda; currying is nested `lam`s, exactly like
  /// `Term.lam`/`CoreIr::Lam`. The static parameter type is dropped —
  /// never needed at runtime, only by the checker.
  lam (body: CoreIr),

  app (fun: CoreIr) (arg: CoreIr),

  lit (l: IrLit),

  /// Compiled `match`, `if`, and dictionary-field projection — one
  /// constructor-tag-dispatch mechanism for everything that "looks at a
  /// value's shape and branches." `arms` is indexed by tag (declaration
  /// order among the scrutinee's inductive's constructors), not scanned
  /// by name.
  match_ (scrutinee: CoreIr) (arms: List MatchArm),

  /// Synthesized in place of a real arm for a constructor tag the source
  /// `match` genuinely never covered (no named case, no wildcard) — see
  /// `core_ir.rs`'s `MatchFail` doc comment. Reaching this at runtime is a
  /// real (if rare) `non_exhaustive_match` error, not a lowering-time one.
  match_fail (inductive: ModulePath) (ctor: Identifier),

  /// A (possibly partially applied) constructor. `tag` is this
  /// constructor's position among its inductive's constructors
  /// (declaration order, resolved once at lowering time); `arity` is its
  /// total field count. `args`'s length is `<= arity`; the evaluator
  /// fills remaining slots left-to-right as further `app`s apply to the
  /// resulting value.
  con (tag: I64) (arity: I64) (args: List CoreIr),

  /// A (possibly partially applied) native/builtin call. `native_id` is
  /// resolved once at lowering time to a stable index into a shared
  /// name -> id table, not re-resolved by name at runtime.
  ntv (native_id: I64) (args: List CoreIr),
}

// ─── Display-equivalent (mirrors core_ir.rs's Display impl) ───────────

def show_irlit (l : IrLit) : String :=
  match l {
    IrLit.ir_str value => value,
    IrLit.ir_char value => "<char>",
    IrLit.ir_num value suffix => I64.to_string value,
    IrLit.ir_float value suffix => "<float>",
    IrLit.ir_sort level => "Sort " ++ I64.to_string level,
  }

def show_core_ir_list (items : List CoreIr) : String :=
  match items {
    List.empty => "",
    List.cons hd rest => " " ++ show_core_ir hd ++ show_core_ir_list rest,
  }

def show_match_arms (arms : List MatchArm) : String :=
  match arms {
    List.empty => "",
    List.cons hd rest =>
      match hd {
        MatchArm.arm bind_count body =>
          " [" ++ I64.to_string bind_count ++ "] " ++ show_core_ir body
            ++ show_match_arms rest,
      },
  }

def show_core_ir (ir : CoreIr) : String :=
  match ir {
    CoreIr.local idx => "(local " ++ I64.to_string idx ++ ")",
    CoreIr.global idx => "(global " ++ I64.to_string idx ++ ")",
    CoreIr.lam body => "(lam " ++ show_core_ir body ++ ")",
    CoreIr.app fun_ arg => "(app " ++ show_core_ir fun_ ++ " " ++ show_core_ir arg ++ ")",
    CoreIr.lit l => "(lit " ++ show_irlit l ++ ")",
    CoreIr.match_ scrutinee arms =>
      "(match " ++ show_core_ir scrutinee ++ show_match_arms arms ++ ")",
    CoreIr.match_fail inductive ctor =>
      "(match-fail " ++ show_module_path inductive ++ ")",
    CoreIr.con tag arity args =>
      "(con #" ++ I64.to_string tag ++ "/" ++ I64.to_string arity
        ++ show_core_ir_list args ++ ")",
    CoreIr.ntv native_id args =>
      "(ntv #" ++ I64.to_string native_id ++ show_core_ir_list args ++ ")",
  }

// ─── Helper constructors (mirror core_ir.rs's free-function style) ─────

def local (idx : I64) : CoreIr := CoreIr.local idx

def global (idx : I64) : CoreIr := CoreIr.global idx

def lam (body : CoreIr) : CoreIr := CoreIr.lam body

def app (fun_ : CoreIr) (arg : CoreIr) : CoreIr := CoreIr.app fun_ arg

def lit (l : IrLit) : CoreIr := CoreIr.lit l

def match_ (scrutinee : CoreIr) (arms : List MatchArm) : CoreIr :=
  CoreIr.match_ scrutinee arms

def arm (bind_count : I64) (body : CoreIr) : MatchArm := MatchArm.arm bind_count body

def con (tag : I64) (arity : I64) (args : List CoreIr) : CoreIr := CoreIr.con tag arity args

def ntv (native_id : I64) (args : List CoreIr) : CoreIr := CoreIr.ntv native_id args

// ─── Tests (mirror core_ir.rs's #[cfg(test)] module) ───────────────────

#[test]
def test_local_construction : Bool :=
  let v : CoreIr := local 0 in
  String.beq (show_core_ir v) "(local 0)"

#[test]
def test_lam_app_construction : Bool :=
  let id_fn : CoreIr := lam (local 0) in
  let applied : CoreIr := app id_fn (lit (IrLit.ir_num 42 NumSuffix.i64)) in
  String.beq (show_core_ir applied) "(app (lam (local 0)) (lit 42))"

#[test]
def test_match_construction : Bool :=
  // match scrutinee { Cons head tail => head, Nil => 0 }
  let m : CoreIr :=
    match_ (global 0) [
      arm 2 (local 1),
      arm 0 (lit (IrLit.ir_num 0 NumSuffix.i64)),
    ]
  in
  String.beq (show_core_ir m) "(match (global 0) [2] (local 1) [0] (lit 0))"

#[test]
def test_con_partial_application : Bool :=
  // A partially-applied 2-arity constructor (e.g. `cons` with only its
  // first field supplied) -- args shorter than arity is a valid shape.
  let partial : CoreIr := con 0 2 [lit (IrLit.ir_num 1 NumSuffix.i64)] in
  String.beq (show_core_ir partial) "(con #0/2 (lit 1))"

#[test]
def test_ntv_construction : Bool :=
  let call : CoreIr :=
    ntv 3 [lit (IrLit.ir_num 1 NumSuffix.i64), lit (IrLit.ir_num 2 NumSuffix.i64)]
  in
  String.beq (show_core_ir call) "(ntv #3 (lit 1) (lit 2))"

#[test]
def test_match_fail_construction : Bool :=
  let mf : CoreIr :=
    CoreIr.match_fail (ModulePath.mp [Identifier.id "Option"]) (Identifier.id "some")
  in
  match mf {
    CoreIr.match_fail _ ctor => id_eq ctor (Identifier.id "some"),
    _ => false,
  }
